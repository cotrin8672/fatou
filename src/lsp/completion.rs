//! Completion (`textDocument/completion` and `completionItem/resolve`).
//!
//! Four Julia contexts, decided by a lexical backward scan from the cursor (robust to
//! the parser's error recovery on the partial input completion always sees, like
//! `Foo.` or `@t`):
//!
//! - **LaTeX** — the run follows a backslash (`\alpha`, `\_1`, `\:smile:`): the
//!   REPL's tab-substitution sequences, inserting the character they expand to;
//! - **value** — a bare identifier: every name visible at the cursor in the
//!   shared masking order ([`Resolver::visible`]), plus Julia's keywords;
//! - **macro** — the run starts with `@`: the visible names in the macro
//!   namespace, each keeping its `@`;
//! - **member** — the run follows a dotted receiver (`Foo.`, `A.B.`): every name
//!   *defined* in the resolved library module (Julia qualified access reaches
//!   non-exported names too), so functions, types, consts, macros, and
//!   submodules.
//!
//! Docstrings and full signatures are filled lazily in [`resolve_completion`]
//! (`completionItem/resolve`) from the [`data`](CompletionItem::data) key each
//! library item carries, so the initial list stays cheap.
//!
//! Static documentation prose offers only input sequences. An explicit `@ref`
//! completes symbols and Markdown anchors in the documented definition's scope;
//! a Julia-bearing fence combines its own local names with that outer scope.
//!
//! The receiver of a member access resolves to a harvested module only
//! (`Base.`, `LinearAlgebra.`, nested `A.B.`); value and type receivers are out
//! of scope until there is type inference.

mod call_keywords;
mod declaration_names;
mod imports;
mod paths;

use std::panic::AssertUnwindSafe;
use std::path::Path;
use std::sync::{Arc, Mutex, Weak};

use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionTextEdit, Documentation, InsertReplaceEdit,
    MarkupContent, MarkupKind, Position, TextEdit,
};
use rowan::TextSize;
use serde::{Deserialize, Serialize};

use crate::incremental::{Analysis, SourceFile};
use crate::index::{ModuleIndex, PackageIndex};
use crate::parse_context::{EditionSource, SourceRole};
#[cfg(test)]
use crate::parser::parse;
use crate::parser::{KEYWORDS, parse_with_options};
use crate::resolve::{
    Candidate, ModulePath, Namespace, PackageSource, Resolution, Resolver, Source,
    has_unresolvable_using, resolve_submodule,
};
use crate::semantic::{BindingId, BindingKind, SemanticModel};
use crate::syntax::{SyntaxKind, SyntaxNode};
use crate::text::{LineIndex, PositionEncoding, TextBuffer};

use super::latex_symbols::{EMOJI_SYMBOLS, LATEX_SYMBOLS};
use super::render::{binding_detail, function_detail, type_detail};
use super::symbols::token_at;

/// The lazy-resolve payload stashed on each library-sourced item: the module it
/// came from (package name first, then any submodule chain) and the name to look
/// up there. A macro keeps its `@` in `name`, which selects the macro table in
/// [`resolve_completion`].
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ResolveData {
    module_path: Vec<String>,
    name: String,
}

/// Private resolve-key tag carried in the standard LSP CompletionList defaults.
const NAME_FROM_LABEL: &str = "fatouNameFromLabel";

/// Shared eligibility for typed and aggregated completion lists. Every item
/// must have exactly the same library origin and use its displayed name.
fn packed_defaults<'a>(
    first: &serde_json::Value,
    items: impl IntoIterator<Item = (Option<&'a str>, Option<&'a serde_json::Value>)>,
) -> Option<serde_json::Value> {
    use serde_json::{Value, json};
    let path = first.get("fatouSourcePath")?;
    let module = first.get("module_path")?;
    if !path.is_string()
        || !module
            .as_array()
            .is_some_and(|parts| !parts.is_empty() && parts.iter().all(Value::is_string))
        || !items.into_iter().all(|(label, data)| {
            data.and_then(Value::as_object).is_some_and(|data| {
                data.len() == 3
                    && data.get("fatouSourcePath") == Some(path)
                    && data.get("module_path") == Some(module)
                    && label.is_some()
                    && data.get("name").and_then(Value::as_str) == label
            })
        })
    {
        return None;
    }
    Some(json!({"data": {
        "fatouSourcePath": path,
        "module_path": module,
        (NAME_FROM_LABEL): true,
    }}))
}

fn completion_list(items: serde_json::Value, defaults: serde_json::Value) -> serde_json::Value {
    use serde_json::Value;
    // lsp-types 0.97 lacks CompletionList.itemDefaults in its response type.
    Value::Object(serde_json::Map::from_iter([
        ("isIncomplete".into(), Value::Bool(false)),
        ("itemDefaults".into(), defaults),
        ("items".into(), items),
    ]))
}

/// Compress a merged wire value only when its data defaults apply to all items.
pub(super) fn compact_response(value: &mut serde_json::Value) {
    use serde_json::Value;
    let Some(items) = value.as_array_mut().filter(|items| items.len() >= 8) else {
        return;
    };
    let Some(defaults) = items[0].get("data").and_then(|first| {
        packed_defaults(
            first,
            items
                .iter()
                .map(|item| (item.get("label").and_then(Value::as_str), item.get("data"))),
        )
    }) else {
        return;
    };
    for item in items.iter_mut() {
        item.as_object_mut().expect("item has data").remove("data");
    }
    *value = completion_list(Value::Array(std::mem::take(items)), defaults);
}

/// The final uncaptured response need not materialize a separate JSON resolve
/// key for every item just to discard it. Ineligible inputs stay unmodified.
pub(super) fn compact_items(items: &mut [CompletionItem]) -> Option<serde_json::Value> {
    if items.len() < 8 {
        return None;
    }
    let defaults = packed_defaults(
        items[0].data.as_ref()?,
        items
            .iter()
            .map(|item| (Some(item.label.as_str()), item.data.as_ref())),
    )?;
    for item in items.iter_mut() {
        item.data = None;
    }
    let items = serde_json::to_value(items).expect("completion items serialize");
    Some(completion_list(items, defaults))
}

/// Normalize before dispatching the resolve job, so path routing, scoped
/// lookups, and fallback responses see exactly the same key as old clients.
pub(super) fn expand_resolve_data(item: &mut CompletionItem) {
    if let Some(data) = item
        .data
        .as_mut()
        .and_then(serde_json::Value::as_object_mut)
        && data.len() == 3
        && data
            .get(NAME_FROM_LABEL)
            .and_then(serde_json::Value::as_bool)
            == Some(true)
        && data.contains_key("fatouSourcePath")
        && data.contains_key("module_path")
    {
        data.remove(NAME_FROM_LABEL);
        data.insert("name".into(), item.label.clone().into());
    }
}

#[cfg(test)]
mod transport_tests {
    use super::*;
    use serde_json::{Value, json};

    fn homogeneous() -> Value {
        Value::Array((0..12).map(|i| {
            let name = format!("α_{i}");
            json!({"label":name, "filterText":format!("alpha_{i}"), "sortText":format!("{i:03}"),
                   "data":{"module_path":["Test", "Nested"], "fatouSourcePath":"/p/test.jl", "name":name}})
        }).collect())
    }

    #[test]
    fn inherited_data_reconstructs_every_item_exactly() {
        let original = homogeneous();
        let mut packed = original.clone();
        compact_response(&mut packed);
        let defaults = &packed["itemDefaults"]["data"];
        assert_eq!(defaults[NAME_FROM_LABEL], true);
        assert_eq!(packed["isIncomplete"], false);
        assert_eq!(packed["items"].as_array().unwrap().len(), 12);
        for (original, wire) in original
            .as_array()
            .unwrap()
            .iter()
            .zip(packed["items"].as_array().unwrap())
        {
            assert!(wire.get("data").is_none());
            let mut restored: CompletionItem = serde_json::from_value(wire.clone()).unwrap();
            restored.data = Some(defaults.clone());
            expand_resolve_data(&mut restored);
            assert_eq!(serde_json::to_value(restored).unwrap(), *original);
        }
    }

    #[test]
    fn pre_serialization_compaction_matches_aggregated_path() {
        let mut expected = homogeneous();
        let mut items: Vec<CompletionItem> = serde_json::from_value(expected.clone()).unwrap();
        compact_response(&mut expected);
        assert_eq!(compact_items(&mut items), Some(expected));
        let mut mixed = homogeneous();
        mixed[0].as_object_mut().unwrap().remove("data");
        let mut items: Vec<CompletionItem> = serde_json::from_value(mixed.clone()).unwrap();
        assert!(compact_items(&mut items).is_none());
        assert_eq!(serde_json::to_value(items).unwrap(), mixed);
    }

    #[test]
    fn mixed_local_items_modules_or_hidden_names_do_not_get_defaults() {
        for incompatible in [
            json!({"label":"variable"}),
            json!({"label":"foo","data":{"module_path":["Other"],"fatouSourcePath":"/p/test.jl","name":"foo"}}),
            json!({"label":"alias","data":{"module_path":["Test","Nested"],"fatouSourcePath":"/p/test.jl","name":"full"}}),
            json!({"label":"foo","data":{"module_path":["Test","Nested"],"fatouSourcePath":"/q/test.jl","name":"foo"}}),
            json!({"label":"foo","data":{"module_path":["Test","Nested"],"fatouSourcePath":"/p/test.jl","name":"foo","extra":true}}),
        ] {
            let mut value = homogeneous();
            value[5] = incompatible;
            let original = value.clone();
            compact_response(&mut value);
            assert_eq!(value, original);
        }
        let original = json!([]);
        let mut value = original.clone();
        compact_response(&mut value);
        assert_eq!(value, original);
    }
}

/// The completion items for `text` at `position`, re-parsing it. Pure and
/// unit-testable; `packages` supplies the library (Base/Core and loaded
/// packages) the value and member contexts draw on.
pub fn compute_completions<P: PackageSource>(
    text: &str,
    position: Position,
    encoding: PositionEncoding,
    packages: &P,
) -> Vec<CompletionItem> {
    let lines = LineIndex::new(text);
    let offset = lines.position_to_byte(position, encoding);
    let root = parse_with_options(text, packages.syntax_options()).cst;
    if let Some(items) = syntax_only_completion(&root, text, offset, encoding) {
        return items;
    }
    let model = SemanticModel::build(&root);
    // The pure path has no file path to key workspace membership on; the live
    // server passes the workspace module through `completion_via_db`.
    completions_for(
        &model,
        &root,
        packages,
        None,
        text,
        TextSize::new(offset as u32),
        encoding,
        &lines,
        None,
    )
}

/// Compute completions off the snapshot's cached parse when the db's tracked
/// buffer for `path` still matches `text`; otherwise re-parse. A write racing
/// the read trips `salsa::Cancelled`, which also falls back to a fresh parse.
/// Mirrors [`document_symbols_via_db`](super::symbols::document_symbols_via_db).
pub(crate) fn completion_via_db(
    snapshot: &Analysis,
    path: &Path,
    text: &TextBuffer,
    position: Position,
    encoding: PositionEncoding,
) -> Vec<CompletionItem> {
    completion_via_db_impl(snapshot, path, text, position, encoding, false)
}

#[derive(Clone, Copy)]
pub(crate) enum CompletionTrigger {
    Standard,
    Punctuation,
    Path,
}

/// Slash and quote trigger completion only for static paths. Do not open generic completion
/// for division, comments, strings in other calls, or interpolations.
pub(crate) fn completion_for_path_trigger(
    snapshot: &Analysis,
    path: &Path,
    text: &TextBuffer,
    position: Position,
    encoding: PositionEncoding,
) -> Vec<CompletionItem> {
    completion_via_db_impl(snapshot, path, text, position, encoding, true)
}

fn completion_via_db_impl(
    snapshot: &Analysis,
    path: &Path,
    text: &TextBuffer,
    position: Position,
    encoding: PositionEncoding,
    path_only: bool,
) -> Vec<CompletionItem> {
    let offset = TextSize::new(text.line_index().position_to_byte(position, encoding) as u32);
    let cached = salsa::Cancelled::catch(AssertUnwindSafe(|| {
        let file = snapshot.lookup_file(path)?;
        if snapshot.file_text(file) != text {
            // The tracked input lags the live buffer; the cached model is stale.
            return None;
        }
        let root = snapshot.parsed_tree(file);
        if let Some(context) = paths::context_at(&root, offset)
            && let Some(items) = paths::complete(
                context,
                snapshot,
                snapshot.semantic_model(file),
                path,
                text,
                offset,
                encoding,
            )
        {
            return Some(items);
        }
        if path_only {
            return Some(Vec::new());
        }
        if let Some(items) = syntax_only_completion(&root, text, offset.into(), encoding) {
            return Some(items);
        }
        if let Some(context) = imports::context_at(&root, text, offset) {
            if context.alias_destination() {
                return Some(Vec::new());
            }
            let model = (!context.package_root()).then(|| snapshot.semantic_model(file));
            return Some(complete_import(
                &context, model, snapshot, path, text, offset, encoding,
            ));
        }
        let model = snapshot.semantic_model(file);
        let workspace = snapshot.workspace_member(path);
        let mut items = completions_for(
            model,
            &root,
            snapshot,
            workspace.clone(),
            text,
            offset,
            encoding,
            &text.line_index(),
            Some((snapshot, file)),
        );
        if let Some(workspace) = workspace {
            append_auto_imports(
                snapshot, file, path, model, &root, workspace, text, offset, encoding, &mut items,
            );
        }
        Some(items)
    }));
    let mut items = match cached {
        Ok(Some(items)) => items,
        // Cache miss (`Ok(None)`) or a racing write (`Err`): re-parse from text.
        Ok(None) | Err(_) => {
            let parsed = parse_with_options(text, snapshot.options_for_path(path));
            if path_only {
                let from_path = salsa::Cancelled::catch(AssertUnwindSafe(|| {
                    let context = paths::context_at(&parsed.cst, offset)?;
                    let model = SemanticModel::build(&parsed.cst);
                    paths::complete(context, snapshot, &model, path, text, offset, encoding)
                }));
                return from_path.ok().flatten().unwrap_or_default();
            }
            // A cold or racing read can still use the real file's project.
            let from_import = salsa::Cancelled::catch(AssertUnwindSafe(|| {
                import_from_tree(snapshot, path, text, &parsed.cst, offset, encoding)
            }));
            match from_import {
                Ok(Some(items)) => items,
                _ => {
                    let model = SemanticModel::build(&parsed.cst);
                    let path_context = paths::context_at(&parsed.cst, offset);
                    let path_syntax = path_context.is_some();
                    let from_path = salsa::Cancelled::catch(AssertUnwindSafe(|| {
                        let context = path_context?;
                        paths::complete(context, snapshot, &model, path, text, offset, encoding)
                    }));
                    match from_path {
                        Ok(Some(items)) => items,
                        // A cancelled semantic query must not turn a recognized
                        // path slot into a menu of unrelated symbols.
                        Err(_) if path_syntax => Vec::new(),
                        _ => completions_for(
                            &model,
                            &parsed.cst,
                            snapshot,
                            None,
                            text,
                            offset,
                            encoding,
                            &text.line_index(),
                            None,
                        ),
                    }
                }
            }
        }
    };
    add_completion_source_path(&mut items, path);
    items
}

/// Space, colon and comma are advertised for import directives; semicolons
/// and top-level keyword commas also open ordinary calls' keyword slots.
/// Unrelated punctuation requests do not build a model or flood the editor.
pub(crate) fn completion_for_punctuation_trigger(
    snapshot: &Analysis,
    path: &Path,
    text: &TextBuffer,
    position: Position,
    encoding: PositionEncoding,
) -> Vec<CompletionItem> {
    let offset = TextSize::new(text.line_index().position_to_byte(position, encoding) as u32);
    // An advertised colon can also complete an existing Julia emoji escape.
    // Preserve that independent feature instead of claiming every colon.
    let before = &text[..usize::from(offset)];
    if before.ends_with(':') && matches!(context_at(text, offset.into()), Context::Latex { .. }) {
        return completion_via_db(snapshot, path, text, position, encoding);
    }
    let maybe_keyword = before.trim_end_matches([' ', '\t']).ends_with([';', ',']);
    salsa::Cancelled::catch(AssertUnwindSafe(|| {
        let cached = snapshot
            .lookup_file(path)
            .filter(|file| snapshot.file_text(*file) == text);
        let root = match cached {
            Some(file) => snapshot.parsed_tree(file),
            None => {
                // A cold, ordinary keystroke is far more common than an
                // import clause. The prefix gate is only a cheap rejection;
                // the CST, not this text check, determines the context.
                let recent = before.rsplitn(9, '\n').take(8);
                if !recent
                    .into_iter()
                    .any(|line| line.contains("using") || line.contains("import"))
                    && !(maybe_keyword && before.contains(';'))
                {
                    return Vec::new();
                }
                parse_with_options(text, snapshot.options_for_path(path)).cst
            }
        };
        let mut items = if let Some(context) = imports::context_at(&root, text, offset) {
            if context.alias_destination() {
                return Vec::new();
            }
            let fresh;
            let model = if context.package_root() {
                None
            } else if let Some(file) = cached {
                Some(snapshot.semantic_model(file))
            } else {
                fresh = SemanticModel::build(&root);
                Some(&fresh)
            };
            complete_import(&context, model, snapshot, path, text, offset, encoding)
        } else if maybe_keyword && let Some(site) = call_keywords::site_at(&root, offset) {
            let fresh;
            let model = if let Some(file) = cached {
                snapshot.semantic_model(file)
            } else {
                fresh = SemanticModel::build(&root);
                &fresh
            };
            let workspace = snapshot.workspace_member(path);
            let Some(mut items) = site.items(
                model,
                snapshot,
                workspace.as_ref(),
                &root,
                &text.line_index(),
                encoding,
            ) else {
                return Vec::new();
            };
            if !site.explicit() {
                items.extend(ordinary_value_items(model, snapshot, workspace, offset));
            }
            items
        } else {
            return Vec::new();
        };
        add_completion_source_path(&mut items, path);
        items
    }))
    .unwrap_or_default()
}

fn import_from_tree(
    snapshot: &Analysis,
    path: &Path,
    text: &TextBuffer,
    root: &SyntaxNode,
    offset: TextSize,
    encoding: PositionEncoding,
) -> Option<Vec<CompletionItem>> {
    let context = imports::context_at(root, text, offset)?;
    if context.alias_destination() {
        return Some(Vec::new());
    }
    let model = (!context.package_root()).then(|| SemanticModel::build(root));
    Some(complete_import(
        &context,
        model.as_ref(),
        snapshot,
        path,
        text,
        offset,
        encoding,
    ))
}

fn complete_import(
    context: &imports::ImportContext<'_>,
    model: Option<&SemanticModel>,
    snapshot: &Analysis,
    path: &Path,
    text: &TextBuffer,
    offset: TextSize,
    encoding: PositionEncoding,
) -> Vec<CompletionItem> {
    let project_names = if context.package_root() {
        imports::project_names(snapshot, path)
    } else {
        Default::default()
    };
    context.complete(
        model,
        snapshot,
        snapshot.workspace_member(path).as_ref(),
        project_names,
        offset,
        &text.line_index(),
        encoding,
    )
}

fn add_completion_source_path(items: &mut [CompletionItem], path: &Path) {
    let mut source = None;
    for item in items {
        if let Some(serde_json::Value::Object(data)) = &mut item.data {
            data.insert(
                "fatouSourcePath".into(),
                source
                    .get_or_insert_with(|| serde_json::to_value(path).expect("path serializes"))
                    .clone(),
            );
        }
    }
}

/// Unicode input outside literals is determined by the token spelling. Never
/// infer module identity from spelling: a local binding may shadow Base or a
/// package alias. Treat both sides of a token boundary as possible literals so
/// decoded docstring mappings remain the authority there.
fn syntax_only_completion(
    root: &SyntaxNode,
    text: &str,
    offset: usize,
    encoding: PositionEncoding,
) -> Option<Vec<CompletionItem>> {
    let at = root.token_at_offset(TextSize::new(offset as u32));
    let lexical = context_at(text, offset);
    if let Some(left) = at.clone().left_biased()
        && !matches!(lexical, Context::Latex { .. })
        && ((left.kind() == SyntaxKind::COMMENT && usize::from(left.text_range().start()) < offset)
            || (left.kind() == SyntaxKind::BLOCK_COMMENT
                && usize::from(left.text_range().start()) + 1 < offset
                && (offset < usize::from(left.text_range().end()) || !left.text().ends_with("=#"))))
    {
        return Some(Vec::new());
    }
    let Context::Latex { start } = lexical else {
        return None;
    };
    let in_literal = [at.clone().left_biased(), at.right_biased()]
        .into_iter()
        .flatten()
        .any(|token| {
            token.parent_ancestors().any(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::CMD_LITERAL | SyntaxKind::STRING_LITERAL
                )
            })
        });
    (!in_literal).then(|| latex_items(text, start, offset, encoding))
}

/// Conservative first version: only a statically verified bare value read in the package
/// entry's root module. Editing an included file, quoted code or a declaration
/// would require proving a different insertion scope and execution order.
#[allow(clippy::too_many_arguments)]
fn append_auto_imports(
    snapshot: &Analysis,
    file: SourceFile,
    path: &Path,
    model: &SemanticModel,
    root: &SyntaxNode,
    workspace: (Arc<PackageIndex>, ModulePath),
    text: &TextBuffer,
    offset: TextSize,
    encoding: PositionEncoding,
    items: &mut Vec<CompletionItem>,
) {
    let Some((prefix, callee)) = auto_import_site(model, root, text, offset) else {
        return;
    };
    let Some(context) = snapshot.context() else {
        return;
    };
    let EditionSource::Project {
        path: project,
        role: SourceRole::Package,
    } = &context.source
    else {
        return;
    };
    let editions = snapshot.source_editions(file);
    if !matches!(editions.as_slice(), [(active, selected)] if active == context && selected.certain)
    {
        return;
    }
    let (package, host) = &workspace;
    if crate::incremental::normalize_path(path) != context.entry
        || !host.is_empty()
        || package.root.bare
        || package.members.len() != 1
        || !package.diagnostics.is_empty()
        || !snapshot.parse_diagnostics(file).is_empty()
        || model
            .enclosing_module_path(model.scope_at(callee.start()))
            .as_slice()
            != [package.name.as_str()]
        || root.descendants().any(|node| {
            matches!(node.kind(), SyntaxKind::MACRO_CALL)
                && model
                    .scope(model.scope_at(node.text_range().start()))
                    .kind
                    .is_global()
        })
        || model
            .idents()
            .iter()
            .any(|read| matches!(read.name.as_str(), "eval" | "include" | "include_string"))
        || model.qualified_reads().iter().any(|read| {
            read.path
                .last()
                .is_some_and(|name| matches!(name.as_str(), "eval" | "include" | "include_string"))
        })
        || has_unresolvable_using(model, snapshot, Some(&workspace))
        || model
            .module_loads()
            .iter()
            .any(|load| load.path.components.is_empty())
    {
        return;
    }
    let Some((anchor, eol)) = auto_import_anchor(root, text, &package.name) else {
        return;
    };
    if TextSize::from(anchor as u32) >= callee.start() {
        return;
    }
    let Some(project_file) = snapshot.lookup_file(project) else {
        return;
    };
    let Some(project_details) =
        crate::environment::parse_project_str(snapshot.file_text_of(project_file))
    else {
        return;
    };
    let mut offers =
        std::collections::BTreeMap::<String, Option<(String, CompletionItemKind)>>::new();
    for (dep, uuid) in project_details.deps {
        let dep = dep.into_inner();
        let Ok(uuid) = uuid.into_inner().parse() else {
            continue;
        };
        if !simple_import_name(&dep)
            || dep == package.name
            || model.module_loads().iter().any(|load| {
                load.path.leading_dots == 0
                    && load
                        .path
                        .components
                        .first()
                        .is_some_and(|name| name == dep.as_str())
            })
        {
            continue;
        }
        let Some(index) = snapshot.auto_import_package(project, &dep, uuid) else {
            continue;
        };
        let module = &index.root;
        if !index.diagnostics.is_empty() || module.name != dep {
            continue;
        }
        for export in &module.exports {
            let name = &export.name;
            if export.visibility != crate::index::Visibility::Exported
                || !name.starts_with(prefix)
                || name == prefix
                || !simple_import_name(name)
            {
                continue;
            }
            // Verify an actual callable definition, not only an `export` of an
            // undefined/macro-generated/re-exported symbol.
            let kind = if module.types.iter().any(|t| &t.name == name) {
                CompletionItemKind::CLASS
            } else if module
                .functions
                .iter()
                .any(|f| f.owner.is_none() && &f.name == name)
            {
                CompletionItemKind::FUNCTION
            } else {
                continue;
            };
            offers
                .entry(name.clone())
                .and_modify(|offer| {
                    if offer.as_ref().is_some_and(|(provider, _)| provider != &dep) {
                        *offer = None;
                    }
                })
                .or_insert_with(|| Some((dep.clone(), kind)));
        }
    }
    let resolver = Resolver::new(model, snapshot).with_workspace(Some(workspace));
    let range = super::documentation::lsp_range(callee, &text.line_index(), encoding);
    let at = text.line_index().byte_to_position(anchor, encoding);
    for (name, (dep, kind)) in offers
        .into_iter()
        .filter_map(|(name, offer)| Some((name, offer?)))
    {
        if resolver.resolve(&name, callee.start(), Namespace::Value) != Resolution::Unresolved {
            continue;
        }
        let mut item = member_item(&name, kind, std::slice::from_ref(&dep));
        item.detail = Some(format!("Auto-import from {dep}"));
        item.sort_text = Some(format!("~~fatou-auto-import:{name}"));
        item.text_edit = Some(CompletionTextEdit::Edit(TextEdit {
            range,
            new_text: name.clone(),
        }));
        item.additional_text_edits = Some(vec![TextEdit {
            range: lsp_types::Range::new(at, at),
            new_text: format!("using {dep}: {name}{eol}"),
        }]);
        items.push(item);
    }
}

fn simple_import_name(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !KEYWORDS.contains(&name)
}

fn auto_import_site<'a>(
    model: &SemanticModel,
    root: &SyntaxNode,
    text: &'a str,
    offset: TextSize,
) -> Option<(&'a str, rowan::TextRange)> {
    let offset_bytes = usize::from(offset);
    let (prefix, _) = take_ident_back(text.get(..offset_bytes)?);
    if prefix.len() < 3
        || !simple_import_name(prefix)
        || !matches!(context_at(text, offset_bytes), Context::Value)
    {
        return None;
    }
    let start = TextSize::from((offset_bytes - prefix.len()) as u32);
    let at_start = token_at(root, start)?;
    let name = at_start.parent()?;
    if name.kind() != SyntaxKind::NAME
        || name.text_range().start() != start
        || name.text_range().end() != offset
        || name.ancestors().any(|node| {
            (node.kind() == SyntaxKind::BINARY_EXPR
                && super::symbols::op_token(&node).is_some_and(|op| op.kind() == SyntaxKind::DOT))
                || matches!(
                    node.kind(),
                    SyntaxKind::MACRO_CALL
                        | SyntaxKind::MACRO_DEF
                        | SyntaxKind::DOC
                        | SyntaxKind::QUOTE_EXPR
                        | SyntaxKind::QUOTE_SYM
                        | SyntaxKind::INTERPOLATION
                        | SyntaxKind::SIGNATURE
                        | SyntaxKind::TYPE_ANNOTATION
                        | SyntaxKind::IMPORT_STMT
                        | SyntaxKind::USING_STMT
                        | SyntaxKind::STRUCT_DEF
                        | SyntaxKind::ERROR
                )
        })
        || !model.free_reads().any(|read| {
            read.range == name.text_range()
                && read.name == prefix
                && read.access == crate::semantic::Access::Read
        })
    {
        return None;
    }
    Some((prefix, name.text_range()))
}

fn auto_import_anchor<'a>(
    root: &SyntaxNode,
    text: &'a str,
    expected: &str,
) -> Option<(usize, &'a str)> {
    let mut children = root.children();
    let module = children.next()?;
    if module.kind() != SyntaxKind::MODULE_DEF || children.next().is_some() {
        return None;
    }
    let start = usize::from(module.text_range().start());
    let header_end = start + text.get(start..)?.find('\n')?;
    let mut header = text[start..header_end].split_whitespace();
    if header.next()? != "module" || header.next()? != expected || header.next().is_some() {
        return None;
    }
    let eol = if text.as_bytes().get(header_end.checked_sub(1)?) == Some(&b'\r') {
        "\r\n"
    } else {
        "\n"
    };
    Some((header_end + 1, eol))
}

/// Fill an item's `documentation` (and, for a function, its `detail` signature)
/// from the harvested library, keyed by the item's [`ResolveData`]. Returns the
/// item unchanged when it carries no key or the symbol has no docs.
pub(crate) fn resolve_completion(snapshot: &Analysis, item: CompletionItem) -> CompletionItem {
    resolve_completion_with(&|name| snapshot.library_package(name), item)
}

/// The masking-order candidate set for `text` at `offset`, mapped to LSP items.
#[allow(clippy::too_many_arguments)]
fn completions_for<P: PackageSource>(
    model: &SemanticModel,
    root: &SyntaxNode,
    packages: &P,
    workspace: Option<(Arc<PackageIndex>, ModulePath)>,
    text: &str,
    offset: TextSize,
    encoding: PositionEncoding,
    lines: &LineIndex,
    cached_docs: Option<(&Analysis, SourceFile)>,
) -> Vec<CompletionItem> {
    let offset_bytes: usize = offset.into();
    if let Some(context) =
        super::documentation::DocumentationContext::at_cached(model, offset, cached_docs)
    {
        if let Some(embedded) = context.embedded_julia() {
            let parsed = parse_with_options(embedded.text, packages.syntax_options());
            let embedded_model = SemanticModel::build(&parsed.cst);
            if declaration_names::introduces_name(&parsed.cst, &embedded_model, embedded.offset) {
                return Vec::new();
            }
            let mut items = completions_for(
                &embedded_model,
                &parsed.cst,
                packages,
                workspace.clone(),
                embedded.text,
                embedded.offset,
                encoding,
                &LineIndex::new(embedded.text),
                None,
            );
            if imports::context_at(&parsed.cst, embedded.text, embedded.offset).is_some() {
                return map_embedded_edits(items, &embedded, text, encoding);
            }
            // Anchors name Markdown targets, so they stay out of the Julia
            // names merged in from the enclosing scope.
            let outer = reference_completions(
                model,
                packages,
                workspace,
                embedded.text,
                embedded.offset,
                context.attachment.target_range.start(),
                false,
                None,
            );
            let mut seen: std::collections::HashSet<String> =
                items.iter().map(|item| item.label.clone()).collect();
            items.extend(
                outer
                    .into_iter()
                    .filter(|item| seen.insert(item.label.clone())),
            );
            return map_embedded_edits(items, &embedded, text, encoding);
        }
        if let Some(reference) = context.explicit_ref() {
            let replacement = context.source_range(reference.range).map(|range| {
                super::documentation::lsp_range(range, &LineIndex::new(text), encoding)
            });
            let mut items = reference_completions(
                model,
                packages,
                workspace,
                reference.target.as_str(),
                reference.offset,
                context.attachment.target_range.start(),
                true,
                cached_docs,
            );
            if let Some(range) = replacement {
                for item in &mut items {
                    if item.kind == Some(CompletionItemKind::REFERENCE) {
                        item.text_edit = Some(CompletionTextEdit::Edit(TextEdit {
                            range,
                            new_text: item.label.clone(),
                        }));
                    }
                }
            }
            return items;
        }
        // Documentation prose keeps Julia's input sequences, but ordinary
        // identifier completion would bury the author in irrelevant code names.
        if let Context::Latex { start } = context_at(text, offset_bytes) {
            let typed = &text[start..offset_bytes];
            if !is_lone_escape(&typed[1..]) {
                return latex_items(text, start, offset_bytes, encoding);
            }
        }
        return Vec::new();
    }

    if let Some(context) = imports::context_at(root, text, offset) {
        return context.complete(
            Some(model),
            packages,
            workspace.as_ref(),
            Default::default(),
            offset,
            lines,
            encoding,
        );
    }

    let context = context_at(text, offset_bytes);
    let ordinary_name = matches!(
        context,
        Context::Value
            | Context::Macro
            | Context::Member {
                macro_member: false,
                ..
            }
    );
    let bare_macro = matches!(context, Context::Macro);
    let mut items = match context {
        // A sequence is an input method, not code, so it wins over the
        // identifier run it would otherwise look like. Where the backslash is
        // more likely the literal's own than an input sequence, nothing is
        // offered at all rather than falling back to another context: a popup
        // of names over a regex escape would be just as much in the way.
        Context::Latex { start } => {
            let typed = &text[start..offset_bytes];
            let suppressed = match string_context_at(root, offset) {
                StringContext::Verbatim => true,
                StringContext::Plain => is_lone_escape(&typed[1..]),
                StringContext::Code => false,
            };
            if suppressed {
                Vec::new()
            } else {
                latex_items(text, start, offset_bytes, encoding)
            }
        }
        // Documentation prose keeps Julia's input sequences, handled above, but
        // ordinary identifier completion would bury the author in irrelevant
        // code names. Only a payload no static decoding reached gets here (an
        // interpolated docstring), and only outside its interpolations.
        _ if string_context_at(root, offset) != StringContext::Code
            && in_documentation_payload(model, offset) =>
        {
            Vec::new()
        }
        Context::Member {
            receiver,
            macro_member,
        } => {
            let mut items = member_completions(
                model,
                packages,
                workspace,
                &receiver,
                offset,
                receiver_start(text, offset, &receiver, macro_member),
                macro_member,
            );
            if macro_member && !items.is_empty() {
                qualified_macro_edits(&mut items, text, offset_bytes, lines, encoding);
            }
            items
        }
        Context::Macro => candidate_items(
            model,
            Resolver::new(model, packages)
                .with_workspace(workspace)
                .visible(offset, Namespace::Macro),
            Namespace::Macro,
        ),
        Context::Value if declaration_names::introduces_name(root, model, offset) => Vec::new(),
        Context::Value => {
            if let Some(site) = call_keywords::site_at(root, offset)
                && let Some(mut items) =
                    site.items(model, packages, workspace.as_ref(), root, lines, encoding)
            {
                if !site.explicit() {
                    items.extend(ordinary_value_items(model, packages, workspace, offset));
                }
                items
            } else {
                ordinary_value_items(model, packages, workspace, offset)
            }
        }
    };
    if ordinary_name && !items.is_empty() {
        complete_identifier_suffix(&mut items, text, offset, root, lines, encoding, bare_macro);
    }
    items
}

fn ordinary_value_items<P: PackageSource>(
    model: &SemanticModel,
    packages: &P,
    workspace: Option<(Arc<PackageIndex>, ModulePath)>,
    offset: TextSize,
) -> Vec<CompletionItem> {
    let mut items = candidate_items(
        model,
        Resolver::new(model, packages)
            .with_workspace(workspace)
            .visible(offset, Namespace::Value),
        Namespace::Value,
    );
    items.extend(KEYWORDS.iter().map(|kw| keyword_item(kw)));
    items
}

/// Completion inside an explicit `@ref target`, resolved in the documented
/// definition's Julia scope rather than in the Markdown string literal.
#[allow(clippy::too_many_arguments)]
fn reference_completions<P: PackageSource>(
    model: &SemanticModel,
    packages: &P,
    workspace: Option<(Arc<PackageIndex>, ModulePath)>,
    target: &str,
    offset: TextSize,
    semantic_offset: TextSize,
    anchors: bool,
    cached_docs: Option<(&Analysis, SourceFile)>,
) -> Vec<CompletionItem> {
    match context_at(target, offset.into()) {
        Context::Member {
            receiver,
            macro_member,
        } => member_completions(
            model,
            packages,
            workspace,
            &receiver,
            semantic_offset,
            None,
            macro_member,
        ),
        Context::Macro => candidate_items(
            model,
            Resolver::new(model, packages)
                .with_workspace(workspace)
                .visible(semantic_offset, Namespace::Macro),
            Namespace::Macro,
        ),
        Context::Value => {
            let mut items = candidate_items(
                model,
                Resolver::new(model, packages)
                    .with_workspace(workspace)
                    .visible(semantic_offset, Namespace::Value),
                Namespace::Value,
            );
            let anchor_names = if anchors {
                super::documentation::markdown_index(model, cached_docs)
                    .anchor_names()
                    .to_vec()
            } else {
                Vec::new()
            };
            for anchor in anchor_names {
                if items.iter().any(|item| item.label == anchor) {
                    continue;
                }
                items.push(CompletionItem {
                    label: anchor,
                    kind: Some(CompletionItemKind::REFERENCE),
                    detail: Some("documentation anchor".to_string()),
                    ..Default::default()
                });
            }
            items
        }
        Context::Latex { .. } => Vec::new(),
    }
}

/// Move any explicit edits produced for an embedded Julia document into the
/// outer Julia source. Most symbol items rely on the client's word replacement
/// and carry no edit; LaTeX input sequences are the important explicit case.
fn map_embedded_edits(
    mut items: Vec<CompletionItem>,
    embedded: &super::documentation::EmbeddedJulia<'_>,
    source: &str,
    encoding: PositionEncoding,
) -> Vec<CompletionItem> {
    let embedded_index = LineIndex::new(embedded.text);
    let source_index = LineIndex::new(source);
    let map = |range| {
        embedded
            .source_range_from_lsp(range, &embedded_index, encoding)
            .map(|range| super::documentation::lsp_range(range, &source_index, encoding))
    };
    for item in &mut items {
        item.text_edit = item.text_edit.take().and_then(|edit| match edit {
            CompletionTextEdit::Edit(mut edit) => {
                edit.range = map(edit.range)?;
                Some(CompletionTextEdit::Edit(edit))
            }
            CompletionTextEdit::InsertAndReplace(mut edit) => {
                edit.insert = map(edit.insert)?;
                edit.replace = map(edit.replace)?;
                Some(CompletionTextEdit::InsertAndReplace(InsertReplaceEdit {
                    new_text: edit.new_text,
                    insert: edit.insert,
                    replace: edit.replace,
                }))
            }
        });
        if let Some(edits) = &mut item.additional_text_edits {
            edits.retain_mut(|edit| match map(edit.range) {
                Some(range) => {
                    edit.range = range;
                    true
                }
                None => false,
            });
        }
    }
    items
}

// --- context detection -----------------------------------------------------

/// What the cursor is completing, decided by the text just before it.
#[derive(Debug, PartialEq, Eq)]
enum Context {
    Value,
    Macro,
    /// After a dotted receiver: `receiver` is the module path (`A.B.` →
    /// `["A", "B"]`), `macro_member` is true for `Foo.@` (a macro member).
    Member {
        receiver: Vec<String>,
        macro_member: bool,
    },
    /// Inside a LaTeX or emoji input sequence: `start` is the byte offset of the
    /// opening backslash, so the sequence typed so far is `text[start..offset]`.
    Latex {
        start: usize,
    },
}

/// Classify the cursor at byte `offset` by scanning the identifier run and the
/// punctuation just before it.
fn context_at(text: &str, offset: usize) -> Context {
    let prefix = &text[..offset.min(text.len())];
    if let Some(start) = sequence_start(prefix) {
        return Context::Latex { start };
    }
    let (_word, rest) = take_ident_back(prefix);
    let (macro_sigil, rest) = match rest.strip_suffix('@') {
        Some(r) => (true, r),
        None => (false, rest),
    };
    if let Some(before_dot) = rest.strip_suffix('.') {
        let receiver = scan_dotted(before_dot);
        if !receiver.is_empty() {
            return Context::Member {
                receiver,
                macro_member: macro_sigil,
            };
        }
    }
    if macro_sigil {
        Context::Macro
    } else {
        Context::Value
    }
}

/// A fresh dot list covers values only. It cannot be used to locally filter
/// the next macro name: typing `@` switches namespaces, even if the client
/// coalesces the trigger with the first identifier characters.
pub(super) fn starts_member_at_dot(
    text: &TextBuffer,
    position: Position,
    encoding: PositionEncoding,
) -> bool {
    let offset = text.line_index().position_to_byte(position, encoding);
    text[..offset].ends_with('.')
        && matches!(
            context_at(text, offset),
            Context::Member {
                macro_member: false,
                ..
            }
        )
}

/// Split off the trailing identifier run of `prefix`, returning `(run, before)`.
/// The run is empty (and `before` is all of `prefix`) when `prefix` does not end
/// in an identifier character.
fn take_ident_back(prefix: &str) -> (&str, &str) {
    let start = prefix
        .char_indices()
        .rev()
        .take_while(|(_, c)| is_ident_char(*c))
        .last()
        .map(|(i, _)| i)
        .unwrap_or(prefix.len());
    (&prefix[start..], &prefix[..start])
}

/// Byte position of the first receiver component. This mirrors the backward
/// scan without extending the parser's recovery requirements.
fn receiver_start(
    text: &str,
    offset: TextSize,
    path: &[String],
    macro_member: bool,
) -> Option<TextSize> {
    let (_, before_member) = take_ident_back(text.get(..usize::from(offset))?);
    let receiver_bytes = path.iter().map(String::len).sum::<usize>() + path.len().checked_sub(1)?;
    let skip = receiver_bytes + 1 + usize::from(macro_member);
    Some(TextSize::new(before_member.len().checked_sub(skip)? as u32))
}

/// The dotted module path ending `s` (`"A.B"` → `["A", "B"]`), or empty when the
/// text before the dot is not a chain of identifiers.
fn scan_dotted(s: &str) -> Vec<String> {
    let mut comps = Vec::new();
    let mut cursor = s;
    loop {
        let (ident, rest) = take_ident_back(cursor);
        if ident.is_empty() {
            break;
        }
        comps.push(ident.to_string());
        match rest.strip_suffix('.') {
            Some(r) => cursor = r,
            None => break,
        }
    }
    comps.reverse();
    comps
}

/// Match Julia's identifier continuation rules when scanning around a caret.
fn is_ident_char(c: char) -> bool {
    crate::parser::is_ident_continue(c)
}

// --- LaTeX and emoji sequences ---------------------------------------------

/// The longest key in either table, capping the backward scan so a stray
/// backslash far up the line cannot pull in an unbounded run. Pinned by
/// [`tables_fit_the_scanner`](tests::tables_fit_the_scanner).
const MAX_SEQUENCE_LEN: usize = 57;

/// The byte offset of the backslash opening the input sequence `prefix` ends
/// in, or `None` when it does not end in one.
///
/// The scan stops at anything a key cannot contain, so a backslash is only
/// found across sequence characters. Note that a backslash directly after an
/// operand is *not* excluded: `A\b` is left division, but `x\_1` is how one
/// types `x₁`, and the second is far and away the common case.
fn sequence_start(prefix: &str) -> Option<usize> {
    for (i, c) in prefix.char_indices().rev() {
        if prefix.len() - i > MAX_SEQUENCE_LEN {
            return None;
        }
        if c == '\\' {
            return Some(i);
        }
        if !is_sequence_char(c) {
            return None;
        }
    }
    None
}

/// Whether `c` can appear in a sequence key after its backslash. Every key is
/// ASCII: letters and digits, plus the punctuation the sub/superscript,
/// fraction, and emoji keys use (`\^2`, `\_1`, `\1/2`, `\:+1:`).
fn is_sequence_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || "_^/+-()!=<>:".contains(c)
}

/// The items for the sequence `text[start..offset]`, each replacing the whole
/// sequence (backslash included) with the character it expands to.
fn latex_items(
    text: &str,
    start: usize,
    offset: usize,
    encoding: PositionEncoding,
) -> Vec<CompletionItem> {
    let typed = &text[start..offset];
    let line_index = LineIndex::new(text);
    let range = lsp_types::Range {
        start: line_index.byte_to_position(start, encoding),
        end: line_index.byte_to_position(offset, encoding),
    };
    // The REPL only reaches for emoji once the `:` is there, so a bare `\` does
    // not bury 2549 LaTeX sequences under 1242 emoji.
    let emoji: &[(&str, &str)] = if typed.starts_with("\\:") {
        prefixed(EMOJI_SYMBOLS, typed)
    } else {
        &[]
    };
    prefixed(LATEX_SYMBOLS, typed)
        .iter()
        .chain(emoji)
        .map(|&(sequence, expansion)| latex_item(sequence, expansion, range))
        .collect()
}

/// The run of entries whose key starts with `prefix`, found by binary search on
/// the sorted table.
fn prefixed<'a>(table: &'a [(&'a str, &'a str)], prefix: &str) -> &'a [(&'a str, &'a str)] {
    let start = table.partition_point(|(key, _)| *key < prefix);
    let len = table[start..].partition_point(|(key, _)| key.starts_with(prefix));
    &table[start..start + len]
}

/// An item offering `sequence`, inserting `expansion` over `range`. The label
/// keeps the backslash so the client filters against what was actually typed.
fn latex_item(sequence: &str, expansion: &str, range: lsp_types::Range) -> CompletionItem {
    CompletionItem {
        label: sequence.to_string(),
        kind: Some(CompletionItemKind::TEXT),
        detail: Some(expansion.to_string()),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("`{expansion}` {}", codepoints(expansion)),
        })),
        filter_text: Some(sequence.to_string()),
        text_edit: Some(CompletionTextEdit::Edit(TextEdit {
            range,
            new_text: expansion.to_string(),
        })),
        ..Default::default()
    }
}

/// The `U+` code points of `s`, space-separated (a couple of dozen expansions
/// are a base character plus a combining mark).
fn codepoints(s: &str) -> String {
    s.chars()
        .map(|c| format!("U+{:04X}", c as u32))
        .collect::<Vec<_>>()
        .join(" ")
}

/// What kind of literal the cursor sits in, which decides how much of a
/// backslash run is the string's own text.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum StringContext {
    /// Ordinary code, where a backslash is never an escape.
    Code,
    /// A plain string or docstring: prose, where writing `α` is exactly what
    /// the sequences are for, but where `\n` is also a newline.
    Plain,
    /// A prefixed string macro (`r"\d"`, `raw"\n"`) or a command literal, where
    /// every backslash is the literal's own and a popup over each regex escape
    /// would be pure noise.
    Verbatim,
}

/// Whether `offset` sits inside a documentation payload literal, statically
/// decodable or not. Ordinary string and command literals are not documentation
/// and keep their identifier completion.
fn in_documentation_payload(model: &SemanticModel, offset: TextSize) -> bool {
    model
        .documentation()
        .iter()
        .any(|doc| doc.payload_range.contains_inclusive(offset))
}

fn string_context_at(root: &SyntaxNode, offset: TextSize) -> StringContext {
    let Some(token) = token_at(root, offset) else {
        return StringContext::Code;
    };
    token
        .parent_ancestors()
        .find_map(|node| match node.kind() {
            // An interpolation is Julia code even though a string literal is a
            // more distant ancestor.
            SyntaxKind::INTERPOLATION => Some(StringContext::Code),
            SyntaxKind::CMD_LITERAL => Some(StringContext::Verbatim),
            SyntaxKind::STRING_LITERAL => Some(
                if node
                    .children_with_tokens()
                    .any(|c| c.kind() == SyntaxKind::STRING_PREFIX)
                {
                    StringContext::Verbatim
                } else {
                    StringContext::Plain
                },
            ),
            _ => None,
        })
        .unwrap_or(StringContext::Code)
}

/// Whether `sequence` is a lone backslash-escape the Julia lexer would read as
/// one, like `\n` or `\u`.
///
/// Only consulted inside a plain string, and only for a one-character run: a
/// popup headed by `\nabla` the instant someone types `"\n` would be in the way
/// far more often than it helps. One more character disambiguates (`\na` is
/// nobody's escape), so `\nu` and `\alpha` are still one keystroke behind.
fn is_lone_escape(sequence: &str) -> bool {
    let mut chars = sequence.chars();
    let (Some(c), None) = (chars.next(), chars.next()) else {
        return false;
    };
    // The escapes Julia's lexer accepts after a backslash, per `read_escaped`
    // in JuliaSyntax's tokenizer.
    c.is_ascii_digit() || "abefnrtv\\'\"?xuU".contains(c)
}

// --- item construction -----------------------------------------------------

fn static_doc_text(doc: &crate::semantic::SemanticDoc) -> Option<&str> {
    match &doc.text {
        crate::ast::DocText::Static(text) => Some(text.as_str()),
        _ => None,
    }
}

/// For document-heavy completion lists, visit each attachment once instead of
/// checking every attachment for every visible binding. Preserve the first
/// static attachment (including empty ones), and keep sparse requests on the
/// existing no-allocation path.
fn candidate_items(
    model: &SemanticModel,
    candidates: Vec<Candidate>,
    ns: Namespace,
) -> Vec<CompletionItem> {
    const MIN_DOCS: usize = 24;
    const MIN_BINDINGS: usize = 24;
    let static_by_binding = (model.documentation().len() >= MIN_DOCS
        && candidates
            .iter()
            .filter(|candidate| matches!(candidate.source, Source::Binding(_)))
            .nth(MIN_BINDINGS - 1)
            .is_some())
    .then(|| {
        let mut indexed = std::collections::HashMap::with_capacity(model.documentation().len());
        for doc in model.documentation() {
            if let (Some(binding), Some(text)) = (doc.binding, static_doc_text(doc)) {
                indexed.entry(binding).or_insert(text);
            }
        }
        indexed
    });
    let binding_doc = |id| match &static_by_binding {
        Some(indexed) => indexed.get(&id).copied(),
        None => model
            .documentation_for_binding(id)
            .find_map(static_doc_text),
    };
    candidates
        .into_iter()
        .map(|candidate| candidate_item(model, candidate, ns, binding_doc))
        .collect()
}

/// Turn a visible [`Candidate`] into a completion item. A file binding gets a
/// precise kind from its [`BindingKind`]; a library name is classified by
/// convention (see [`heuristic_kind`]) and carries a lazy-resolve key.
fn candidate_item<'a>(
    model: &'a SemanticModel,
    cand: Candidate,
    ns: Namespace,
    binding_doc: impl FnOnce(BindingId) -> Option<&'a str>,
) -> CompletionItem {
    let label = cand.name.to_string();
    match cand.source {
        Source::Binding(id) => {
            let kind = model.binding(id).kind;
            let mut item = CompletionItem {
                label,
                kind: Some(binding_kind(kind)),
                detail: Some(binding_detail(kind).to_string()),
                ..Default::default()
            };
            set_doc(&mut item, binding_doc(id));
            item
        }
        // A workspace sibling lives in the library map under its package name,
        // so it resolves lazily through the same key as any library item.
        Source::Workspace { module } | Source::Using { module } | Source::System { module } => {
            library_item(label, &[module.to_string()], ns)
        }
    }
}

/// An item for a library name (a `using` export or a Base/Core name): a
/// convention-based kind, the source module as `detail`, and a resolve key.
fn library_item(name: String, module_path: &[String], ns: Namespace) -> CompletionItem {
    let detail = module_path.last().cloned();
    CompletionItem {
        label: name.clone(),
        kind: Some(heuristic_kind(&name, ns)),
        detail,
        data: resolve_data(module_path, &name),
        ..Default::default()
    }
}

fn keyword_item(kw: &str) -> CompletionItem {
    CompletionItem {
        label: kw.to_string(),
        kind: Some(CompletionItemKind::KEYWORD),
        ..Default::default()
    }
}

/// The lazy-resolve key for looking `name` up in the module at `module_path`.
fn resolve_data(module_path: &[String], name: &str) -> Option<serde_json::Value> {
    serde_json::to_value(ResolveData {
        module_path: module_path.to_vec(),
        name: name.to_string(),
    })
    .ok()
}

/// Map a file binding's kind to an LSP completion kind.
fn binding_kind(kind: BindingKind) -> CompletionItemKind {
    use BindingKind::*;
    match kind {
        Global | Local | ForVar | LetVar => CompletionItemKind::VARIABLE,
        Const => CompletionItemKind::CONSTANT,
        Param | KeywordParam | CatchParam => CompletionItemKind::VARIABLE,
        TypeParam => CompletionItemKind::TYPE_PARAMETER,
        Field => CompletionItemKind::FIELD,
        Function => CompletionItemKind::FUNCTION,
        // LSP has no macro kind; match the document-symbol convention.
        Macro => CompletionItemKind::FUNCTION,
        Type => CompletionItemKind::CLASS,
        Module => CompletionItemKind::MODULE,
        Import => CompletionItemKind::MODULE,
    }
}

/// Classify a library name without a module lookup: a macro is a function, a
/// `CamelCase` name is (by Julia convention) a type or module, anything else a
/// function. Precise kinds come from member completion, which has the module.
fn heuristic_kind(name: &str, ns: Namespace) -> CompletionItemKind {
    if ns == Namespace::Macro {
        return CompletionItemKind::FUNCTION;
    }
    match name.chars().next() {
        Some(c) if c.is_uppercase() => CompletionItemKind::CLASS,
        _ => CompletionItemKind::FUNCTION,
    }
}

/// Only a mid-token completion needs to override the client's word edit. An
/// explicit range avoids appending the old suffix in prefix-only clients.
fn complete_identifier_suffix(
    items: &mut [CompletionItem],
    text: &str,
    offset: TextSize,
    root: &SyntaxNode,
    lines: &LineIndex,
    encoding: PositionEncoding,
    macro_name: bool,
) {
    use crate::parser::{is_ident_continue, is_ident_start};

    let at: usize = offset.into();
    let tail = &text[at..];
    if !tail.chars().next().is_some_and(is_ident_continue) {
        return;
    }

    let mut suffix = tail.char_indices().peekable();
    let mut end = at;
    while let Some((relative, ch)) = suffix.next() {
        // Julia lexes a trailing `!=` as an operator, not half an identifier.
        if !is_ident_continue(ch) || ch == '!' && suffix.peek().is_some_and(|&(_, c)| c == '=') {
            break;
        }
        end = at + relative + ch.len_utf8();
    }
    if end == at {
        return;
    }
    let (prefix, before) = take_ident_back(&text[..at]);
    if !prefix.chars().next().is_some_and(is_ident_start)
        || string_context_at(root, offset) != StringContext::Code
    {
        return;
    }
    let range = lsp_types::Range::new(
        lines.byte_to_position(before.len(), encoding),
        lines.byte_to_position(end, encoding),
    );
    for item in items {
        if item.text_edit.is_some() || item.insert_text.is_some() {
            continue;
        }
        let label = if macro_name {
            let Some(label) = item.label.strip_prefix('@') else {
                continue;
            };
            label
        } else {
            &item.label
        };
        let mut chars = label.chars();
        if !chars.next().is_some_and(is_ident_start) || !chars.all(is_ident_continue) {
            continue;
        }
        if macro_name {
            item.filter_text = Some(label.to_string());
        }
        item.text_edit = Some(CompletionTextEdit::Edit(TextEdit {
            range,
            new_text: label.to_string(),
        }));
    }
}

// --- member completion -----------------------------------------------------

/// Keep the typed `@` outside the identifier edit. The label and lazy-resolve
/// key still identify a macro, while clients can match and replace just its
/// identifier (including any suffix to the right of the cursor).
fn qualified_macro_edits(
    items: &mut [CompletionItem],
    text: &str,
    offset: usize,
    lines: &LineIndex,
    encoding: PositionEncoding,
) {
    let (_, before_name) = take_ident_back(&text[..offset]);
    let suffix_bytes: usize = text[offset..]
        .chars()
        .take_while(|&c| is_ident_char(c))
        .map(char::len_utf8)
        .sum();
    let range = lsp_types::Range::new(
        lines.byte_to_position(before_name.len(), encoding),
        lines.byte_to_position(offset + suffix_bytes, encoding),
    );
    for item in items {
        if let Some(name) = item.label.strip_prefix('@') {
            item.filter_text = Some(name.to_string());
            item.text_edit = Some(CompletionTextEdit::Edit(TextEdit {
                range,
                new_text: name.to_string(),
            }));
        }
    }
}

/// Every name defined in the library module named by `receiver`, or empty when
/// the receiver does not resolve to a harvested module. `macro_member` (the
/// `Foo.@` case) keeps only macros; otherwise macros are dropped and the rest
/// kept.
fn member_completions<P: PackageSource>(
    model: &SemanticModel,
    packages: &P,
    workspace: Option<(Arc<PackageIndex>, ModulePath)>,
    receiver: &[String],
    offset: TextSize,
    receiver_start: Option<TextSize>,
    macro_member: bool,
) -> Vec<CompletionItem> {
    let written: ModulePath = receiver.iter().map(Into::into).collect();
    let resolver = Resolver::new(model, packages).with_workspace(workspace.clone());
    let Some(resolved) = resolver.module_receiver_path(&written, offset, receiver_start) else {
        return Vec::new();
    };
    let Some((head, tail)) = resolved.split_first() else {
        return Vec::new();
    };
    let pkg = workspace
        .as_ref()
        .map(|(package, _)| package)
        .filter(|package| package.name == head.as_str())
        .cloned()
        .or_else(|| packages.package(head));
    let Some(pkg) = pkg else { return Vec::new() };
    let tail: Vec<&str> = tail.iter().map(|part| part.as_str()).collect();
    let Some(module) = resolve_submodule(&pkg.root, &tail) else {
        return Vec::new();
    };
    let resolved: Vec<String> = resolved.iter().map(ToString::to_string).collect();
    cached_member_items(&pkg, module, &resolved, macro_member)
}

/// Keep candidate templates only after resolving the receiver in its actual
/// lexical context. A weak key ties the entry to the exact immutable index
/// generation, without pinning replaced indexes or mixing loading contexts.
/// Requests still add their own resolve source path after cloning templates.
struct MemberTemplates {
    package: Weak<PackageIndex>,
    path: Vec<String>,
    macros: bool,
    items: Arc<Vec<CompletionItem>>,
}

fn cached_member_items(
    package: &Arc<PackageIndex>,
    module: &ModuleIndex,
    path: &[String],
    macros: bool,
) -> Vec<CompletionItem> {
    static CACHE: Mutex<Vec<MemberTemplates>> = Mutex::new(Vec::new());
    let size = if macros {
        module.macros.len()
    } else {
        module.types.len() + module.consts.len() + module.functions.len() + module.submodules.len()
    };
    if !(32..=4096).contains(&size) || path.iter().map(String::len).sum::<usize>() > 256 {
        return member_items(module, path, macros);
    }
    let key = Arc::downgrade(package);
    let hit = {
        let mut entries = CACHE
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        entries.retain(|entry| entry.package.strong_count() > 0);
        entries
            .iter()
            .position(|entry| {
                Weak::ptr_eq(&entry.package, &key) && entry.macros == macros && entry.path == path
            })
            .map(|index| {
                let entry = entries.remove(index);
                let result = Arc::clone(&entry.items);
                entries.push(entry);
                result
            })
    };
    if let Some(items) = hit {
        return items.as_ref().clone();
    }
    let items = member_items(module, path, macros);
    let name_bytes: usize = items.iter().map(|item| item.label.len()).sum();
    if name_bytes <= 128 * 1024 {
        let mut entries = CACHE
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !entries.iter().any(|entry| {
            Weak::ptr_eq(&entry.package, &key) && entry.macros == macros && entry.path == path
        }) {
            if entries.len() == 8 {
                entries.remove(0);
            }
            entries.push(MemberTemplates {
                package: key,
                path: path.to_vec(),
                macros,
                items: Arc::new(items.clone()),
            });
        }
    }
    items
}

/// The items for a resolved module's defined names, preferring type and alias
/// declarations over constructor groups.
fn member_items(module: &ModuleIndex, path: &[String], macro_member: bool) -> Vec<CompletionItem> {
    let mut items = Vec::new();
    if macro_member {
        for m in &module.macros {
            items.push(member_item(&m.name, CompletionItemKind::FUNCTION, path));
        }
        return items;
    }
    let mut seen = std::collections::HashSet::new();
    for t in &module.types {
        if seen.insert(t.name.as_str()) {
            items.push(member_item(&t.name, CompletionItemKind::CLASS, path));
        }
    }
    for c in &module.consts {
        if seen.insert(c.name.as_str()) {
            items.push(member_item(&c.name, CompletionItemKind::CONSTANT, path));
        }
    }
    for f in &module.functions {
        // A qualified extension (`Base.show`) is not a name of this module.
        if f.owner.is_none() && seen.insert(f.name.as_str()) {
            items.push(member_item(&f.name, CompletionItemKind::FUNCTION, path));
        }
    }
    for s in &module.submodules {
        if seen.insert(s.name.as_str()) {
            items.push(member_item(&s.name, CompletionItemKind::MODULE, path));
        }
    }
    items
}

fn member_item(name: &str, kind: CompletionItemKind, module_path: &[String]) -> CompletionItem {
    CompletionItem {
        label: name.to_string(),
        kind: Some(kind),
        detail: module_path.last().cloned(),
        data: resolve_data(module_path, name),
        ..Default::default()
    }
}

// --- resolve (lazy docs) ---------------------------------------------------

/// The resolve step, taking a `lookup` from package name to its index so it can
/// be unit-tested without a salsa db.
fn resolve_completion_with(
    lookup: &dyn Fn(&str) -> Option<Arc<PackageIndex>>,
    mut item: CompletionItem,
) -> CompletionItem {
    let Some(data) = item.data.take() else {
        return item;
    };
    let Ok(data) = serde_json::from_value::<ResolveData>(data) else {
        return item;
    };
    let Some((head, tail)) = data.module_path.split_first() else {
        return item;
    };
    let Some(pkg) = lookup(head) else {
        return item;
    };
    let tail: Vec<&str> = tail.iter().map(String::as_str).collect();
    let Some(module) = resolve_submodule(&pkg.root, &tail) else {
        return item;
    };
    enrich(&mut item, module, &data.name);
    item
}

// Signature and type rendering moved to `super::render`, shared with hover.

/// Fill `item`'s signature detail and documentation from the definition of
/// `name` in `module`, preferring type and alias metadata over constructor groups.
fn enrich(item: &mut CompletionItem, module: &ModuleIndex, name: &str) {
    if name.starts_with('@') {
        if let Some(m) = module.macros.iter().find(|m| m.name == name) {
            set_doc(item, m.doc.as_ref().map(|d| d.text.as_str()));
        }
        return;
    }
    if let Some(t) = module.types.iter().find(|t| t.name == name) {
        item.detail = Some(type_detail(t));
        set_doc(item, t.doc.as_ref().map(|d| d.text.as_str()));
        return;
    }
    if let Some(c) = module.consts.iter().find(|c| c.name == name) {
        if let Some(repr) = &c.value_repr {
            item.detail = Some(format!("{name} = {repr}"));
        }
        set_doc(item, c.doc.as_ref().map(|d| d.text.as_str()));
        return;
    }
    if let Some(f) = module.functions.iter().find(|f| f.name == name) {
        item.detail = Some(function_detail(f));
        set_doc(item, f.doc.as_ref().map(|d| d.text.as_str()));
    }
}

fn set_doc(item: &mut CompletionItem, doc: Option<&str>) {
    if let Some(text) = doc.and_then(super::documentation::render) {
        item.documentation = Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: text,
        }));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    use std::sync::Arc;

    use crate::index::model::{DefLocation, ExportedName, PackageIndex, Span, Visibility};
    use crate::index::{
        ConstDef, FunctionGroup, MacroDef, Method, Param, TypeDef, TypeExpr, TypeKind,
    };

    fn loc() -> DefLocation {
        DefLocation {
            file: "src/x.jl".into(),
            range: Span { start: 0, end: 0 },
        }
    }

    /// A module with the given name, exports, and defined members.
    fn module(name: &str, exports: &[&str]) -> ModuleIndex {
        ModuleIndex {
            name: name.to_string(),
            bare: false,
            loc: loc(),
            doc: None,
            exports: exports
                .iter()
                .map(|n| ExportedName {
                    name: n.to_string(),
                    visibility: Visibility::Exported,
                    loc: loc(),
                })
                .collect(),
            functions: Vec::new(),
            types: Vec::new(),
            consts: Vec::new(),
            macros: Vec::new(),
            submodules: Vec::new(),
            usings: Vec::new(),
            imported_names: Vec::new(),
        }
    }

    fn package(root: ModuleIndex) -> Arc<PackageIndex> {
        Arc::new(PackageIndex {
            name: root.name.clone(),
            root,
            members: Vec::new(),
            member_modules: Default::default(),
            diagnostics: Vec::new(),
        })
    }

    fn library(pkgs: Vec<Arc<PackageIndex>>) -> BTreeMap<String, Arc<PackageIndex>> {
        pkgs.into_iter().map(|p| (p.name.clone(), p)).collect()
    }

    fn func(name: &str) -> FunctionGroup {
        FunctionGroup {
            name: name.to_string(),
            owner: None,
            methods: Vec::new(),
            doc: None,
        }
    }

    /// Completions at the position just past `needle` in `src`.
    fn completions_at(
        src: &str,
        needle: &str,
        lib: &BTreeMap<String, Arc<PackageIndex>>,
    ) -> Vec<CompletionItem> {
        let offset = src.find(needle).unwrap() + needle.len();
        let line_index = LineIndex::new(src);
        let position = line_index.byte_to_position(offset, PositionEncoding::Utf16);
        compute_completions(src, position, PositionEncoding::Utf16, lib)
    }

    #[test]
    fn mid_identifier_edits_replace_existing_suffix_without_touching_punctuation() {
        let mut base = module("Base", &[]);
        base.functions.push(func("sqrt"));
        let lib = library(vec![package(base)]);
        for (source, prefix, old, candidate, expected) in [
            (
                "detuning = 1\ndetuNIng != nothing",
                "\ndet",
                "detuNIng",
                "detuning",
                "detuning",
            ),
            ("f() = Base.sqrtt(2)", "Base.sq", "sqrtt", "sqrt", "sqrt"),
            (
                "λ = 1; text = \"🔬\"; Base.sqrtt!=2",
                "Base.sq",
                "sqrtt",
                "sqrt",
                "sqrt",
            ),
            (
                "macro sparkle() end\n@spWRONG 1",
                "@sp",
                "spWRONG",
                "@sparkle",
                "sparkle",
            ),
        ] {
            let items = completions_at(source, prefix, &lib);
            let found = items.iter().find(|item| item.label == candidate).unwrap();
            let at = source.rfind(old).unwrap();
            let lines = LineIndex::new(source);
            assert_eq!(
                edit(found),
                (
                    expected,
                    lsp_types::Range::new(
                        lines.byte_to_position(at, PositionEncoding::Utf16),
                        lines.byte_to_position(at + old.len(), PositionEncoding::Utf16),
                    ),
                ),
                "{source}",
            );
        }
        let items = completions_at("detuning = 1\ndet", "\ndet", &lib);
        assert!(
            items
                .iter()
                .find(|i| i.label == "detuning")
                .unwrap()
                .text_edit
                .is_none()
        );
        let literal = "detuning = 1\nprint(\"detuNIng\")";
        let items = completions_at(literal, "\"det", &lib);
        assert!(
            items
                .iter()
                .find(|i| i.label == "detuning")
                .unwrap()
                .text_edit
                .is_none()
        );
    }

    fn labels(items: &[CompletionItem]) -> Vec<String> {
        items.iter().map(|i| i.label.clone()).collect()
    }

    fn at_declaration_marker(body: &str) -> Vec<CompletionItem> {
        let mut src = format!("const visible_candidate = 1\n{body}\n");
        let offset = src.find('│').unwrap();
        src.remove(offset);
        let pos = LineIndex::new(&src).byte_to_position(offset, PositionEncoding::Utf16);
        compute_completions(&src, pos, PositionEncoding::Utf16, &library(vec![]))
    }

    #[test]
    fn declaration_names_withhold_existing_names_only_for_proven_binders() {
        for body in [
            "map(xs) do arg│\n end",
            "map(xs) do a, arg│\n end",
            "map(xs) do (arg│, a)\n end",
            "msg = \"😀\"; map(xs) do κεφ│άλαιο\n end",
            "map(xs) do arg│",
            "function f(arg│)\n end",
            "function f(arg│::Int=1)\n end",
            "function f(arg│...)\n end",
            "f(arg│)=nothing",
            "function f(; arg│=1)\n end",
            "f(arg│=1)=nothing",
            "g = function (arg│)\n end",
            "g = (arg│, x) -> x",
            "macro f(arg│)\n end",
            "for arg│ in xs\n end",
            "for a in ys, arg│ in xs\n end",
            "for (arg│, b) ∈ xs\n end",
            "for arg│ = xs\n end",
            "for a=ys, arg│ in xs\n end",
            "for a in ys, arg│ = xs\n end",
            "[x for arg│ in xs]",
            "(x for arg│ in xs)",
            "let arg│\n end",
            "let first = 1, (arg│, b) = xs\n end",
            "try\n nothing\ncatch arg│\n end",
            "function f()\n local arg│\nend",
            "function f()\n local arg│::Int=1\nend",
            "function f()\n local (arg│, b) = xs\nend",
        ] {
            assert!(at_declaration_marker(body).is_empty(), "{body}");
        }
    }

    #[test]
    fn declaration_names_keep_references_and_ambiguous_input() {
        for body in [
            "map(xs) do │\n end",
            "map(xs) do a\n vis│\n end",
            "map(xs) do a; vis│; end",
            "map(xs) do a::Vis│\n end",
            "function f(x=vis│)\n end",
            "function f(x::Vis│)\n end",
            "function f(x::Int=vis│)\n end",
            "function f(; key=vis│)\n end",
            "function f(visible = (x -> x))\n vis│ible\n end",
            "f(vis│)",
            "f(vis│",
            "f(; vis│)",
            "f(; key=vis│)",
            "f(; vis│=1)",
            "g = x -> vis│",
            "macro fa│(x)\n end",
            "function fa│(x)\n end",
            "struct A\n vis│::Int\n end",
            "for vis│\n end",
            "for a in vis│\n end",
            "for a=ys, b in vis│\n end",
            "for a=vis│, b in xs\n end",
            "for arg::Vis│ in xs\n end",
            "for a in xs\n vis│\n end",
            "[x for a in vis│]",
            "[a for a in xs if vis│]",
            "let x=vis│\n end",
            "let arg; vis│; end",
            "try\n nothing\ncatch ex\n vis│\n end",
            "function f(existing)\n for outer ex│isting in xs\n end\n end",
            "function f()\n local x=(vis│=1)\nend",
            "function f()\n local x=vis│\nend",
            "function f()\n vis│=1\nend",
            "function f()\n (vis│, b)=xs\nend",
            "xs[vis│]=1",
            "vis│.field=1",
        ] {
            let names = labels(&at_declaration_marker(body));
            assert!(
                names.iter().any(|name| name == "visible_candidate"),
                "{body}: {names:?}"
            );
        }
    }

    #[test]
    fn explicit_named_tuple_keys_are_not_reference_slots() {
        for body in [
            "(; name│=2)",
            "(; prior, name│=2)",
            "(name│=2,)",
            "(name│=2, other=3)",
            "f((; name│=2))",
        ] {
            assert!(at_declaration_marker(body).is_empty(), "{body}");
        }
        for body in [
            "(; vis│)",
            "(; name=│)",
            "(; name=vis│)",
            "(vis│=2)",
            "(vis│=2, unnamed)",
            "f(; vis│=2)",
            "f(vis│=2, other=3)",
            "x = :( (; vis│=2) )",
            "quote\n (; vis│=2)\nend",
        ] {
            let names = labels(&at_declaration_marker(body));
            assert!(
                names.iter().any(|name| name == "visible_candidate"),
                "{body}: {names:?}"
            );
        }
    }

    #[test]
    fn doc_fences_do_not_restore_outer_names_at_declarations() {
        let fence =
            |body: &str| format!("\"\"\"\n```julia\n{body}\n```\n\"\"\"\nf()=visible_candidate\n");
        assert!(at_declaration_marker(&fence("map(xs) do arg│\nend")).is_empty());
        assert!(at_declaration_marker(&fence("(; key│=2)")).is_empty());
        let labels = labels(&at_declaration_marker(&fence("map(xs) do arg\n vis│\nend")));
        assert!(labels.iter().any(|name| name == "arg"));
        assert!(labels.iter().any(|name| name == "visible_candidate"));
    }

    #[test]
    fn member_templates_are_scoped_to_the_exact_package_index() {
        let make_index = |last: &str| {
            let mut root = module("TemplatePkg", &[]);
            root.functions = (0..64).map(|i| func(&format!("f{i}"))).collect();
            root.functions.push(func(last));
            package(root)
        };
        let first = make_index("before");
        let second = make_index("after");
        let path = vec!["TemplatePkg".into()];
        let mut first_items = cached_member_items(&first, &first.root, &path, false);
        assert_eq!(first_items.last().unwrap().label, "before");
        first_items.pop();
        assert_eq!(
            cached_member_items(&first, &first.root, &path, false).len(),
            65
        );
        assert_eq!(
            cached_member_items(&second, &second.root, &path, false)
                .last()
                .unwrap()
                .label,
            "after"
        );
    }

    #[test]
    fn comments_are_quiet_but_keep_unicode_sequences() {
        assert!(completions_bare("# comment_name", "comment_name").is_empty());
        assert!(completions_bare("#= comment_name =#", "comment_name").is_empty());
        assert!(!completions_bare("#= comment_name =#", "=#").is_empty());
        assert_eq!(labels(&completions_bare("# \\alph", "\\alph")), ["\\alpha"]);
    }

    /// Completions at the position just past `needle`, resolving free names
    /// against `workspace` (the enclosing package's module) too.
    fn completions_ws(
        src: &str,
        needle: &str,
        lib: &BTreeMap<String, Arc<PackageIndex>>,
        workspace: Arc<PackageIndex>,
    ) -> Vec<CompletionItem> {
        let root = parse(src).cst;
        let model = SemanticModel::build(&root);
        let offset = TextSize::new((src.find(needle).unwrap() + needle.len()) as u32);
        completions_for(
            &model,
            &root,
            lib,
            Some((workspace, Vec::new())),
            src,
            offset,
            PositionEncoding::Utf16,
            &LineIndex::new(src),
            None,
        )
    }

    /// Completions at the position just past `needle`, with no library at all.
    fn completions_bare(src: &str, needle: &str) -> Vec<CompletionItem> {
        completions_at(src, needle, &library(vec![]))
    }

    /// The item labelled `label`, panicking when it was not offered.
    fn item<'a>(items: &'a [CompletionItem], label: &str) -> &'a CompletionItem {
        items
            .iter()
            .find(|i| i.label == label)
            .unwrap_or_else(|| panic!("no {label:?} in {:?}", labels(items)))
    }

    /// The text an item inserts and the range it replaces.
    fn edit(item: &CompletionItem) -> (&str, lsp_types::Range) {
        match item.text_edit.as_ref().expect("a text edit") {
            CompletionTextEdit::Edit(e) => (e.new_text.as_str(), e.range),
            other => panic!("expected a plain edit, got {other:?}"),
        }
    }

    fn auto_import_fixture(source: &str, mode: &str) -> Vec<CompletionItem> {
        use crate::environment::{EnvSource, Environment, Package, PackageKind};
        use crate::incremental::IncrementalDatabase;
        use std::collections::BTreeSet;
        use std::fs;

        let temp = tempfile::tempdir().unwrap();
        let dir = temp.path();
        let project = dir.join("Project.toml");
        let manifest = dir.join("Manifest.toml");
        let id = "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee";
        let id2 = "aaaaaaaa-bbbb-cccc-dddd-ffffffffffff";
        let direct = match mode {
            "transitive" => format!("[extras]\nTools = \"{id}\"\n"),
            "uuid_mismatch" => format!("[deps]\nTools = \"{id2}\"\n"),
            "duplicate" => format!("[deps]\nTools = \"{id}\"\nTools2 = \"{id2}\"\n"),
            _ => format!("[deps]\nTools = \"{id}\"\n"),
        };
        fs::write(&project, format!("name = \"Tester\"\n{direct}")).unwrap();
        fs::write(&manifest, format!(
            "manifest_format = \"2.0\"\n[[deps.Tools]]\nuuid = \"{id}\"\npath = \"Tools\"\n[[deps.Tools2]]\nuuid = \"{id2}\"\npath = \"Tools2\"\n"
        )).unwrap();
        fs::create_dir(dir.join("src")).unwrap();
        fs::write(dir.join("src").join("sibling.jl"), "helper() = 1\n").unwrap();
        let entry = dir.join("src").join("Tester.jl");
        let (left, right) = source.split_once('|').unwrap();
        let text = format!("{left}{right}");
        fs::write(&entry, &text).unwrap();
        let packages = [("Tools", id), ("Tools2", id2)].into_iter().map(|(name, id)| {
            let root = dir.join(name);
            fs::create_dir_all(root.join("src")).unwrap();
            fs::write(root.join("src").join(format!("{name}.jl")), format!(
                "module {name}\nexport calculate, ghost, calculator\ncalculate() = 2\nstruct calculator end\nend\n"
            )).unwrap();
            Package {
                syntax_edition: crate::parser::SyntaxEdition::OLDEST,
                name: name.into(), uuid: id.parse().unwrap(), version: None, tree_sha1: None,
                deps: vec![], extensions: vec![], kind: PackageKind::Dev, source: Some(root),
            }
        }).collect();
        let env = Environment {
            project_file: project,
            project_dir: dir.into(),
            manifest_file: Some(manifest),
            name: Some("Tester".into()),
            uuid: None,
            direct_deps: BTreeMap::new(),
            declared_deps: BTreeSet::new(),
            packages,
            depots: vec![],
            source: EnvSource::WorkspaceWalkUp,
            install: None,
        };
        let indexed = crate::index::harvest_library(&env);
        let mut db = IncrementalDatabase::default();
        db.set_library_syntax(indexed.syntax);
        db.set_project_files(indexed.project_files);
        db.set_library(indexed.packages, indexed.roots, indexed.workspaces);
        db.seed_workspace_members();
        let snapshot = db.snapshot();
        let (context, selection) = snapshot
            .capture_source_editions(&entry)
            .into_iter()
            .next()
            .unwrap();
        let snapshot = snapshot.with_context(context, selection.options);
        let encoding = PositionEncoding::Utf16;
        let at = LineIndex::new(&text).byte_to_position(left.len(), encoding);
        completion_via_db(&snapshot, &entry, &TextBuffer::new(text), at, encoding)
    }

    fn legacy_candidate_items(
        model: &SemanticModel,
        candidates: Vec<Candidate>,
        ns: Namespace,
    ) -> Vec<CompletionItem> {
        candidates
            .into_iter()
            .map(|candidate| {
                candidate_item(model, candidate, ns, |id| {
                    model
                        .documentation_for_binding(id)
                        .find_map(static_doc_text)
                })
            })
            .collect()
    }

    #[test]
    fn ordinary_completions_do_not_fall_back_inside_import_alias_destination() {
        for statement in [
            "import Base as ou",
            "using .LocalTool: bell as ou",
            "import Base as ",
        ] {
            let src = format!("outer_visible = 1\n{statement}");
            assert!(completions_bare(&src, statement).is_empty(), "{statement}");
        }
        let src = "outer_visible = 1\nimport Base as renamed\nou";
        let items = completions_bare(src, "\nou");
        assert!(labels(&items).iter().any(|label| label == "outer_visible"));
    }

    #[test]
    fn indexed_candidate_docs_preserve_first_static_and_all_item_fields() {
        let mut src = concat!(
            "\"First\"\nfoo(x::Int) = x\n",
            "\"Second\"\nfoo(x::Float64) = x\n",
            "\"\"\nempty_doc(x::Int) = x\n",
            "\"Later\"\nempty_doc(x::Float64) = x\n",
            "\"$interpolated\"\nopaque_doc(x::Int) = x\n",
            "\"Fallback static\"\nopaque_doc(x::Float64) = x\n",
        )
        .to_string();
        for n in 0..35 {
            src.push_str(&format!("\"Doc {n}\"\nf_{n}() = {n}\n"));
        }
        src.push_str("undoc() = 0\n");
        let root = parse(&src).cst;
        let model = SemanticModel::build(&root);
        let packages = BTreeMap::new();
        let at = (src.len() as u32).into();
        let candidates = Resolver::new(&model, &packages).visible(at, Namespace::Value);
        assert!(model.documentation().len() >= 24);
        assert!(
            candidates
                .iter()
                .filter(|c| matches!(c.source, Source::Binding(_)))
                .count()
                >= 24
        );
        let expected = legacy_candidate_items(&model, candidates.clone(), Namespace::Value);
        let actual = candidate_items(&model, candidates, Namespace::Value);
        assert_eq!(actual, expected);
        fn text(item: &CompletionItem) -> Option<&str> {
            match &item.documentation {
                Some(Documentation::MarkupContent(content)) => Some(&content.value),
                _ => None,
            }
        }
        assert_eq!(text(item(&actual, "foo")), Some("First"));
        assert_eq!(text(item(&actual, "empty_doc")), None);
        assert_eq!(text(item(&actual, "opaque_doc")), Some("Fallback static"));
        assert_eq!(text(item(&actual, "undoc")), None);
    }

    #[test]
    fn auto_import_adds_exact_using_at_root_with_non_overlapping_edits() {
        let offered = auto_import_fixture(
            "#!/usr/bin/julia\r\nmodule Tester\r\n\r\n# user comment\r\n\"Docs\"\r\nprior() = 1\r\nf() = (\"🚀\"; calc|())\r\nend\r\n",
            "direct",
        );
        let item = item(&offered, "calculate");
        assert_eq!(item.kind, Some(CompletionItemKind::FUNCTION));
        assert_eq!(item.detail.as_deref(), Some("Auto-import from Tools"));
        let (replacement, range) = edit(item);
        assert_eq!(replacement, "calculate");
        assert_eq!(
            range,
            lsp_types::Range::new(Position::new(6, 13), Position::new(6, 17))
        );
        let imports = item.additional_text_edits.as_ref().unwrap();
        assert_eq!(imports.len(), 1);
        assert_eq!(
            imports[0].range,
            lsp_types::Range::new(Position::new(2, 0), Position::new(2, 0))
        );
        assert_eq!(imports[0].new_text, "using Tools: calculate\r\n");
    }

    #[test]
    fn auto_import_offers_bare_value_and_only_defined_exports() {
        let offered = auto_import_fixture("module Tester\nf() = calc|\nend\n", "direct");
        assert!(item(&offered, "calculate").additional_text_edits.is_some());
        assert_eq!(
            item(&offered, "calculator").kind,
            Some(CompletionItemKind::CLASS)
        );
        assert!(
            auto_import_fixture("module Tester\nf() = gho|\nend\n", "direct")
                .iter()
                .all(|item| item.label != "ghost")
        );
    }

    #[test]
    fn auto_import_skips_unknown_scope_collisions_and_non_direct_packages() {
        let cases = [
            ("module Tester\nf() = calc|()\nend", "transitive"),
            ("module Tester\nf() = calc|()\nend", "uuid_mismatch"),
            ("module Tester\nf() = calc|()\nend", "duplicate"),
            ("module Tester\nusing Unknown\nf() = calc|()\nend", "direct"),
            (
                "module Tester\nusing Tools: calculator\nf() = calc|()\nend",
                "direct",
            ),
            (
                "module Tester\n@eval calculate() = 3\nf() = calc|()\nend",
                "direct",
            ),
            (
                "module Tester\ncalculate() = 2\ncalculator() = 3\nf() = calc|()\nend",
                "direct",
            ),
            ("module Tester\nf(calculator) = calc|()\nend", "duplicate"),
            (
                "module Tester\nmodule Child\nf() = calc|()\nend\nend",
                "direct",
            ),
            ("module Tester\nf() = :(calc|())\nend", "direct"),
            ("module Tester\nf() = @foo calc|()\nend", "direct"),
            ("module Tester\nf() = Tools.calc|()\nend", "direct"),
            (
                "module Tester\nf() = g(calc|())\nend # no parser error",
                "duplicate",
            ),
            ("module Tester\ncalc|() = 3\nend", "direct"),
            (
                "module Tester\ninclude(\"sibling.jl\")\nf() = calc|()\nend",
                "direct",
            ),
            (
                "module Tester # same-line comment\nf() = calc|()\nend",
                "direct",
            ),
            ("module Tester\nf() = calc|()", "direct"),
            ("baremodule Tester\nf() = calc|()\nend", "direct"),
        ];
        for (source, mode) in cases {
            assert!(
                auto_import_fixture(source, mode)
                    .iter()
                    .all(|item| item.additional_text_edits.is_none()),
                "{mode}: {source}"
            );
        }
    }

    #[test]
    fn value_context_offers_workspace_siblings() {
        // `sibling`, a top-level function of the enclosing workspace package,
        // is offered even though it is not defined in this file.
        let lib = library(vec![package(module("Base", &["println"]))]);
        let ws = package(ModuleIndex {
            functions: vec![func("sibling")],
            ..module("MyPkg", &[])
        });
        let src = "function f()\n    \nend";
        let items = completions_ws(src, "    ", &lib, ws);
        let names = labels(&items);
        assert!(names.contains(&"sibling".to_string()), "{names:?}");
        // The sibling ranks after locals and before Base.
        assert!(
            names.iter().position(|n| n == "sibling") < names.iter().position(|n| n == "println")
        );
    }

    #[test]
    fn value_context_lists_locals_before_library_and_includes_keywords() {
        let lib = library(vec![package(module("Base", &["println"]))]);
        let src = "function f(a)\n    b = 1\n    \nend";
        let items = completions_at(src, "b = 1\n    ", &lib);
        let names = labels(&items);
        for expected in ["a", "b", "f", "println", "function", "end"] {
            assert!(names.contains(&expected.to_string()), "missing {expected}");
        }
        // Locals precede the library name.
        assert!(names.iter().position(|n| n == "b") < names.iter().position(|n| n == "println"));
        // A keyword is a KEYWORD item.
        let kw = items.iter().find(|i| i.label == "function").unwrap();
        assert_eq!(kw.kind, Some(CompletionItemKind::KEYWORD));
    }

    #[test]
    fn local_completion_carries_decoded_documentation() {
        let lib = library(vec![]);
        let src = "\"A decoded\\n**docstring**.\"\ngreet(name) = name\ngr";
        let items = completions_at(src, "\ngr", &lib);
        let greet = item(&items, "greet");
        match &greet.documentation {
            Some(Documentation::MarkupContent(markup)) => {
                assert_eq!(markup.value, "A decoded\n**docstring**.")
            }
            other => panic!("expected decoded markdown documentation, got {other:?}"),
        }
    }

    #[test]
    fn explicit_ref_offers_symbols_but_ordinary_prose_does_not() {
        let lib = library(vec![]);
        let source = concat!(
            "\"\"\"\n",
            "See [`greet`](@ref gre) and ordinary gre prose.\n",
            "\"\"\"\n",
            "greet(name) = name\n",
        );
        let ref_items = completions_at(source, "@ref gre", &lib);
        assert!(labels(&ref_items).contains(&"greet".to_string()));
        let prose_items = completions_at(source, "ordinary gre", &lib);
        assert!(
            prose_items.is_empty(),
            "prose should not offer Julia names: {:?}",
            labels(&prose_items)
        );
    }

    #[test]
    fn incomplete_explicit_ref_still_offers_completion() {
        let lib = library(vec![]);
        let source = concat!(
            "\"\"\"\n",
            "See [`greet`](@ref gre\n",
            "\"\"\"\n",
            "greet(name) = name\n",
        );
        let names = labels(&completions_at(source, "@ref gre", &lib));
        assert!(names.contains(&"greet".to_string()), "{names:?}");
    }

    #[test]
    fn embedded_julia_completion_sees_fence_locals() {
        let lib = library(vec![]);
        let source = concat!(
            "\"\"\"\n",
            "```julia\n",
            "example_value = 1\n",
            "example_\n",
            "```\n",
            "\"\"\"\n",
            "f() = 1\n",
        );
        let names = labels(&completions_at(source, "\nexample_", &lib));
        assert!(names.contains(&"example_value".to_string()), "{names:?}");
    }

    #[test]
    fn embedded_julia_completion_sees_the_documented_file_scope() {
        let lib = library(vec![]);
        let source = concat!(
            "\"\"\"\n",
            "```julia\n",
            "gre\n",
            "```\n",
            "\"\"\"\n",
            "greet(name) = name\n",
        );
        let names = labels(&completions_at(source, "\ngre", &lib));
        assert!(names.contains(&"greet".to_string()), "{names:?}");
    }

    #[test]
    fn explicit_ref_completes_qualified_workspace_members() {
        let lib = library(vec![]);
        let workspace = package(ModuleIndex {
            functions: vec![func("greet")],
            ..module("MyPkg", &[])
        });
        let source = concat!(
            "\"\"\"\n",
            "See [`greet`](@ref MyPkg.gre).\n",
            "\"\"\"\n",
            "f() = 1\n",
        );
        let names = labels(&completions_ws(source, "MyPkg.gre", &lib, workspace));
        assert!(names.contains(&"greet".to_string()), "{names:?}");
    }

    #[test]
    fn explicit_ref_completes_markdown_anchors() {
        let lib = library(vec![]);
        let source = concat!(
            "\"\"\"\n",
            "# [Overview](@id custom-overview)\n",
            "\n",
            "See [above](@ref custom-ov).\n",
            "\"\"\"\n",
            "f() = 1\n",
        );
        let items = completions_at(source, "@ref custom-ov", &lib);
        let anchor = item(&items, "custom-overview");
        assert_eq!(anchor.kind, Some(CompletionItemKind::REFERENCE));
        let (new_text, range) = edit(anchor);
        assert_eq!(new_text, "custom-overview");
        assert_eq!(range.start, Position::new(3, 17));
        assert_eq!(range.end, Position::new(3, 26));
    }

    #[test]
    fn markdown_anchors_stay_out_of_embedded_julia_completion() {
        let lib = library(vec![]);
        let source = concat!(
            "\"\"\"\n",
            "# [Overview](@id custom_overview)\n",
            "\n",
            "```julia\n",
            "custom_\n",
            "```\n",
            "\"\"\"\n",
            "f() = 1\n",
        );
        let names = labels(&completions_at(source, "\ncustom_", &lib));
        assert!(
            !names.contains(&"custom_overview".to_string()),
            "an anchor leaked into Julia code completion: {names:?}"
        );
    }

    /// Only documentation prose withholds identifier completion; an ordinary
    /// string or command literal is not documentation.
    #[test]
    fn plain_strings_and_commands_keep_identifier_completion() {
        let lib = library(vec![]);
        for (source, needle) in [
            ("greeting = 1\npath = \"gree\"\n", "\"gree"),
            ("greeting = 1\ncmd = `run gree`\n", "run gree"),
        ] {
            let names = labels(&completions_at(source, needle, &lib));
            assert!(
                names.contains(&"greeting".to_string()),
                "{source:?}: {names:?}"
            );
        }
    }

    #[test]
    fn interpolations_keep_julia_completion_inside_strings() {
        let lib = library(vec![]);
        let source = "greeting = \"hello\"\nmessage = \"$(gree)\"\n";
        let names = labels(&completions_at(source, "$(gree", &lib));
        assert!(names.contains(&"greeting".to_string()), "{names:?}");
    }

    #[test]
    fn shadowed_name_appears_once() {
        let lib = library(vec![package(module("Base", &["map"]))]);
        let src = "function f()\n    map = 1\n    \nend";
        let names = labels(&completions_at(src, "map = 1\n    ", &lib));
        assert_eq!(names.iter().filter(|n| *n == "map").count(), 1);
    }

    #[test]
    fn macro_context_offers_only_at_names() {
        let mut base = module("Base", &["@time", "time"]);
        base.macros.push(MacroDef {
            name: "@time".into(),
            params: Vec::new(),
            doc: None,
            loc: loc(),
        });
        let lib = library(vec![package(base)]);
        let src = "@t";
        let names = labels(&completions_at(src, "@t", &lib));
        assert!(names.contains(&"@time".to_string()));
        assert!(!names.contains(&"time".to_string()));
    }

    #[test]
    fn member_context_respects_a_visible_receiver_binding() {
        let mut base = module("Base", &[]);
        base.functions.push(func("indexed_member"));
        let lib = library(vec![package(base)]);
        for (source, cursor) in [
            ("function f(Base)\n    Base.in\nend", "Base.in"),
            ("function f()\n    Base.in\n    Base = 1\nend", "Base.in"),
            ("let Base = 1\n    Base.in\nend", "Base.in"),
            ("Base = 1\nBase.in", "Base.in"),
        ] {
            assert!(completions_at(source, cursor, &lib).is_empty(), "{source}");
        }
        // The new let binding is not visible in its own initializer.
        let source = "let Base = Base.ind\n    Base.in\nend";
        assert_eq!(
            labels(&completions_at(source, "Base.ind", &lib)),
            vec!["indexed_member"]
        );
        let source = "function f(Base)\n    Base.in\nend\nBase.ind";
        let names = labels(&completions_at(source, "Base.ind", &lib));
        assert_eq!(names, vec!["indexed_member"]);
    }

    #[test]
    fn member_context_uses_julia_identifier_continuations() {
        for (alias, member) in [("Tool′", "membre′"), ("Da\u{301}g", "me\u{301}lange")] {
            let mut indexed = module("Library", &[]);
            indexed.functions.push(func(member));
            let lib = library(vec![package(indexed)]);
            for suffix in ["", member] {
                let site = format!("{alias}.{suffix}");
                let source = format!("import Library as {alias}\n{site}");
                assert_eq!(
                    labels(&completions_at(&source, &site, &lib)),
                    [member],
                    "{source}"
                );
            }
            let site = format!("{alias}.{member}");
            let source = format!("import Library as {alias}\nlet {alias} = 1\n    {site}\nend");
            assert!(completions_at(&source, &site, &lib).is_empty(), "{source}");
        }
    }

    #[test]
    fn member_context_follows_the_resolved_import_alias() {
        let mut lib_module = module("Library", &[]);
        lib_module.functions.push(func("correct_member"));
        let mut alias_module = module("Alias", &[]);
        alias_module.functions.push(func("unrelated_member"));
        let lib = library(vec![package(lib_module), package(alias_module)]);
        let source = "import Library as Alias\nAlias.";
        let names = labels(&completions_at(source, "Alias.", &lib));
        assert_eq!(names, vec!["correct_member"]);
    }

    #[test]
    fn member_context_lists_defined_names_and_submodules() {
        let mut root = module("A", &[]);
        root.functions.push(func("foo"));
        root.types.push(TypeDef {
            name: "Bar".into(),
            kind: TypeKind::Struct { mutable: false },
            type_params: Vec::new(),
            supertype: None,
            fields: Vec::new(),
            doc: None,
            loc: loc(),
        });
        root.consts.push(ConstDef {
            name: "BAUD".into(),
            value_repr: Some("9600".into()),
            doc: None,
            loc: loc(),
        });
        root.submodules.push(module("Inner", &[]));
        let lib = library(vec![package(root)]);
        let items = completions_at("A.", "A.", &lib);
        let names = labels(&items);
        for expected in ["foo", "Bar", "BAUD", "Inner"] {
            assert!(names.contains(&expected.to_string()), "missing {expected}");
        }
        let bar = items.iter().find(|i| i.label == "Bar").unwrap();
        assert_eq!(bar.kind, Some(CompletionItemKind::CLASS));
        let inner = items.iter().find(|i| i.label == "Inner").unwrap();
        assert_eq!(inner.kind, Some(CompletionItemKind::MODULE));
    }

    #[test]
    fn member_context_preserves_declarations_with_constructors() {
        for definitions in [
            concat!(
                "for op in (:Animal, :Alias, :greet)\n",
                "    @eval ($op)(x::Int) = x\n",
                "end\n",
            ),
            "Animal(x::Int) = x\nAlias(x::Int) = x\ngreet(x::Int) = x\n",
        ] {
            let parsed = parse(&format!(
                "abstract type Animal end\nconst Alias = Vector{{Int}}\n{definitions}"
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut creatures = crate::index::harvest_tree(&parsed.cst);
            assert_eq!(creatures.functions.len(), 3);
            creatures.name = "Creatures".into();
            let lib = library(vec![package(creatures)]);

            let items = completions_at("Creatures.", "Creatures.", &lib);
            let mut members: Vec<_> = items
                .iter()
                .map(|item| (item.label.as_str(), item.kind))
                .collect();
            members.sort_by_key(|&(name, _)| name);
            assert_eq!(
                members,
                vec![
                    ("Alias", Some(CompletionItemKind::CONSTANT)),
                    ("Animal", Some(CompletionItemKind::CLASS)),
                    ("greet", Some(CompletionItemKind::FUNCTION)),
                ],
                "{definitions}",
            );
        }
    }

    #[test]
    fn member_context_walks_a_submodule_chain() {
        let mut inner = module("B", &[]);
        inner.functions.push(func("deep"));
        let mut root = module("A", &[]);
        root.submodules.push(inner);
        let lib = library(vec![package(root)]);
        let names = labels(&completions_at("A.B.", "A.B.", &lib));
        assert_eq!(names, vec!["deep".to_string()]);
    }

    #[test]
    fn macro_member_context_offers_only_macros() {
        let mut root = module("Dagger", &[]);
        root.functions.push(func("plain"));
        root.macros.push(MacroDef {
            name: "@spawn".into(),
            params: Vec::new(),
            doc: None,
            loc: loc(),
        });
        let lib = library(vec![package(root)]);
        for (src, needle, end) in [
            ("λ = Dagger.@", "Dagger.@", 12),
            ("λ = Dagger.@sp", "Dagger.@sp", 14),
            ("λ = Dagger.@spaw(x)", "Dagger.@sp", 16),
        ] {
            let items = completions_at(src, needle, &lib);
            assert_eq!(labels(&items), ["@spawn"], "{src}");
            let spawn = &items[0];
            assert_eq!(spawn.filter_text.as_deref(), Some("spawn"), "{src}");
            let (new_text, range) = edit(spawn);
            assert_eq!(new_text, "spawn", "{src}");
            assert_eq!(range.start, Position::new(0, 12), "{src}");
            assert_eq!(range.end, Position::new(0, end), "{src}");
            assert_eq!(spawn.data.as_ref().unwrap()["name"], "@spawn", "{src}");
        }
        assert_eq!(
            labels(&completions_at("Dagger.", "Dagger.", &lib)),
            ["plain"]
        );
        let shadow = "function f(Dagger)\n    Dagger.@sp\nend";
        assert!(completions_at(shadow, "Dagger.@sp", &lib).is_empty());
    }

    #[test]
    fn unknown_receiver_yields_no_members() {
        let lib = library(vec![package(module("A", &[]))]);
        assert!(completions_at("Nope.", "Nope.", &lib).is_empty());
    }

    #[test]
    fn resolve_preserves_type_metadata_with_generated_constructors() {
        let parsed = parse(concat!(
            "export Animal\n",
            "\"An animal.\"\n",
            "abstract type Animal end\n",
            "for op in (:Animal,)\n",
            "    @eval ($op)(x::Int) = x\n",
            "end\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut creatures = crate::index::harvest_tree(&parsed.cst);
        creatures.name = "Creatures".into();
        let pkg = package(creatures);
        let item = CompletionItem {
            label: "Animal".into(),
            data: resolve_data(&["Creatures".into()], "Animal"),
            ..Default::default()
        };
        let resolved =
            resolve_completion_with(&|name| (name == "Creatures").then(|| pkg.clone()), item);
        assert_eq!(resolved.detail.as_deref(), Some("abstract type Animal"));
        match resolved.documentation {
            Some(Documentation::MarkupContent(m)) => assert_eq!(m.value, "An animal."),
            other => panic!("expected type documentation, got {other:?}"),
        }
    }

    #[test]
    fn resolve_preserves_alias_metadata_with_generated_constructors() {
        let parsed = parse(concat!(
            "export Alias\n",
            "\"An integer vector.\"\n",
            "const Alias = Vector{Int}\n",
            "for op in (:Alias,)\n",
            "    @eval ($op)(x::Int) = x\n",
            "end\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut aliases = crate::index::harvest_tree(&parsed.cst);
        assert_eq!(aliases.functions.len(), 1);
        aliases.name = "Aliases".into();
        let pkg = package(aliases);
        let item = CompletionItem {
            label: "Alias".into(),
            data: resolve_data(&["Aliases".into()], "Alias"),
            ..Default::default()
        };
        let resolved =
            resolve_completion_with(&|name| (name == "Aliases").then(|| pkg.clone()), item);
        assert_eq!(resolved.detail.as_deref(), Some("Alias = Vector{Int}"));
        match resolved.documentation {
            Some(Documentation::MarkupContent(m)) => assert_eq!(m.value, "An integer vector."),
            other => panic!("expected alias documentation, got {other:?}"),
        }
    }

    #[test]
    fn resolve_fills_docs_and_signature() {
        let mut root = module("A", &[]);
        let mut group = func("foo");
        group.doc = Some(crate::index::Docstring {
            text: "does a foo".into(),
            loc: loc(),
        });
        group.methods.push(Method {
            params: vec![Param {
                name: Some("x".into()),
                type_annotation: Some(TypeExpr::Name {
                    path: vec!["Int".into()],
                }),
                default: None,
                is_vararg: false,
                is_opaque: false,
            }],
            keyword_params: Vec::new(),
            type_args: Vec::new(),
            where_clauses: Vec::new(),
            return_type: None,
            has_body: true,
            is_generated: false,
            doc: None,
            loc: loc(),
        });
        root.functions.push(group);
        let pkg = package(root);
        let item = CompletionItem {
            label: "foo".into(),
            data: resolve_data(&["A".into()], "foo"),
            ..Default::default()
        };
        let resolved = resolve_completion_with(&|name| (name == "A").then(|| pkg.clone()), item);
        assert_eq!(resolved.detail.as_deref(), Some("foo(x::Int)"));
        match resolved.documentation {
            Some(Documentation::MarkupContent(m)) => assert_eq!(m.value, "does a foo"),
            other => panic!("expected markdown docs, got {other:?}"),
        }
    }

    // --- LaTeX and emoji sequences -----------------------------------------

    /// The generated tables and the backward scanner have to agree: every key
    /// must be reachable by a scan, and both tables must be sorted for
    /// [`prefixed`]. Regenerating on a Julia bump re-checks this.
    #[test]
    fn tables_fit_the_scanner() {
        for table in [LATEX_SYMBOLS, EMOJI_SYMBOLS] {
            assert!(!table.is_empty());
            for window in table.windows(2) {
                assert!(window[0].0 < window[1].0, "unsorted at {:?}", window[0].0);
            }
            for &(key, expansion) in table {
                let rest = key
                    .strip_prefix('\\')
                    .unwrap_or_else(|| panic!("{key:?} lacks a backslash"));
                assert!(!rest.is_empty(), "{key:?} is a bare backslash");
                assert!(
                    rest.chars().all(is_sequence_char),
                    "{key:?} has a character the scanner stops at"
                );
                assert!(
                    key.len() <= MAX_SEQUENCE_LEN,
                    "{key:?} outruns the scan cap"
                );
                assert!(!expansion.is_empty(), "{key:?} expands to nothing");
            }
        }
    }

    #[test]
    fn latex_sequence_offers_expansions_and_replaces_the_backslash() {
        let items = completions_bare("x = \\alph", "\\alph");
        let alpha = item(&items, "\\alpha");
        assert_eq!(alpha.detail.as_deref(), Some("α"));
        assert_eq!(alpha.kind, Some(CompletionItemKind::TEXT));
        let (new_text, range) = edit(alpha);
        assert_eq!(new_text, "α");
        // The edit swallows the backslash, so accepting leaves `x = α`.
        assert_eq!(range.start.character, 4);
        assert_eq!(range.end.character, 9);
        // Only the matching prefix is offered.
        assert!(!labels(&items).contains(&"\\beta".to_string()));
    }

    /// The REPL way to type `x₁` puts the backslash straight after an operand,
    /// which is also how left division (`A\b`) is written. The subscript wins:
    /// a completion only inserts when accepted, and this is the common case.
    #[test]
    fn sequence_directly_after_an_identifier_is_offered() {
        let items = completions_bare("x\\_1", "\\_1");
        let (new_text, range) = edit(item(&items, "\\_1"));
        assert_eq!(new_text, "₁");
        // The edit starts at the backslash, leaving the `x` alone.
        assert_eq!(range.start.character, 1);
    }

    #[test]
    fn emoji_sequences_are_offered() {
        let items = completions_bare("\\:smi", "\\:smi");
        assert_eq!(edit(item(&items, "\\:smile:")).0, "😄");
    }

    /// `REPL.REPLCompletions.completions` answers a bare `\` with the LaTeX
    /// table alone and only reaches the emoji once the `:` is typed. Matching
    /// that keeps the first list the muscle-memory one.
    #[test]
    fn a_bare_backslash_offers_latex_only() {
        let names = labels(&completions_bare("\\", "\\"));
        assert!(names.contains(&"\\alpha".to_string()));
        assert!(!names.contains(&"\\:smile:".to_string()));
        assert_eq!(names.len(), LATEX_SYMBOLS.len());
    }

    #[test]
    fn a_colon_opens_the_emoji_table() {
        let names = labels(&completions_bare("\\:", "\\:"));
        assert_eq!(names.len(), EMOJI_SYMBOLS.len());
        assert!(names.contains(&"\\:smile:".to_string()));
    }

    /// In `r"\d"` or `raw"\n"` the backslash is the string's own, so a popup of
    /// `\delta`/`\nabla` over every regex would be pure noise.
    #[test]
    fn verbatim_strings_offer_nothing() {
        for src in [
            "m = r\"\\d",
            "p = raw\"\\n",
            "c = `ls \\d",
            "m = match(r\"\\s", // still unterminated, mid-typing
        ] {
            let needle = &src[src.len() - 2..];
            assert!(
                completions_bare(src, needle).is_empty(),
                "expected nothing in {src:?}"
            );
        }
    }

    /// A plain string and a docstring are prose, where `α` is exactly what the
    /// author wants; only the string macros are verbatim.
    #[test]
    fn plain_strings_and_docstrings_still_offer_sequences() {
        for src in ["s = \"\\alph", "\"\"\"\n\\alph"] {
            let names = labels(&completions_bare(src, "\\alph"));
            assert!(
                names.contains(&"\\alpha".to_string()),
                "expected sequences in {src:?}, got {names:?}"
            );
        }
    }

    /// In a plain string `\n` is a newline, so a one-character escape run stays
    /// quiet; the second character resolves the ambiguity and the sequences
    /// come back. In code there is no escape to collide with.
    #[test]
    fn a_lone_escape_stays_quiet_only_inside_a_plain_string() {
        assert!(completions_bare("s = \"\\n", "\\n").is_empty());
        assert!(completions_bare("s = \"\\u", "\\u").is_empty());
        // One more character and `\nu` is offered again.
        let names = labels(&completions_bare("s = \"\\nu", "\\nu"));
        assert!(names.contains(&"\\nu".to_string()), "{names:?}");
        // A non-escape character is never ambiguous, even at one character.
        assert!(!completions_bare("s = \"\\^", "\\^").is_empty());
        // The same run in code is not an escape at all.
        assert!(!completions_bare("x = \\n", "\\n").is_empty());
    }

    #[test]
    fn lone_escape_recognition() {
        for escape in ["n", "t", "u", "x", "0", "\\", "\""] {
            assert!(is_lone_escape(escape), "{escape:?} is an escape");
        }
        for other in ["^", "_", ":", "alpha", "nu", "", "nn"] {
            assert!(!is_lone_escape(other), "{other:?} is not a lone escape");
        }
    }

    /// Candidate sets taken from `REPL.REPLCompletions.completions` on Julia
    /// 1.12, so the two agree on what a partial sequence offers.
    #[test]
    fn candidate_counts_match_the_repl() {
        for (typed, expected) in [
            ("\\alph", 1),
            ("\\:smi", 9),
            ("\\:smile", 4),
            ("\\:smile:", 1),
            ("\\:+1:", 1),
        ] {
            let src = format!("x = {typed}");
            let items = completions_bare(&src, typed);
            assert_eq!(
                items.len(),
                expected,
                "{typed:?} offered {:?}",
                labels(&items)
            );
        }
    }

    #[test]
    fn an_unknown_sequence_offers_nothing() {
        assert!(completions_bare("\\notasymbol", "\\notasymbol").is_empty());
    }

    #[test]
    fn prefix_search_takes_exactly_the_matching_run() {
        let table: &[(&str, &str)] = &[("\\a", "1"), ("\\ab", "2"), ("\\abc", "3"), ("\\b", "4")];
        assert_eq!(prefixed(table, "\\ab").len(), 2);
        assert_eq!(prefixed(table, "\\").len(), 4);
        assert_eq!(prefixed(table, "\\abcd").len(), 0);
        assert_eq!(prefixed(table, "\\z").len(), 0);
    }

    #[test]
    fn codepoints_names_combining_expansions() {
        assert_eq!(codepoints("α"), "U+03B1");
        // `\nleqslant` is a base character plus a combining solidus.
        assert_eq!(codepoints("⩽̸"), "U+2A7D U+0338");
    }

    #[test]
    fn context_detection() {
        assert_eq!(context_at("foo", 3), Context::Value);
        assert_eq!(context_at("\\alph", 5), Context::Latex { start: 0 });
        assert_eq!(context_at("x = \\_1", 7), Context::Latex { start: 4 });
        assert_eq!(context_at("\\", 1), Context::Latex { start: 0 });
        // A spaced left division is not a sequence: the scan stops at the space.
        assert_eq!(context_at("A \\ b", 5), Context::Value);
        // Nor is a run longer than the longest key.
        let long = format!("\\{}", "a".repeat(MAX_SEQUENCE_LEN));
        assert_eq!(context_at(&long, long.len()), Context::Value);
        assert_eq!(context_at("@ti", 3), Context::Macro);
        assert_eq!(
            context_at("Base.", 5),
            Context::Member {
                receiver: vec!["Base".into()],
                macro_member: false,
            }
        );
        assert_eq!(
            context_at("A.B.foo", 7),
            Context::Member {
                receiver: vec!["A".into(), "B".into()],
                macro_member: false,
            }
        );
        assert_eq!(
            context_at("Base.@ti", 8),
            Context::Member {
                receiver: vec!["Base".into()],
                macro_member: true,
            }
        );
    }
}
