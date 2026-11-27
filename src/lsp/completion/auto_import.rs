//! Focused auto-imports for a Julia file whose one explicit module is itself
//! the scope owner. Its imports cannot change bindings in the caller.

use super::{
    Context, auto_import_site, context_at, member_item, safe_auto_import_file,
    simple_auto_import_symbol, simple_import_name, take_ident_back,
};
use crate::incremental::{Analysis, SourceFile, normalize_path};
use crate::index::{PackageIndex, Visibility};
use crate::parse_context::EditionSource;
use crate::resolve::{ModulePath, Namespace, Resolution, Resolver};
use crate::semantic::{Access, SemanticModel};
use crate::syntax::{SyntaxKind, SyntaxNode};
use crate::text::{PositionEncoding, TextBuffer};
use lsp_types::{CompletionItem, CompletionItemKind, CompletionTextEdit, Range, TextEdit};
use rowan::{TextRange, TextSize};
use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;

#[allow(clippy::too_many_arguments)]
pub(super) fn isolated_module(
    snapshot: &Analysis,
    file: SourceFile,
    path: &Path,
    model: &SemanticModel,
    root: &SyntaxNode,
    workspace: Option<&(Arc<PackageIndex>, ModulePath)>,
    text: &TextBuffer,
    offset: TextSize,
    encoding: PositionEncoding,
    items: &mut Vec<CompletionItem>,
) {
    let n = usize::from(offset);
    let Some((prefix, _)) = text.get(..n).map(take_ident_back) else {
        return;
    };
    if prefix.len() < 2 || !simple_auto_import_symbol(prefix) {
        return;
    }
    let context = context_at(text, n);
    let at = TextSize::new((n - prefix.len()) as u32);
    let (receiver, replacement, reference) = match context {
        Context::Value => {
            let Some((_, range)) = auto_import_site(model, root, text, offset) else {
                return;
            };
            (None, range, range)
        }
        Context::Member {
            receiver,
            macro_member: false,
        } => {
            let [dep] = receiver.as_slice() else { return };
            let Some(token) = super::token_at(root, at) else {
                return;
            };
            if token.parent_ancestors().any(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::QUOTE_EXPR
                        | SyntaxKind::QUOTE_SYM
                        | SyntaxKind::MACRO_CALL
                        | SyntaxKind::MACRO_DEF
                        | SyntaxKind::DOC
                        | SyntaxKind::INTERPOLATION
                        | SyntaxKind::TYPE_ANNOTATION
                        | SyntaxKind::IMPORT_STMT
                        | SyntaxKind::USING_STMT
                        | SyntaxKind::SIGNATURE
                        | SyntaxKind::STRUCT_DEF
                        | SyntaxKind::ERROR
                )
            }) || !simple_import_name(dep)
            {
                return;
            }
            let Some(read) = model.qualified_reads().iter().find(|read| {
                read.path.len() == 2
                    && read.path[0] == dep.as_str()
                    && read.range.start() < at
                    && offset <= read.range.end()
                    && read.path[1].starts_with(prefix)
                    && !read.is_macro
            }) else {
                return;
            };
            if usize::from(read.range.end()) != usize::from(at) + read.path[1].len() {
                return;
            }
            (
                Some(dep.clone()),
                TextRange::new(at, read.range.end()),
                read.range,
            )
        }
        _ => return,
    };

    // Only a single, normal fresh module with no evaluated includes or
    // unknown top-level macros. Keep the existing include-closure algorithm
    // for package entries and sibling files.
    let mut children = root.children();
    let Some(module) = children.next() else {
        return;
    };
    let module_path = model.enclosing_module_path(model.scope_at(offset));
    if module.kind() != SyntaxKind::MODULE_DEF
        || children.next().is_some()
        || !module
            .children_with_tokens()
            .any(|e| e.kind() == SyntaxKind::MODULE_KW)
        || module_path.len() != 1
        || !model.module_loads().is_empty()
        || !model.exports().is_empty()
        || model.idents().iter().any(|id| id.name == "include")
        || !safe_auto_import_file(root, model)
        || !snapshot.parse_diagnostics(file).is_empty()
        || !matches!(snapshot.source_editions(file).as_slice(), [(context, selection)]
            if selection.certain && context.entry == normalize_path(path))
        || workspace.is_some_and(|(package, host)| {
            !host.is_empty()
                || module_path
                    .first()
                    .is_some_and(|name| name.as_str() == package.name.as_str())
        })
    {
        return;
    }
    let Some((anchor, separator)) = anchor(&module, text) else {
        return;
    };
    if TextSize::new(anchor as u32) >= replacement.start() {
        return;
    }
    let project = snapshot
        .context()
        .and_then(|c| match &c.source {
            EditionSource::Project { path, .. } => Some(path.clone()),
            _ => None,
        })
        .or_else(|| {
            let parent = path.parent()?;
            crate::environment::discover_project(&crate::environment::EnvContext::from_process(
                parent.to_path_buf(),
            ))
        });
    let Some(project) = project else { return };
    let project = normalize_path(&project);
    let source = normalize_path(path);
    if !project
        .parent()
        .is_some_and(|parent| source.starts_with(parent))
    {
        return;
    }
    let Some(project_input) = snapshot.lookup_file(&project) else {
        return;
    };
    let Some(details) = crate::environment::parse_project_str(snapshot.file_text_of(project_input))
    else {
        return;
    };
    let resolver = Resolver::new(model, snapshot);
    let unbound = |name: &str| {
        resolver.resolve(name, offset, Namespace::Value) == Resolution::Unresolved
            && !model.bindings().iter().any(|b| b.name == name)
            && !model.free_reads().any(|r| {
                r.name == name && r.access != Access::Write && !reference.contains_range(r.range)
            })
    };
    let mut offers = BTreeMap::<String, Option<_>>::new();
    for (dep, uuid) in details.deps {
        let dep = dep.into_inner();
        if !simple_import_name(&dep)
            || receiver.as_ref().is_some_and(|head| head != &dep)
            || (receiver.is_some() && !unbound(&dep))
        {
            continue;
        }
        let Ok(uuid) = uuid.into_inner().parse() else {
            continue;
        };
        let Some(index) = snapshot.auto_import_package(&project, &dep, uuid) else {
            continue;
        };
        if !index.diagnostics.is_empty() || index.root.name != dep {
            continue;
        }
        let root = &index.root;
        for (name, kind) in root
            .types
            .iter()
            .map(|name| (&name.name, CompletionItemKind::CLASS))
            .chain(
                root.functions
                    .iter()
                    .filter(|f| f.owner.is_none())
                    .map(|f| (&f.name, CompletionItemKind::FUNCTION)),
            )
        {
            if !name.starts_with(prefix) || !simple_auto_import_symbol(name) {
                continue;
            }
            if receiver.is_none()
                && (!unbound(name)
                    || !root.exports.iter().any(|export| {
                        export.name == *name && export.visibility == Visibility::Exported
                    }))
            {
                continue;
            }
            offers
                .entry(name.clone())
                .and_modify(|offer| {
                    if offer.as_ref().is_some_and(|(owner, _)| owner != &dep) {
                        *offer = None;
                    }
                })
                .or_insert_with(|| Some((dep.clone(), kind)));
        }
    }
    let line = text.line_index();
    let at = line.byte_to_position(anchor, encoding);
    let range = crate::lsp::documentation::lsp_range(replacement, &line, encoding);
    for (name, (dep, kind)) in offers.into_iter().filter_map(|(n, v)| Some((n, v?))) {
        // Replace the existing same-name qualified item rather than show a
        // second non-working option with no import edit.
        if receiver.is_some() {
            items.retain(|item| item.label != name);
        } else if items.iter().any(|item| item.label == name) {
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
            range: Range::new(at, at),
            new_text: if receiver.is_some() {
                format!("import {dep}{separator}")
            } else {
                format!("using {dep}: {name}{separator}")
            },
        }]);
        items.push(item);
    }
}

/// Keep the edit before the first expression and inside the explicit module.
fn anchor<'a>(module: &SyntaxNode, text: &'a str) -> Option<(usize, &'a str)> {
    let body = module
        .children()
        .find(|child| child.kind() == SyntaxKind::BLOCK)?;
    for child in body.children_with_tokens() {
        let range = child.text_range();
        match child.kind() {
            SyntaxKind::WHITESPACE | SyntaxKind::COMMENT | SyntaxKind::BLOCK_COMMENT => {}
            SyntaxKind::NEWLINE => {
                let eol = if text
                    .get(usize::from(range.start())..usize::from(range.end()))?
                    .ends_with("\r\n")
                {
                    "\r\n"
                } else {
                    "\n"
                };
                return Some((usize::from(range.end()), eol));
            }
            SyntaxKind::SEMICOLON => return Some((usize::from(range.end()), ";")),
            _ => return None,
        }
    }
    None
}
