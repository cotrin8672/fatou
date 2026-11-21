//! Julia source files and folders for a confirmed `include("literal")`.
//! The edit stays inside one source path component; relative lookup follows the
//! including document, not the process or workspace directory.
use std::path::{Component, Path};

use lsp_types::{CompletionItem, CompletionItemKind, CompletionTextEdit, Range, TextEdit};
use rowan::{TextSize, TokenAtOffset};
use smol_str::SmolStr;

use crate::ast::{AstNode, AstToken, CallExpr, Expr, HasArgList, ModuleDef, StringLiteral};
use crate::incremental::Analysis;
use crate::parse_context::{EditionSource, SourceRole};
use crate::resolve::{Namespace, Resolution, Resolver, resolve_submodule};
use crate::semantic::{BindingKind, SemanticModel};
use crate::syntax::{SyntaxKind, SyntaxNode};
use crate::text::{PositionEncoding, TextBuffer};

pub(super) struct IncludePath {
    callee: Loader,
    content_start: usize,
    content_end: usize,
    unterminated: bool,
}

enum Loader {
    Include { offset: TextSize, in_module: bool },
    Includet(TextSize),
    QualifiedIncludet(SmolStr, TextSize),
}

pub(super) fn context_at(root: &SyntaxNode, offset: TextSize) -> Option<IncludePath> {
    let (left, right) = match root.token_at_offset(offset) {
        TokenAtOffset::None => return None,
        TokenAtOffset::Single(token) => (Some(token), None),
        TokenAtOffset::Between(left, right) => (Some(left), Some(right)),
    };
    left.into_iter().chain(right).find_map(|token| {
        let literal = StringLiteral::cast(token.parent()?)?;
        let call = literal
            .syntax()
            .ancestors()
            .skip(1)
            .find_map(CallExpr::cast)?;
        let callee = loader_at(&call, &literal)?;
        let mut tokens = literal
            .syntax()
            .children_with_tokens()
            .filter_map(|part| part.into_token());
        let open = tokens.next()?;
        if open.kind() != SyntaxKind::STRING_DELIM_OPEN || open.text() != "\"" {
            return None;
        }
        let start = open.text_range().end();
        let close = tokens.find(|token| token.kind() == SyntaxKind::STRING_DELIM_CLOSE);
        let end = close.as_ref().map_or_else(
            || literal.syntax().text_range().end(),
            |token| token.text_range().start(),
        );
        if offset < start || offset > end {
            return None;
        }
        Some(IncludePath {
            callee,
            content_start: start.into(),
            content_end: end.into(),
            unterminated: close.is_none(),
        })
    })
}

fn loader_at(call: &CallExpr, literal: &StringLiteral) -> Option<Loader> {
    if let Some(ident) = call.callee_ident()
        && ident.text() == "include"
    {
        // Reuse the static-include shape checked by the project graph.
        if crate::project::include_literal(call)?.syntax() != literal.syntax() {
            return None;
        }
        // Julia injects the include wrapper into regular module bodies.
        let module = call.syntax().ancestors().find_map(ModuleDef::cast);
        if module.as_ref().is_some_and(|module| {
            module
                .syntax()
                .first_token()
                .is_some_and(|token| token.text() == "baremodule")
        }) {
            return None;
        }
        return Some(Loader::Include {
            offset: ident.syntax().text_range().start(),
            in_module: module.is_some(),
        });
    }

    if literal.prefix().is_some() || literal.interpolations().next().is_some() {
        return None;
    }
    let args = call.arg_list()?;
    let mut args = args.args();
    let Expr::StringLiteral(argument) = args.next()?.expr()? else {
        return None;
    };
    if argument.syntax() != literal.syntax() || args.next().is_some() {
        return None;
    }
    if let Some(ident) = call
        .callee_ident()
        .filter(|ident| ident.text() == "includet")
    {
        return Some(Loader::Includet(ident.syntax().text_range().start()));
    }
    let Expr::BinaryExpr(dot) = call.callee()? else {
        return None;
    };
    if dot.op()?.syntax().kind() != SyntaxKind::DOT || dot.rhs()?.name_ident()?.text() != "includet"
    {
        return None;
    }
    let receiver = dot.lhs()?.name_ident()?;
    Some(Loader::QualifiedIncludet(
        SmolStr::new(receiver.text()),
        receiver.syntax().text_range().start(),
    ))
}

fn resolves_loader(
    loader: Loader,
    resolver: &Resolver<'_, Analysis>,
    model: &SemanticModel,
) -> bool {
    let value = Namespace::Value;
    if let Loader::Include { offset, .. } = loader {
        // Julia injects include(p) = Base.include(Mod, p) in an ordinary
        // module (and supplies Main.include); it is not an exported Base
        // name. The known Julia prelude applies only if no masking binding
        // was found and baremodule was ruled out.
        return match resolver.resolve("include", offset, value) {
            Resolution::Unresolved => true,
            Resolution::System { module, .. } => module == "Base",
            _ => false,
        };
    }
    // No package-free fallback for Revise: the indexed module must have
    // includet and the receiver or imported binding must match it.
    let owner = SmolStr::new("Revise");
    let name = SmolStr::new("includet");
    if resolver.qualified_name_exists(&[owner.clone(), name.clone()], value) != Some(true) {
        return false;
    }
    match loader {
        Loader::Includet(offset) => match resolver.resolve(&name, offset, value) {
            Resolution::Using { module, .. } => module == owner,
            Resolution::Binding(id) => {
                let binding = model.binding(id);
                binding.kind == BindingKind::Import
                    && model.module_loads().iter().any(|load| {
                        load.scope == binding.scope
                            && load.range.contains_range(binding.def_range)
                            && load.path.leading_dots == 0
                            && load.path.components.as_slice() == [owner.clone()]
                            && load.items.as_ref().is_some_and(|items| {
                                items.iter().any(|item| {
                                    item.range.contains_range(binding.def_range)
                                        && item.name == name
                                        && item.alias.as_ref().unwrap_or(&item.name) == &name
                                })
                            })
                    })
            }
            _ => false,
        },
        Loader::QualifiedIncludet(receiver, offset) => {
            !matches!(
                resolver.resolve(&receiver, offset, value),
                Resolution::Unresolved
                    | Resolution::Workspace { .. }
                    | Resolution::WorkspaceImport { .. }
            ) && resolver
                .module_receiver_path(&[receiver], offset, Some(offset))
                .as_deref()
                == Some(&[owner])
        }
        Loader::Include { .. } => unreachable!(),
    }
}

pub(super) fn complete(
    context: IncludePath,
    snapshot: &Analysis,
    model: &SemanticModel,
    path: &Path,
    text: &TextBuffer,
    offset: TextSize,
    encoding: PositionEncoding,
) -> Option<Vec<CompletionItem>> {
    if !path.is_absolute() || super::super::uri::is_synthetic(path) {
        return None;
    }
    let workspace = snapshot.workspace_member(path);
    if matches!(
        context.callee,
        Loader::Include {
            in_module: false,
            ..
        }
    ) && workspace.as_ref().is_some_and(|(package, host)| {
        let host: Vec<_> = host.iter().map(SmolStr::as_str).collect();
        resolve_submodule(&package.root, &host).is_some_and(|module| module.bare)
    }) {
        return None;
    }
    let scripts = snapshot
        .context()
        .filter(|context| {
            matches!(
                context.source,
                EditionSource::Project {
                    role: SourceRole::Script,
                    ..
                }
            )
        })
        .map(|context| snapshot.scripts(std::slice::from_ref(&context.entry)));
    let contexts = scripts
        .as_ref()
        .map(|analysis| analysis.contexts(path))
        .unwrap_or_default();
    let resolver = Resolver::new(model, snapshot).with_workspace(workspace);
    let resolver = if contexts.is_empty() {
        resolver
    } else {
        resolver.with_scripts(contexts)
    };
    if !resolves_loader(context.callee, &resolver, model) {
        return None;
    }
    let raw = text.get(context.content_start..context.content_end)?;
    // An unmatched ordinary quote can consume all subsequent source lines
    // as string content during editing. Do not replace any of those lines.
    let raw = if context.unterminated {
        raw.split(['\r', '\n']).next().unwrap_or_default()
    } else {
        raw
    };
    let cursor = usize::from(offset).checked_sub(context.content_start)?;
    let items = complete_literal(raw, cursor, path.parent()?, |byte| {
        text.line_index()
            .byte_to_position(context.content_start + byte, encoding)
    });
    // Once this is a confirmed static literal, never send unrelated Julia
    // names on I/O failure or an invalid/incomplete path escape.
    Some(items.unwrap_or_default())
}

fn complete_literal(
    raw: &str,
    cursor: usize,
    base: &Path,
    position: impl Fn(usize) -> lsp_types::Position,
) -> Option<Vec<CompletionItem>> {
    if raw.contains(['\r', '\n']) {
        return None;
    }
    let before = raw.get(..cursor)?;
    let after = raw.get(cursor..)?;
    let start = before.rfind('/').map_or(0, |i| i + 1);
    let following_slash = after.find('/');
    let end = cursor + following_slash.unwrap_or(after.len());
    let dir = crate::parser::string_value(&raw[..start]).ok()?;
    let prefix = crate::parser::string_value(&raw[start..cursor]).ok()?;
    // Only document-relative paths; do not look up absolute paths, volumes,
    // UNC hosts, or escaped separators that cannot map to this source edit.
    if dir.starts_with(['/', '\\'])
        || dir.get(..2).is_some_and(|s| s.ends_with(':'))
        || dir.contains('\\')
        || Path::new(&dir)
            .components()
            .any(|c| matches!(c, Component::RootDir | Component::Prefix(_)))
        || prefix.contains('/')
        || (cfg!(windows) && prefix.contains('\\'))
    {
        return None;
    }
    let range = Range::new(position(start), position(end));
    let mut items = Vec::new();
    // One explicitly named directory only: no project scan, globbing or
    // recursion. Unreadable and non-UTF-8 entries can't be represented.
    for entry in std::fs::read_dir(base.join(dir)).ok()?.flatten() {
        let Some(label) = entry.file_name().into_string().ok() else {
            continue;
        };
        if (label.starts_with('.') && !prefix.starts_with('.'))
            || !label.starts_with(&prefix)
            || label.contains(char::is_control)
        {
            continue;
        }
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        let directory = kind.is_dir();
        // Julia can evaluate files with other suffixes when named explicitly.
        // But this picker is for source files, not Project.toml or data files.
        let julia_source = Path::new(&label)
            .extension()
            .and_then(|ext| ext.to_str())
            .is_some_and(|ext| ext.eq_ignore_ascii_case("jl"));
        if !directory && (!kind.is_file() || !julia_source || following_slash.is_some()) {
            continue;
        }
        let escaped = escape_component(&label);
        let mut new_text = escaped.clone();
        if directory && following_slash.is_none() {
            new_text.push('/');
        }
        items.push(CompletionItem {
            label,
            kind: Some(if directory {
                CompletionItemKind::FOLDER
            } else {
                CompletionItemKind::FILE
            }),
            filter_text: Some(escaped),
            text_edit: Some(CompletionTextEdit::Edit(TextEdit { range, new_text })),
            ..CompletionItem::default()
        });
    }
    items.sort_unstable_by(|a, b| a.label.cmp(&b.label));
    Some(items)
}

fn escape_component(name: &str) -> String {
    let mut escaped = String::with_capacity(name.len());
    for ch in name.chars() {
        if matches!(ch, '\\' | '"' | '$') {
            escaped.push('\\');
        }
        escaped.push(ch);
    }
    escaped
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use lsp_types::Position;

    fn context(marked: &str) -> bool {
        let (left, right) = marked.split_once('|').unwrap();
        let tree = parse(&format!("{left}{right}")).cst;
        context_at(&tree, TextSize::new(left.len() as u32)).is_some()
    }

    #[test]
    fn narrow_static_path_cst_context() {
        for source in [
            "include(\"|\")",
            "include(\"./mo|.jl\")",
            "include(\"par|",
            "includet(\"|\")",
            "Revise.includet(\"|\")",
            "module A\ninclude(\"pa|\")\nend",
        ] {
            assert!(context(source), "{source}");
        }
        for source in [
            "# include(\"x|\")",
            "chores(\"|\")",
            "Base.include(Me, \"|\")",
            "include(map, \"|\")",
            "include(raw\"|\")",
            "include(\"$(part|)\")",
            "include(\"\"\"x|\"\"\")",
            "baremodule A\ninclude(\"x|\")\nend",
        ] {
            assert!(!context(source), "{source}");
        }
    }

    #[test]
    fn filesystem_edit_only_replaces_current_path_component() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::create_dir(dir.path().join("sibling")).unwrap();
        std::fs::create_dir(dir.path().join("suffix")).unwrap();
        std::fs::create_dir(dir.path().join("sub")).unwrap();
        std::fs::write(dir.path().join("solver.jl"), "").unwrap();
        std::fs::write(dir.path().join("solver.data"), "").unwrap();
        std::fs::write(dir.path().join("main.jl"), "").unwrap();
        std::fs::write(dir.path().join("main.toml"), "").unwrap();
        std::fs::write(dir.path().join("Project.toml"), "").unwrap();
        std::fs::create_dir(dir.path().join("main_parts")).unwrap();
        std::fs::write(dir.path().join("with$dollar.jl"), "").unwrap();
        std::fs::write(dir.path().join(".hidden.jl"), "").unwrap();
        std::fs::write(dir.path().join("sub/model.jl"), "").unwrap();
        let items = |raw: &str, cursor| {
            complete_literal(raw, cursor, dir.path(), |byte| {
                Position::new(0, byte as u32)
            })
            .unwrap()
        };
        let labels =
            |items: &[CompletionItem]| items.iter().map(|i| i.label.clone()).collect::<Vec<_>>();
        assert_eq!(labels(&items("sol", 3)), ["solver.jl"]);
        assert_eq!(labels(&items("main", 4)), ["main.jl", "main_parts"]);
        assert!(
            !labels(&items("", 0))
                .iter()
                .any(|name| name.ends_with(".toml") || name == ".hidden.jl")
        );
        assert_eq!(labels(&items(".h", 2)), [".hidden.jl"]);
        assert_eq!(labels(&items("./sub/mo", 8)), ["model.jl"]);
        assert_eq!(labels(&items("suF/tail.jl", 2)), ["sub", "suffix"]);
        let first = &items("suF/tail.jl", 2)[0];
        assert_eq!(first.kind, Some(CompletionItemKind::FOLDER));
        assert_eq!(
            first.text_edit,
            Some(CompletionTextEdit::Edit(TextEdit::new(
                Range::new(Position::new(0, 0), Position::new(0, 3)),
                "sub".into(),
            )))
        );
        let first = &items("with", 4)[0];
        assert_eq!(first.kind, Some(CompletionItemKind::FILE));
        assert_eq!(
            first.text_edit,
            Some(CompletionTextEdit::Edit(TextEdit::new(
                Range::new(Position::new(0, 0), Position::new(0, 4)),
                "with\\$dollar.jl".into(),
            )))
        );
    }
}
