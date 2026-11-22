//! Completion for Julia's load directives, kept separate from value resolution.
//!
//! The CST identifies the statement and its separators. Only the unfinished
//! path component is scanned, because the parser can leave its final dot or
//! an empty clause outside IMPORT_PATH during error recovery.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Arc;

use lsp_types::{CompletionItem, CompletionItemKind, CompletionTextEdit, Range, TextEdit};
use rowan::TextSize;

use crate::environment::{EnvContext, discover_project, parse_project_str};
use crate::incremental::Analysis;
use crate::index::PackageIndex;
use crate::parse_context::EditionSource;
use crate::parser::{is_ident_continue, is_ident_start};
use crate::resolve::{ModulePath, PackageSource, resolve_submodule};
use crate::semantic::{BindingKind, ScopeId, SemanticModel};
use crate::syntax::{SyntaxKind, SyntaxNode};
use crate::text::{LineIndex, PositionEncoding};

#[derive(Debug)]
struct PathParts<'a> {
    dots: usize,
    components: Vec<&'a str>,
}

#[derive(Debug)]
pub(super) struct ImportContext<'a> {
    /// Everything before the currently edited component.
    parent: PathParts<'a>,
    symbols: bool,
    alias_destination: bool,
    prefix: &'a str,
    start: usize,
    end: usize,
}

fn atom(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(is_ident_start) && chars.all(is_ident_continue)
}

/// Leading relative dots may be separated by whitespace; named components
/// require adjacent dots. Quoted and interpolated paths are not guessed.
fn path_parts(text: &str) -> Option<PathParts<'_>> {
    let mut text = text.trim_start();
    let mut dots = 0;
    while let Some(rest) = text.strip_prefix('.') {
        dots += 1;
        text = rest.trim_start();
    }
    let components = if text.is_empty() {
        Vec::new()
    } else {
        text.split('.').collect::<Vec<_>>()
    };
    components
        .iter()
        .all(|name| atom(name))
        .then_some(PathParts { dots, components })
}

pub(super) fn context_at<'a>(
    root: &SyntaxNode,
    text: &'a str,
    offset: TextSize,
) -> Option<ImportContext<'a>> {
    let tokens = root.token_at_offset(offset);
    let token = tokens
        .clone()
        .left_biased()
        .or_else(|| tokens.right_biased())?;
    if matches!(
        token.kind(),
        SyntaxKind::COMMENT | SyntaxKind::BLOCK_COMMENT
    ) {
        return None;
    }
    use crate::lsp::symbols::is_trivia;

    // After a dangling keyword/separator, recovery may leave the subsequent
    // newline and indentation outside the statement. A trailing complete path
    // is still rejected by the component checks below.
    let mut anchor = token.clone();
    let stmt = loop {
        if let Some(stmt) = anchor
            .parent_ancestors()
            .take_while(|node| node.kind() != SyntaxKind::INTERPOLATION)
            .find(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::USING_STMT | SyntaxKind::IMPORT_STMT
                )
            })
        {
            break stmt;
        }
        if !is_trivia(anchor.kind()) {
            return None;
        }
        anchor = anchor.prev_token()?;
    };
    // An ordinary RHS alias declares a new name; it is not a reference.
    // The parser owns both the contextual keyword and the destination token,
    // so an unrelated `as` expression or a cursor after the clause cannot
    // suppress ordinary completion.
    let alias_destination = anchor
        .parent_ancestors()
        .take_while(|node| node != &stmt)
        .find(|node| node.kind() == SyntaxKind::IMPORT_ALIAS)
        .is_some_and(|alias| {
            let mut tokens = alias.children_with_tokens().filter_map(|e| e.into_token());
            let Some(keyword) = tokens.find(|token| token.text() == "as") else {
                return false;
            };
            let Some(destination) = tokens.find(|token| !is_trivia(token.kind())) else {
                return false;
            };
            destination.kind() == SyntaxKind::IDENT
                && keyword.text_range().end() <= offset
                && offset <= destination.text_range().end()
        });
    // A missing destination cannot form IMPORT_ALIAS. The parser keeps
    // its `as` as a direct recovery token in the original statement, after
    // the parsed IMPORT_PATH. Accept only that unfinished same-line tail.
    let dangling_alias = || {
        if offset > stmt.text_range().end() {
            return false;
        }
        let mut previous = None;
        let mut last = None;
        for element in stmt.children_with_tokens().filter(|element| {
            element
                .as_token()
                .is_none_or(|token| !is_trivia(token.kind()))
        }) {
            previous = last.replace(element);
        }
        let Some(keyword) = last.and_then(|element| element.into_token()) else {
            return false;
        };
        keyword.kind() == SyntaxKind::IDENT
            && keyword.text() == "as"
            && keyword.text_range().end() <= offset
            && previous.is_some_and(|element| element.kind() == SyntaxKind::IMPORT_PATH)
            && text[usize::from(keyword.text_range().end())..usize::from(offset)]
                .chars()
                .all(|c| matches!(c, ' ' | '\t'))
    };
    if alias_destination || dangling_alias() {
        return Some(ImportContext {
            parent: path_parts("")?,
            symbols: false,
            alias_destination: true,
            prefix: "",
            start: offset.into(),
            end: offset.into(),
        });
    }
    let mut clause_start = stmt.text_range().start();
    let mut base_end = None;
    let mut first_start = clause_start;
    let mut had_comma = false;
    let mut leading = true;
    for element in stmt.children_with_tokens() {
        if element.text_range().end() > offset {
            break;
        }
        let Some(token) = element.into_token() else {
            leading = false;
            continue;
        };
        match token.kind() {
            SyntaxKind::USING_KW | SyntaxKind::IMPORT_KW => {
                clause_start = token.text_range().end();
                first_start = clause_start;
            }
            SyntaxKind::COLON if base_end.is_none() && !had_comma => {
                base_end = Some(token.text_range().start());
                clause_start = token.text_range().end();
                leading = true;
            }
            SyntaxKind::COMMA => {
                clause_start = token.text_range().end();
                had_comma = true;
                leading = true;
            }
            kind if leading && is_trivia(kind) => {
                clause_start = token.text_range().end();
                if base_end.is_none() && !had_comma {
                    first_start = clause_start;
                }
            }
            _ => leading = false,
        }
    }
    let cursor = usize::from(offset);
    let clause_start = usize::from(clause_start);
    if cursor == clause_start
        && matches!(token.kind(), SyntaxKind::USING_KW | SyntaxKind::IMPORT_KW)
    {
        // `using│` itself is not a name slot; wait for the separator.
        return None;
    }
    let typed = text.get(clause_start..cursor)?;
    let prefix_start = typed
        .char_indices()
        .rev()
        .take_while(|(_, c)| is_ident_continue(*c))
        .last()
        .map_or(typed.len(), |(i, _)| i);
    let prefix_start = if typed[..prefix_start].ends_with('@') {
        prefix_start - 1
    } else {
        prefix_start
    };
    let prefix = &typed[prefix_start..];
    let start = clause_start + prefix_start;
    let prefix_head = typed[..prefix_start].trim_start();
    let (parent, symbols) = if let Some(base_end) = base_end {
        if !prefix_head.is_empty() {
            return None;
        }
        (
            path_parts(
                text.get(usize::from(first_start)..usize::from(base_end))?
                    .trim(),
            )?,
            true,
        )
    } else {
        // At a trailing dot the next (possibly empty) token is a new path
        // component. Plain whitespace after a completed path isn't one.
        let parent = if prefix_head.is_empty() {
            path_parts("")?
        } else {
            let (before, suffix) = prefix_head.rsplit_once('.')?;
            if !suffix.is_empty() {
                return None;
            }
            if before.trim().chars().all(|c| c == '.' || c.is_whitespace()) {
                path_parts(prefix_head)?
            } else {
                path_parts(before)?
            }
        };
        if prefix.starts_with('@') && stmt.kind() == SyntaxKind::USING_STMT {
            return None;
        }
        let symbols = stmt.kind() == SyntaxKind::IMPORT_STMT && !parent.components.is_empty();
        (parent, symbols)
    };
    // A selective import can be completed at the start of an existing
    // macro token, too. Include that token's `@` and name in the edit and
    // offer only macros, rather than inserting a second token before it.
    let existing_macro = symbols && prefix.is_empty() && text[cursor..].starts_with('@');
    let suffix_start = cursor + usize::from(existing_macro);
    let end = text[suffix_start..]
        .char_indices()
        .take_while(|(_, c)| is_ident_continue(*c))
        .last()
        .map_or(suffix_start, |(i, c)| suffix_start + i + c.len_utf8());
    let prefix = if existing_macro { "@" } else { prefix };
    Some(ImportContext {
        parent,
        symbols,
        alias_destination: false,
        prefix,
        start,
        end,
    })
}

/// Reuse the loader's selected Project.toml and the tracked, potentially
/// unsaved buffer. A declared dependency need not be installed or indexed.
pub(super) fn project_names(snapshot: &Analysis, path: &Path) -> BTreeSet<String> {
    let project = snapshot
        .context()
        .and_then(|context| match &context.source {
            EditionSource::Project { path, .. } => Some(path.clone()),
            _ => None,
        })
        .or_else(|| {
            snapshot.workspace_member(path).and_then(|(pkg, _)| {
                snapshot
                    .project_file_of(&pkg.name)
                    .and_then(|file| snapshot.file_path_of(file))
            })
        })
        .or_else(|| {
            let parent = path.parent().unwrap_or(path);
            discover_project(&EnvContext::from_process(parent.to_path_buf()))
        });
    let Some(project) = project else {
        return BTreeSet::new();
    };
    let parsed = if let Some(file) = snapshot.lookup_file(&project) {
        parse_project_str(snapshot.file_text_of(file))
    } else {
        std::fs::read_to_string(project)
            .ok()
            .and_then(|text| parse_project_str(&text))
    };
    names_from_project(parsed)
}

/// During Salsa cancellation no tracked inputs can safely be read. Follow an
/// already chosen project context, or discover the enclosing project directly.
pub(super) fn disk_project_names(snapshot: &Analysis, path: &Path) -> BTreeSet<String> {
    let selected = snapshot
        .context()
        .and_then(|context| match &context.source {
            EditionSource::Project { path, .. } => Some(path.clone()),
            _ => None,
        });
    let project = selected.or_else(|| {
        let parent = path.parent().unwrap_or(path);
        discover_project(&EnvContext::from_process(parent.to_path_buf()))
    });
    names_from_project(project.and_then(|project| {
        std::fs::read_to_string(project)
            .ok()
            .and_then(|text| parse_project_str(&text))
    }))
}

fn names_from_project(project: Option<crate::environment::ProjectFile>) -> BTreeSet<String> {
    project.map_or_else(BTreeSet::new, |project| {
        let mut names = project.declared_dep_names();
        names.extend(project.name.map(|name| name.into_inner()));
        names
    })
}

impl ImportContext<'_> {
    pub(super) fn alias_destination(&self) -> bool {
        self.alias_destination
    }

    pub(super) fn package_root(&self) -> bool {
        self.parent.dots == 0 && self.parent.components.is_empty() && !self.symbols
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn complete<P: PackageSource>(
        &self,
        model: Option<&SemanticModel>,
        packages: &P,
        workspace: Option<&(Arc<PackageIndex>, ModulePath)>,
        project_names: BTreeSet<String>,
        offset: TextSize,
        index: &LineIndex,
        encoding: PositionEncoding,
    ) -> Vec<CompletionItem> {
        if self.alias_destination {
            return Vec::new();
        }
        let module_item = |label: &str| CompletionItem {
            label: label.to_string(),
            kind: Some(CompletionItemKind::MODULE),
            ..Default::default()
        };
        let mode = self.parent.components.as_slice();
        let mut items = if self.package_root() {
            let mut names = project_names;
            names.extend(["Base".into(), "Core".into(), "Main".into()]);
            names.extend(workspace.map(|(pkg, _)| pkg.name.clone()));
            names.iter().map(|name| module_item(name)).collect()
        } else if self.parent.dots > 0 || mode.first() == Some(&"Main") {
            // Only relative and Main paths can refer to file-local names.
            let Some(model) = model else {
                return Vec::new();
            };
            let source_scope = model.scope_at(offset);
            let lexical_path = model.enclosing_module_path(source_scope);
            let host: Vec<&str> = workspace
                .into_iter()
                .flat_map(|(_, host)| host.iter().map(|s| s.as_str()))
                .collect();
            let outer_package = workspace
                .filter(|(_, host)| host.is_empty())
                .map(|(pkg, _)| pkg.name.as_str());
            let lexical_has_root = lexical_path
                .first()
                .is_some_and(|name| Some(name.as_str()) == outer_package);
            let mut target: Vec<&str> = host
                .iter()
                .copied()
                .chain(
                    lexical_path[usize::from(lexical_has_root)..]
                        .iter()
                        .map(|s| s.as_str()),
                )
                .collect();
            if self.parent.dots == 0 {
                target = mode[1..].to_vec();
            } else {
                let Some(depth) = target.len().checked_sub(self.parent.dots - 1) else {
                    return Vec::new();
                };
                target.truncate(depth);
                target.extend(mode.iter().copied());
            }

            let mut candidates = Vec::new();
            if let Some((pkg, _)) = workspace
                && self.parent.dots != 0
                && let Some(module) = resolve_submodule(&pkg.root, &target)
            {
                let indexed_path = std::iter::once(pkg.name.clone())
                    .chain(target.iter().map(|name| (*name).to_string()))
                    .collect::<Vec<_>>();
                candidates.extend(indexed_items(module, &indexed_path, self.symbols));
            }
            let local = if self.parent.dots == 0 && workspace.is_none() {
                Some(target.as_slice())
            } else {
                target.strip_prefix(host.as_slice())
            };
            if let Some(local) = local {
                for (i, scope) in model
                    .scopes()
                    .iter()
                    .enumerate()
                    .filter(|(_, s)| s.kind.is_global())
                {
                    let path = model.enclosing_module_path(ScopeId(i as u32));
                    let skip = usize::from(
                        lexical_has_root
                            && path
                                .first()
                                .is_some_and(|name| Some(name.as_str()) == outer_package),
                    );
                    if (lexical_has_root && skip == 0)
                        || !path[skip..]
                            .iter()
                            .map(|s| s.as_str())
                            .eq(local.iter().copied())
                    {
                        continue;
                    }
                    for id in &scope.bindings {
                        let b = model.binding(*id);
                        if self.symbols || b.kind == BindingKind::Module {
                            let is_macro = b.kind == BindingKind::Macro;
                            candidates.push(CompletionItem {
                                label: if is_macro {
                                    format!("@{}", b.name)
                                } else {
                                    b.name.to_string()
                                },
                                kind: Some(super::binding_kind(b.kind)),
                                ..Default::default()
                            });
                        }
                    }
                }
            }
            candidates
        } else {
            let Some((head, tail)) = mode.split_first() else {
                return Vec::new();
            };
            let pkg = workspace
                .map(|(p, _)| p)
                .filter(|pkg| pkg.name == *head)
                .cloned()
                .or_else(|| packages.package(head));
            let Some(pkg) = pkg else { return Vec::new() };
            let Some(module) = resolve_submodule(&pkg.root, tail) else {
                return Vec::new();
            };
            let path = mode
                .iter()
                .map(|name| (*name).to_string())
                .collect::<Vec<_>>();
            indexed_items(module, &path, self.symbols)
        };
        let folded = self.prefix.to_lowercase();
        let range = Range::new(
            index.byte_to_position(self.start, encoding),
            index.byte_to_position(self.end, encoding),
        );
        let mut seen = BTreeSet::new();
        items.retain_mut(|item| {
            if !item.label.to_lowercase().starts_with(&folded) || !seen.insert(item.label.clone()) {
                return false;
            }
            item.text_edit = Some(CompletionTextEdit::Edit(TextEdit {
                range,
                new_text: item.label.clone(),
            }));
            true
        });
        items
    }
}

fn indexed_items(
    module: &crate::index::ModuleIndex,
    path: &[String],
    symbols: bool,
) -> Vec<CompletionItem> {
    if symbols {
        let mut items = super::member_items(module, path, false);
        items.extend(super::member_items(module, path, true));
        items.extend(module.imported_names.iter().map(|name| CompletionItem {
            label: name.clone(),
            ..Default::default()
        }));
        items
    } else {
        module
            .submodules
            .iter()
            .map(|sub| super::member_item(&sub.name, CompletionItemKind::MODULE, path))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::incremental::IncrementalDatabase;
    use crate::parser::parse;

    fn marked(source: &str) -> (String, TextSize) {
        let offset = source.find('│').unwrap();
        (source.replacen('│', "", 1), TextSize::new(offset as u32))
    }

    fn candidates(source: &str) -> Option<Vec<CompletionItem>> {
        let (source, offset) = marked(source);
        let root = parse(&source).cst;
        let model = SemanticModel::build(&root);
        let packages = std::collections::BTreeMap::new();
        let context = context_at(&root, &source, offset)?;
        Some(context.complete(
            (!context.package_root()).then_some(&model),
            &packages,
            None,
            ["FFTW".into(), "Plots".into()].into(),
            offset,
            &LineIndex::new(&source),
            PositionEncoding::Utf16,
        ))
    }

    #[test]
    fn module_name_slot_uses_dependencies_only_on_real_imports() {
        for source in [
            "local_name = 1\nusing │",
            "using Plots, │",
            "import │",
            "using Plots,\n FF│TW",
            "using Plots, \n    │FFTW",
            "import # note\n FF│TW",
        ] {
            let names = candidates(source)
                .unwrap_or_else(|| panic!("{source:?}"))
                .into_iter()
                .map(|item| item.label)
                .collect::<Vec<_>>();
            assert!(names.iter().any(|n| n == "FFTW"), "{source:?}: {names:?}");
            assert!(
                !names.iter().any(|n| n == "local_name"),
                "{source:?}: {names:?}"
            );
        }
        for source in [
            "using│",
            "# using │",
            "\"using │\"",
            "using FFTW\n│",
            "using FFTW; │",
            "using FFTW │",
            "using FFTW, # using │",
            "using FFTW, \n α = 1; β│",
        ] {
            assert!(candidates(source).is_none(), "{source:?}");
        }
    }

    #[test]
    fn ordinary_alias_destination_is_handled_without_candidates() {
        for source in [
            "outer_name = 1\nimport Base as ou│",
            "import Base as │",
            "import Base as │outer_name",
            "import Base as outer_│name",
            "using .LocalTool: bell as ou│",
            "using .LocalTool: bell as │",
            "import Base, Core as ca│",
            "import Base as 木│",
        ] {
            assert_eq!(candidates(source), Some(Vec::new()), "{source}");
        }
        for source in [
            "import B│ase as outer_name",
            "import Base as outer_name, Plo│ts",
            "using .LocalTool: be│ll as outer_name",
        ] {
            let (text, at) = marked(source);
            let context = context_at(&parse(&text).cst, &text, at).unwrap();
            assert!(!context.alias_destination(), "{source}");
        }
        for source in [
            "import Base as outer_name\nouter│",
            "import Base as outer_name; outer│",
            "as = outer│",
            "import Base: @time as @ou│",
        ] {
            let (text, at) = marked(source);
            assert!(
                !context_at(&parse(&text).cst, &text, at)
                    .is_some_and(|context| context.alias_destination()),
                "{source}"
            );
        }
    }

    #[test]
    fn root_edit_replaces_the_full_identifier_using_utf16() {
        let items = candidates("a = \"😀\"; using FF│incorrect, Plots").unwrap();
        let item = items.into_iter().find(|item| item.label == "FFTW").unwrap();
        assert_eq!(
            item.text_edit,
            Some(CompletionTextEdit::Edit(TextEdit {
                range: Range::new(
                    lsp_types::Position::new(0, 16),
                    lsp_types::Position::new(0, 27)
                ),
                new_text: "FFTW".into(),
            }))
        );
    }

    #[test]
    fn selective_import_replaces_macro_from_either_side_of_at_sign() {
        let preamble = "module Fixture\nanswer = 1\nmacro shiny(x) end\nend\n";
        for (source, start, end) in [
            ("using .Fixture: │@shWrong", 16, 24),
            ("using .Fixture: @sh│Wrong", 16, 24),
            ("import .Fixture: │@shWrong", 17, 25),
            ("import .Fixture.│@shWrong", 16, 24),
            ("using .Fixture: │@", 16, 17),
        ] {
            let items = candidates(&format!("{preamble}{source}")).unwrap();
            assert_eq!(items.len(), 1, "{source}: {items:?}");
            assert_eq!(items[0].label, "@shiny");
            assert_eq!(
                items[0].text_edit,
                Some(CompletionTextEdit::Edit(TextEdit {
                    range: Range::new(
                        lsp_types::Position::new(4, start),
                        lsp_types::Position::new(4, end)
                    ),
                    new_text: "@shiny".into(),
                })),
                "{source}"
            );
        }
    }

    #[test]
    fn relative_module_paths_and_selected_names_are_separate() {
        let src = "module Outer\n module Utils\n answer = 1\n macro action() end\n end\n";
        let names = |body: &str| {
            candidates(&format!("{src}{body}"))
                .unwrap_or_else(|| panic!("{body:?}"))
                .into_iter()
                .map(|item| item.label)
                .collect::<Vec<_>>()
        };
        assert_eq!(names("using .Ut│"), ["Utils"]);
        assert_eq!(names("module Child\nusing ..U│"), ["Utils"]);
        assert_eq!(names("using .Utils: ans│"), ["answer"]);
        assert_eq!(names("using .Utils: answer, @ac│"), ["@action"]);
        assert_eq!(names("using .Utils.an│"), Vec::<String>::new());
        assert_eq!(names("import .Utils.an│"), ["answer"]);
        assert_eq!(
            candidates(&format!("{src}using .Utils: ans as al│")).unwrap(),
            []
        );
    }

    #[test]
    fn tracked_unnamed_project_supplies_uninstalled_dependencies() {
        let dir = tempfile::tempdir().unwrap();
        let project = dir.path().join("Project.toml");
        let file = dir.path().join("script.jl");
        std::fs::write(
            &project,
            "[deps]\nOnDisk = \"00000000-0000-0000-0000-000000000001\"\n",
        )
        .unwrap();
        let mut db = IncrementalDatabase::default();
        db.upsert_file(&file, "using ");
        db.upsert_file(
            &project,
            "[deps]\nUninstalled = \"00000000-0000-0000-0000-000000000002\"\n",
        );
        let names = project_names(&db.snapshot(), &file);
        assert!(names.contains("Uninstalled"), "{names:?}");
        assert!(!names.contains("OnDisk"), "{names:?}");
    }
}
