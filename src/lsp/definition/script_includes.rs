//! Definition fallback for free reads in scripts connected by a literal
//! top-level include. Do not give a loose file package/workspace membership:
//! these are location hints, not a contract for lint or rewrite operations.

use std::collections::{BTreeMap, HashSet};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use lsp_types::Location;
use rowan::TextSize;

use crate::ast::{AstNode, AstToken, CallExpr, Expr};
use crate::incremental::{Analysis, normalize_path};
use crate::parse_context::{EditionSource, SourceRole};
use crate::parser::parse_with_options;
use crate::project::{include_literal, literal_path, resolve_target};
use crate::resolve::ModulePath;
use crate::semantic::{Access, BindingKind, SemanticModel};
use crate::syntax::{SyntaxKind, SyntaxNode};
use crate::text::{LineIndex, PositionEncoding};

const MAX_FILES: usize = 64;
const MAX_FILE_BYTES: usize = 2 * 1024 * 1024;
const MAX_TOTAL_BYTES: usize = 8 * 1024 * 1024;

#[derive(Hash, PartialEq, Eq)]
struct Member {
    path: PathBuf,
    host: ModulePath,
}

pub(super) fn locations(
    snapshot: &Analysis,
    path: &Path,
    text: &str,
    offset: TextSize,
    encoding: PositionEncoding,
    open: &super::OpenDefinitionBuffers,
) -> Vec<Location> {
    // Package members already have dependency-aware include indexes. Keep
    // ordinary scripts and entry points separate from that resolution.
    if !julia_file(path) || text.len() > MAX_FILE_BYTES || snapshot.workspace_member(path).is_some()
    {
        return Vec::new();
    }
    let path = normalize_path(path);
    let root = snapshot
        .context()
        .filter(|context| {
            matches!(
                context.source,
                EditionSource::Project {
                    role: SourceRole::Script,
                    ..
                } | EditionSource::Fixed(_)
            )
        })
        .map_or_else(|| path.clone(), |context| normalize_path(&context.entry));
    // The common undefined-name case needs no traversal or filesystem access.
    if root == path && !crate::project::may_contain_static_include(text) {
        return Vec::new();
    }
    let options = snapshot.options_for_path(&path);
    let caller = parse_with_options(text, options).cst;
    let caller_model = SemanticModel::build(&caller);
    let Some(ident) = caller_model.ident_at(offset) else {
        return Vec::new();
    };
    if ident.binding.is_some()
        || ident.is_macro
        || ident.access != Access::Read
        || caller_model
            .qualified_reads()
            .iter()
            .any(|read| read.range.contains_range(ident.range))
    {
        return Vec::new();
    }
    let local_host = caller_model.enclosing_module_path(ident.scope);
    let mut pending = vec![(
        Member {
            path: root,
            host: Vec::new(),
        },
        Vec::new(),
    )];
    let mut seen = HashSet::new();
    let mut visited_hosts = BTreeMap::new();
    let mut candidates = Vec::new();
    let mut bytes = 0usize;

    while let Some((member, prefix)) = pending.pop() {
        if !seen.insert((member.path.clone(), member.host.clone())) {
            continue;
        }
        if seen.len() > MAX_FILES {
            return Vec::new();
        }
        let source = if member.path == path {
            Arc::from(text)
        } else if let Some(buffer) = open.get(&member.path) {
            buffer.text_arc()
        } else {
            match bounded_source(snapshot, &member.path) {
                Ok(Some(source)) => source,
                Ok(None) => continue,
                Err(()) => return Vec::new(),
            }
        };
        bytes += source.len();
        if source.len() > MAX_FILE_BYTES || bytes > MAX_TOTAL_BYTES {
            return Vec::new();
        }
        let (cst, model);
        let (tree, model) = if member.path == path {
            let mut use_order = prefix.clone();
            use_order.push(ident.range.start());
            visited_hosts.insert(join(&member.host, &local_host), use_order);
            (&caller, &caller_model)
        } else {
            cst = parse_with_options(&source, options).cst;
            model = SemanticModel::build(&cst);
            (&cst, &model)
        };
        for binding in model.bindings() {
            if member.path != path
                && binding.kind == BindingKind::Function
                && binding.name == ident.name
                && model.scope(binding.scope).kind.is_global()
            {
                let host = join(&member.host, &model.enclosing_module_path(binding.scope));
                let mut order = prefix.clone();
                order.push(binding.def_range.start());
                candidates.push((
                    host,
                    member.path.clone(),
                    binding.def_range,
                    Arc::clone(&source),
                    order,
                ));
            }
        }
        if let Some(parent) = member.path.parent() {
            for (target, host, offset) in static_includes(tree, model, parent, &member.host)
                .into_iter()
                .rev()
            {
                if pending.len() >= MAX_FILES {
                    return Vec::new();
                }
                let mut order = prefix.clone();
                order.push(offset);
                pending.push((Member { path: target, host }, order));
            }
        }
    }

    // A file can be included into more than one module. Do not choose one
    // host arbitrarily when the current load graph cannot disambiguate it.
    let Some((host, use_order)) =
        (visited_hosts.len() == 1).then(|| visited_hosts.first_key_value().unwrap())
    else {
        return Vec::new();
    };
    candidates.sort_by(|a, b| (&a.1, a.2.start(), a.2.end()).cmp(&(&b.1, b.2.start(), b.2.end())));
    candidates.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1 && a.2 == b.2);
    let execution_is_immediate = caller_model.scope(ident.scope).kind.is_global();
    candidates
        .into_iter()
        .filter(|(module, _, _, _, order)| {
            module == host && (!execution_is_immediate || order < use_order)
        })
        .filter_map(|(_, path, range, source, _)| {
            let uri = super::from_path(&path)?;
            Some(Location {
                uri,
                range: super::to_range(range, &LineIndex::new(&source), encoding),
            })
        })
        .collect()
}

fn julia_file(path: &Path) -> bool {
    path.extension()
        .is_some_and(|extension| extension.eq_ignore_ascii_case("jl"))
}

// Treat exceeding the budget differently from an unavailable file; never
// return a partial graph because a large file happened to be visited last.
fn bounded_source(snapshot: &Analysis, path: &Path) -> Result<Option<Arc<str>>, ()> {
    if let Some(file) = snapshot.lookup_file(path) {
        return Ok(Some(snapshot.file_text_arc(file)));
    }
    if !path.is_file() {
        return Ok(None);
    }
    let Ok(file) = std::fs::File::open(path) else {
        return Ok(None);
    };
    let mut bytes = Vec::new();
    if file
        .take((MAX_FILE_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .is_err()
    {
        return Ok(None);
    }
    if bytes.len() > MAX_FILE_BYTES {
        return Err(());
    }
    Ok(String::from_utf8(bytes).ok().map(Arc::from))
}

fn join(host: &[smol_str::SmolStr], suffix: &[smol_str::SmolStr]) -> ModulePath {
    host.iter().chain(suffix).cloned().collect()
}

fn static_includes(
    root: &SyntaxNode,
    model: &SemanticModel,
    parent: &Path,
    host: &[smol_str::SmolStr],
) -> Vec<(PathBuf, ModulePath, TextSize)> {
    root.descendants()
        .filter_map(CallExpr::cast)
        .filter_map(|call| {
            let literal = include_literal(&call)?;
            if !call
                .syntax()
                .ancestors()
                .skip(1)
                .all(|ancestor| match ancestor.kind() {
                    SyntaxKind::ROOT | SyntaxKind::BLOCK | SyntaxKind::BEGIN_EXPR => true,
                    SyntaxKind::MODULE_DEF => !ancestor
                        .first_token()
                        .is_some_and(|token| token.text() == "baremodule"),
                    _ => false,
                })
            {
                return None;
            }
            let Expr::Name(name) = call.callee()? else {
                return None;
            };
            let ident = model.ident_at(name.ident()?.syntax().text_range().start())?;
            // A lexical/global binding named include may be a different function.
            if ident.binding.is_some() {
                return None;
            }
            let target = normalize_path(&resolve_target(&literal_path(&literal)?, Some(parent))?);
            julia_file(&target).then(|| {
                (
                    target,
                    join(host, &model.enclosing_module_path(ident.scope)),
                    call.syntax().text_range().start(),
                )
            })
        })
        .collect()
}
