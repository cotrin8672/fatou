//! The one name-resolution/masking order every consumer shares.
//!
//! Completion, hover, and the future undefined-name lint must all agree on how
//! a bare identifier resolves. Julia layers four tiers, innermost wins:
//!
//! 1. **local scopes** — a binding reachable up the scope chain (a local,
//!    parameter, loop/`let` variable, or a file/module global);
//! 2. **explicit imports** — `import X`, `import X: a`, `using X: a`, which are
//!    themselves file bindings (kind [`BindingKind::Import`]), so tiers 1 and 2
//!    are together exactly "does the name bind in this file?" — already answered
//!    by the [`SemanticModel`];
//! 3. **`using`'d exports** — the `export`ed names of a whole-module `using X`,
//!    with ambiguity reported when multiple imports provably expose different bindings;
//! 4. **Base/Core implicit** — the names every (non-bare) module gets for free.
//!
//! [`Resolver::resolve`] walks the tiers and returns the first hit;
//! [`Resolver::visible`] enumerates every visible name in the same order with
//! shadowed names dropped, for completion. Both read one [`SemanticModel`] and a
//! [`PackageSource`] (the harvested library), so the order lives in one place.
//!
//! Macros resolve in a parallel namespace ([`Namespace::Macro`]): `@time` never
//! resolves to a value `time`, matching the model's split.
//!
//! Deferred: relative (`using ..A`) and interpolated `using`s do not resolve
//! against the library (their target module is unknown here), and `baremodule`
//! bodies are still granted the implicit Base/Core tier — the model does not yet
//! distinguish `baremodule` from `module`.

use std::collections::BTreeMap;
use std::collections::HashSet;
use std::sync::Arc;

use rowan::TextSize;
use smol_str::SmolStr;

use crate::index::{ModuleIndex, ModuleUsing, PackageIndex, Visibility};
use crate::semantic::{
    Access, Binding, BindingId, BindingKind, LoadKind, ScopeId, ScopeKind, SemanticModel,
};

/// The namespace a name is resolved in. Julia keeps macros separate: `@time`
/// and a value `time` never resolve to one another. `Ord` so it can key the
/// reverse-occurrence index's per-name buckets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Namespace {
    Value,
    Macro,
}

/// A module path relative to a package's root module (empty = the root module
/// itself), naming the chain of enclosing nested `module`s. Threads through the
/// workspace-resolution tier and the reverse-occurrence index so a symbol in a
/// nested `module` resolves against that module rather than the root, and two
/// same-named symbols in different modules never conflate.
pub type ModulePath = Vec<SmolStr>;

type UsingProvider = (SmolStr, Arc<ModuleIndexHandle>);

/// The key of a workspace symbol in the reverse-occurrence index: the dev
/// package it belongs to, the module it lives in, its namespace, and its
/// bare-or-`@` name. The module path keeps same-named symbols in different
/// (nested) modules from conflating; the package name does the same across
/// workspace folders, whose reverse indexes share one map.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OccurrenceKey {
    /// The dev package the symbol belongs to ([`PackageIndex::name`]).
    pub package: SmolStr,
    pub module: ModulePath,
    pub namespace: Namespace,
    pub name: SmolStr,
}

/// Whether any whole-module `using` in the file fails to resolve against
/// `packages`: a relative or interpolated path, an unharvested package, or a
/// missing submodule. Such a `using` may export anything, so no conclusion
/// about what a free name means (or what methods it carries) is sound for the
/// file. (Item lists — `using X: a` — bind their names explicitly and don't
/// gate the file.) Shared by the resolution-dependent lint rules
/// (`undefined-name`, `call-arity`).
pub fn has_unresolvable_using(
    model: &SemanticModel,
    packages: &dyn PackageSource,
    workspace: Option<&(Arc<PackageIndex>, ModulePath)>,
) -> bool {
    // This file's own whole-module `using`s.
    if model.module_loads().iter().any(|load| {
        load.kind == LoadKind::Using
            && load.items.is_none()
            && module_path_unresolvable(load.path.leading_dots, &load.path.components, packages)
    }) {
        return true;
    }
    // Sibling files' whole-module `using`s, harvested per module: a `using` in
    // any file of a module this file also lives in (its host module plus each
    // nested `module` it opens) is visible module-wide, so an unresolvable one
    // could export anything. Restricted to the file's own modules, not every
    // package submodule, to avoid bailing on unrelated submodules' relative
    // `using`s.
    let Some((pkg, host)) = workspace else {
        return false;
    };
    file_module_paths(model, host).iter().any(|path| {
        module_at(&pkg.root, path).is_some_and(|module| {
            module
                .usings
                .iter()
                .any(|u| module_path_unresolvable(u.leading_dots, &u.components, packages))
        })
    })
}

/// Whether a whole-module `using` path — `leading_dots` relative dots and the
/// dotted `components` — fails to resolve against `packages`: a relative or
/// interpolated path, an unharvested package, or a missing submodule. Shared by
/// the model-based and harvested `has_unresolvable_using` scans. `S: AsRef<str>`
/// so it accepts the model's `SmolStr` components and the index's `String`s.
pub(crate) fn module_path_unresolvable<S: AsRef<str>>(
    leading_dots: u32,
    components: &[S],
    packages: &dyn PackageSource,
) -> bool {
    if leading_dots != 0 || components.is_empty() {
        return true;
    }
    let Some(pkg) = packages.package(components[0].as_ref()) else {
        return true;
    };
    let rest: Vec<SmolStr> = components[1..].iter().map(SmolStr::new).collect();
    module_at(&pkg.root, &rest).is_none()
}

/// The distinct module paths (relative to the package root) the file's reads
/// resolve in: its host module and each nested `module` written in the file. The
/// set `has_unresolvable_using`'s harvested scan and the resolver's workspace
/// tiers agree on for this file.
fn file_module_paths(model: &SemanticModel, host: &ModulePath) -> Vec<ModulePath> {
    let mut paths = vec![host.clone()];
    for (i, scope) in model.scopes().iter().enumerate() {
        if scope.kind == ScopeKind::Module {
            let mut path = host.clone();
            path.extend(model.enclosing_module_path(ScopeId(i as u32)));
            if !paths.contains(&path) {
                paths.push(path);
            }
        }
    }
    paths
}

/// The submodule of `root` reached by following `path`, or `None` if any
/// segment is missing. An empty `path` returns `root` itself.
pub fn module_at<'m>(root: &'m ModuleIndex, path: &[SmolStr]) -> Option<&'m ModuleIndex> {
    let mut current = root;
    for segment in path {
        current = current
            .submodules
            .iter()
            .find(|m| m.name == segment.as_str())?;
    }
    Some(current)
}

/// Where a name resolved, in the shared masking order. [`Resolution::Binding`]
/// covers tiers 1 and 2 (inspect the binding's [`BindingKind`] to tell a local
/// from an import); the library tiers name the module the symbol came from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    /// A global supplied by an explicitly configured script program.
    Script { name: SmolStr },
    /// Different script contexts disagree, or multiple whole-module imports
    /// provably expose different bindings under one name.
    Ambiguous,
    /// A binding in this file: a local, parameter, global, or explicit import.
    Binding(BindingId),
    /// A top-level symbol of the enclosing workspace package's module, defined
    /// in one of its *other* files (tier 2 — the same-module globals an
    /// `include` splices in). `module` is the path (relative to the package
    /// root) of the nested `module` the symbol lives in; `name` is bare for a
    /// value, `@`-prefixed for a macro. The consumer looks `name` up in
    /// [`module_at`]`(&pkg.root, &module)`.
    Workspace { module: ModulePath, name: SmolStr },
    /// A name a module-level `using`/`import` binds in a *sibling* file of the
    /// enclosing workspace module (`import X`→`X`, `using X: a`→`a`, `… as Y`→
    /// `Y`). An `include` splices every file into one module, so the binding is
    /// module-wide. Ranks with tier 2 (an explicit module import outranks
    /// `using`/Base), but stays distinct from [`Workspace`](Self::Workspace) so
    /// references/rename do not treat it as a navigable definition — navigation
    /// to the `import` site is deferred. `name` is bare for a value,
    /// `@`-prefixed for a macro.
    WorkspaceImport { name: SmolStr },
    /// An `export`ed name brought in by a whole-module `using` (tier 3).
    /// `module` is the full path from the package root, such as `A.B.C`.
    Using { module: SmolStr, name: SmolStr },
    /// An implicitly available Base/Core name (tier 4).
    System { module: SmolStr, name: SmolStr },
    /// No tier provides the name.
    Unresolved,
}

/// One recorded occurrence of a workspace top-level symbol: its byte range, the
/// definition-vs-use flag, and how the site accesses the binding. The unit the
/// reverse-occurrence index unions across files (cross-file references/rename).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OccurrenceRec {
    pub range: rowan::TextRange,
    pub is_def: bool,
    pub access: Access,
}

/// One name visible at a position, tagged with the tier that provides it. The
/// completion counterpart of [`Resolution`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Candidate {
    /// The name as it would be typed (macros keep their `@`).
    pub name: SmolStr,
    pub source: Source,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum QualifiedMember {
    Module(ModulePath),
    Symbol {
        module: ModulePath,
        name: SmolStr,
        kind: QualifiedMemberKind,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum QualifiedMemberKind {
    Function,
    Type,
    Const,
    Macro,
}

/// The tier a [`Candidate`] came from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    Binding(BindingId),
    /// A same-module sibling top-level symbol of the workspace package.
    Workspace {
        module: SmolStr,
    },
    Using {
        module: SmolStr,
    },
    System {
        module: SmolStr,
    },
}

/// The harvested library, seen as "give me the [`PackageIndex`] named `name`".
/// Implemented for the plain harvest map and for the language server's
/// read-only [`Analysis`](crate::incremental::Analysis) snapshot.
pub trait PackageSource {
    /// Grammar of the active source view. Pure callers keep the latest edition;
    /// an Analysis snapshot supplies its immutable loading context.
    fn syntax_options(&self) -> crate::parser::ParseOptions {
        Default::default()
    }
    fn syntax_options_at(&self, _path: &std::path::Path) -> crate::parser::ParseOptions {
        self.syntax_options()
    }

    fn package(&self, name: &str) -> Option<Arc<PackageIndex>>;

    /// A trusted path already resolved through a visible module may end at a
    /// transitive provider in that same environment. Do not use this for a
    /// name written by the user before proving how it is in scope.
    fn environment_package(&self, name: &str) -> Option<Arc<PackageIndex>> {
        self.package(name)
    }

    /// Verify that the importing package may load a target in its own
    /// manifest context, even when the editor project cannot import it.
    fn dependency_package(&self, _owner: &str, name: &str) -> Option<Arc<PackageIndex>> {
        self.package(name)
    }

    /// The absolute source root of package `name` (the directory its
    /// `DefLocation` paths are relative to), if known. Only the live server,
    /// which has located the depot on disk, can answer this; the plain harvest
    /// map has no roots, so the default is `None`. Go-to-definition uses it to
    /// turn a package-relative definition location into a real file path.
    fn package_root(&self, _name: &str) -> Option<std::path::PathBuf> {
        None
    }

    /// The workspace package and the host module path of `path`, when `path` is
    /// one of the package's source files — the package whose same-module globals
    /// a file's free reads resolve against (resolution tier 2), and the nested
    /// `module` the file's top-level items splice into (empty for the root). Only
    /// the live server knows the workspace, so the default is `None`. See
    /// [`Analysis::workspace_member`](crate::incremental::Analysis::workspace_member).
    fn workspace_member(&self, _path: &std::path::Path) -> Option<(Arc<PackageIndex>, ModulePath)> {
        None
    }

    /// Just the workspace package for `path` (dropping the host module path), for
    /// consumers that navigate via a [`Resolution::Workspace`]'s own module path.
    fn workspace_module(&self, path: &std::path::Path) -> Option<Arc<PackageIndex>> {
        self.workspace_member(path).map(|(pkg, _)| pkg)
    }
}

impl PackageSource for BTreeMap<String, Arc<PackageIndex>> {
    fn package(&self, name: &str) -> Option<Arc<PackageIndex>> {
        self.get(name).cloned()
    }
}

/// Resolves names against one file's [`SemanticModel`] and a [`PackageSource`],
/// following the shared masking order. Cheap to construct; holds only borrows.
/// `P` may be unsized (`Resolver<'a, dyn PackageSource>`) for callers that
/// only have a trait object, like the linter's `undefined-name` rule.
pub struct Resolver<'a, P: PackageSource + ?Sized> {
    model: &'a SemanticModel,
    packages: &'a P,
    /// The enclosing workspace package's index, when the file being resolved is
    /// one of its source files. The file's own host module (see
    /// [`WorkspaceCtx::host`]) supplies the tier-2 same-module globals. `None`
    /// for a non-member file or a non-package workspace.
    workspace: Option<WorkspaceCtx>,
    scripts: Option<Vec<crate::project::scripts::ScriptContext<'a>>>,
}

/// The workspace context of the file being resolved: the enclosing package and
/// the file's host module path within it.
struct WorkspaceCtx {
    pkg: Arc<PackageIndex>,
    /// The host module path (relative to [`pkg`](Self::pkg)'s root, empty for the
    /// root itself) the file's top-level items splice into, derived from the
    /// include graph (`host_module_of` over `project_graph`,
    /// `src/incremental.rs`). The file's top-level globals and free reads
    /// resolve against this module.
    host: ModulePath,
    entry: bool,
}

impl<'a, P: PackageSource + ?Sized> Resolver<'a, P> {
    pub fn new(model: &'a SemanticModel, packages: &'a P) -> Self {
        Resolver {
            model,
            packages,
            workspace: None,
            scripts: None,
        }
    }

    /// Set the enclosing workspace package and the file's host module path
    /// (tier 2). Chain onto [`new`](Self::new) at a call site that knows the
    /// file's path, via [`PackageSource::workspace_member`].
    pub fn with_workspace(mut self, workspace: Option<(Arc<PackageIndex>, ModulePath)>) -> Self {
        self.workspace = workspace.map(|(pkg, host)| WorkspaceCtx {
            pkg,
            host,
            entry: false,
        });
        self
    }

    /// The package entry file's named wrapper is already represented by the
    /// index root. Identity is based on the file path, not a same-name module
    /// in an included file.
    pub(crate) fn with_workspace_at(
        self,
        workspace: Option<(Arc<PackageIndex>, ModulePath)>,
        path: Option<&std::path::Path>,
    ) -> Self {
        let is_entry = workspace
            .as_ref()
            .zip(path)
            .is_some_and(|((pkg, host), path)| {
                host.is_empty()
                    && self.packages.package_root(&pkg.name).is_some_and(|root| {
                        crate::incremental::normalize_path(path)
                            == crate::incremental::normalize_path(&root.join(&pkg.root.loc.file))
                    })
            });
        self.with_workspace(workspace)
            .with_workspace_entry(is_entry)
    }

    pub(crate) fn with_workspace_entry(mut self, entry: bool) -> Self {
        if let Some(workspace) = &mut self.workspace {
            workspace.entry = entry;
        }
        self
    }

    /// Attach independent script contexts. A common answer is required by
    /// consumers that cannot attribute findings to an individual program.
    pub fn with_scripts(
        mut self,
        scripts: Vec<crate::project::scripts::ScriptContext<'a>>,
    ) -> Self {
        self.scripts = Some(scripts);
        self
    }

    /// The full module path (relative to the package root) of a position in
    /// `scope`: the file's host module followed by the file-internal nested
    /// `module` path. This is where a top-level symbol declared, or a free read
    /// issued, at `scope` resolves against in the package's module tree.
    fn full_module_path(&self, workspace: &WorkspaceCtx, scope: ScopeId) -> ModulePath {
        let mut path = workspace.host.clone();
        let lexical = self.model.enclosing_module_path(scope);
        let wrapper = usize::from(
            workspace.entry
                && lexical
                    .first()
                    .is_some_and(|name| name == workspace.pkg.name.as_str()),
        );
        path.extend(lexical.into_iter().skip(wrapper));
        path
    }

    /// Resolve `name` (bare, without `@` even in [`Namespace::Macro`]) as read
    /// at `offset`, walking the four tiers in order.
    pub fn resolve(&self, name: &str, offset: TextSize, namespace: Namespace) -> Resolution {
        self.resolve_at_scope(name, offset, namespace, self.model.scope_at(offset))
    }

    fn resolve_at_scope(
        &self,
        name: &str,
        offset: TextSize,
        namespace: Namespace,
        scope: ScopeId,
    ) -> Resolution {
        if let Some(scripts) = &self.scripts {
            let mut answers = scripts.iter().map(|context| {
                self.resolve_with_script(name, offset, namespace, scope, Some(context))
            });
            let Some(first) = answers.next() else {
                return Resolution::Ambiguous;
            };
            return if answers.all(|answer| answer == first) {
                first
            } else {
                Resolution::Ambiguous
            };
        }
        self.resolve_with_script(name, offset, namespace, scope, None)
    }

    pub fn resolve_in_script(
        &self,
        name: &str,
        offset: TextSize,
        namespace: Namespace,
        context: &crate::project::scripts::ScriptContext<'_>,
    ) -> Resolution {
        self.resolve_with_script(
            name,
            offset,
            namespace,
            self.model.scope_at(offset),
            Some(context),
        )
    }

    fn resolve_with_script(
        &self,
        name: &str,
        offset: TextSize,
        namespace: Namespace,
        scope: ScopeId,
        script: Option<&crate::project::scripts::ScriptContext<'_>>,
    ) -> Resolution {
        let wanted = wanted_name(name, namespace);

        // Tiers 1 + 2: a binding in this file.
        if let Some(binding) = self.file_binding(&wanted, scope, namespace) {
            return Resolution::Binding(binding);
        }
        let script_module = script.and_then(|context| {
            let mut path = context.host.clone();
            path.extend(self.model.enclosing_module_path(scope));
            context.program.modules.get(&path)
        });
        if namespace == Namespace::Value
            && let Some(context) = script
        {
            let mut path = context.host.clone();
            path.extend(self.model.enclosing_module_path(scope));
            let own_name = path.last().map(SmolStr::as_str).unwrap_or("Main");
            if wanted == own_name {
                return Resolution::Script { name: wanted };
            }
        }
        if script_module.is_some_and(|module| module.bindings.contains(&wanted)) {
            return Resolution::Script { name: wanted };
        }
        // Tier 2 (cross-file): a same-module sibling top-level symbol of the
        // module enclosing this read (the file's host module plus any file-internal
        // nested `module`). Ranks above `using`/Base — an `include`-spliced module
        // global masks them, just as a same-file global would. A module also
        // binds its *own* name inside itself (`SLOPE.foo()` within module
        // `SLOPE`), which no `export`/definition records — Julia scopes only the
        // enclosing module's own name, never an ancestor's, so this matches
        // exactly `wanted == module.name`.
        if let Some(workspace) = &self.workspace
            && script.is_none()
        {
            let path = self.full_module_path(workspace, scope);
            if let Some(module) = module_at(&workspace.pkg.root, &path) {
                if self.workspace_defines(module, &wanted, offset, namespace)
                    || (namespace == Namespace::Value && module.name == wanted.as_str())
                {
                    return Resolution::Workspace {
                        module: path,
                        name: wanted,
                    };
                }
                // A name a sibling file's module-level `using`/`import` binds is
                // a module global too, ranking with the definitions above.
                if module_imports(module, &wanted) {
                    return Resolution::WorkspaceImport { name: wanted };
                }
            }
        }
        // Tier 3: a whole-module `using` opens exports without binding them
        // explicitly. Julia does not select the first of distinct bindings.
        let module = if let Some(module) = script_module {
            self.opened_export(&wanted, self.indexed_usings(&module.usings))
        } else if script.is_none() {
            self.opened_export(&wanted, self.visible_usings(scope))
        } else {
            Ok(None)
        };
        match module {
            Err(()) => return Resolution::Ambiguous,
            Ok(Some((module, _))) => {
                return Resolution::Using {
                    module,
                    name: wanted,
                };
            }
            Ok(None) => {}
        }
        // Tier 4: Base/Core implicit.
        if let Some((module, _)) = self.system_export(&wanted) {
            return Resolution::System {
                module,
                name: wanted,
            };
        }
        Resolution::Unresolved
    }

    /// Resolve the receiver of a dotted read before consulting a package
    /// index. A known value is never a package merely because its spelling
    /// matches one. For an unresolved head, keep the existing best-effort
    /// indexed-package lookup (also useful in incomplete source).
    pub(crate) fn module_receiver_path(
        &self,
        written: &[SmolStr],
        offset: TextSize,
        receiver_start: Option<TextSize>,
    ) -> Option<ModulePath> {
        self.module_receiver_path_impl(written, offset, receiver_start, false)
    }

    pub(crate) fn indexed_module_receiver_path(
        &self,
        written: &[SmolStr],
        offset: TextSize,
        receiver_start: Option<TextSize>,
    ) -> Option<ModulePath> {
        self.module_receiver_path_impl(written, offset, receiver_start, true)
    }

    fn module_receiver_path_impl(
        &self,
        written: &[SmolStr],
        offset: TextSize,
        receiver_start: Option<TextSize>,
        require_index: bool,
    ) -> Option<ModulePath> {
        let (head, tail) = written.split_first()?;
        // A recorded occurrence has the actual scope of a read. In a let/for
        // initializer, that is outside the scope that binds the new variable,
        // even when the latter's source range overlaps the initializer.
        let scope = receiver_start
            .and_then(|start| {
                self.model.ident_at(start).filter(|ident| {
                    ident.range.start() == start && &ident.name == head && !ident.is_macro
                })
            })
            .map_or_else(|| self.model.scope_at(offset), |ident| ident.scope);
        let mut path = match self.resolve_at_scope(head, offset, Namespace::Value, scope) {
            Resolution::Binding(id) => {
                let binding = self.model.binding(id);
                match binding.kind {
                    BindingKind::Module => {
                        let workspace = self.workspace.as_ref()?;
                        let mut path = self.full_module_path(workspace, binding.scope);
                        path.insert(0, SmolStr::new(&workspace.pkg.name));
                        path.push(head.clone());
                        path
                    }
                    BindingKind::Import => {
                        let load = self.model.module_loads().iter().find(|load| {
                            load.scope == binding.scope
                                && load.range.contains_range(binding.def_range)
                        })?;
                        if load.path.leading_dots != 0 {
                            return None;
                        }
                        let mut path = load.path.components.clone();
                        if let Some(items) = &load.items {
                            let item = items.iter().find(|item| {
                                item.range.contains_range(binding.def_range)
                                    && item.alias.as_ref().unwrap_or(&item.name) == head
                            })?;
                            path.push(item.name.clone());
                        }
                        // A clause can import a function, type, or value rather
                        // than a module. Confirm the target before using it.
                        self.canonical_module_path(&path)?;
                        path
                    }
                    _ => return None,
                }
            }
            Resolution::Workspace { mut module, name } => {
                let workspace = self.workspace.as_ref()?;
                let host = module_at(&workspace.pkg.root, &module)?;
                if host.name != name.as_str() {
                    host.submodules
                        .iter()
                        .find(|sub| sub.name == name.as_str())?;
                    module.push(name);
                }
                module.insert(0, SmolStr::new(&workspace.pkg.name));
                module
            }
            Resolution::WorkspaceImport { .. } => {
                let workspace = self.workspace.as_ref()?;
                let mut path = self.full_module_path(workspace, scope);
                path.insert(0, SmolStr::new(&workspace.pkg.name));
                path.push(head.clone());
                self.canonical_module_path(&path)?;
                path
            }
            Resolution::Using { module, name } | Resolution::System { module, name } => {
                let mut path: ModulePath = module.split('.').map(SmolStr::new).collect();
                if module != name {
                    path.push(name);
                }
                self.canonical_module_path(&path)?;
                path
            }
            Resolution::Unresolved => {
                if let Some(workspace) = &self.workspace {
                    let mut host_path = self.full_module_path(workspace, scope);
                    if module_at(&workspace.pkg.root, &host_path).is_some_and(|host| {
                        host.submodules.iter().any(|sub| sub.name == head.as_str())
                    }) {
                        host_path.push(head.clone());
                        host_path.insert(0, SmolStr::new(&workspace.pkg.name));
                        host_path
                    } else {
                        vec![head.clone()]
                    }
                } else {
                    vec![head.clone()]
                }
            }
            Resolution::Script { .. } | Resolution::Ambiguous => return None,
        };
        path.extend_from_slice(tail);
        self.canonical_module_path(&path)
            .or_else(|| (!require_index).then_some(path))
    }

    fn indexed_module_at(&self, path: &[SmolStr]) -> Option<ModuleIndexHandle> {
        self.module_index_with(path, |name| self.packages.package(name))
    }

    fn environment_module_at(&self, path: &[SmolStr]) -> Option<ModuleIndexHandle> {
        self.module_index_with(path, |name| self.packages.environment_package(name))
    }

    fn module_index_with(
        &self,
        path: &[SmolStr],
        lookup: impl FnOnce(&str) -> Option<Arc<PackageIndex>>,
    ) -> Option<ModuleIndexHandle> {
        let (head, rest) = path.split_first()?;
        let pkg = self
            .workspace
            .as_ref()
            .filter(|workspace| workspace.pkg.name == head.as_str())
            .map(|workspace| workspace.pkg.clone())
            .or_else(|| lookup(head))?;
        module_at(&pkg.root, rest)?;
        Some(ModuleIndexHandle {
            pkg,
            rest: rest.to_vec(),
        })
    }

    /// Resolve aliases only when the destination is a statically indexed module.
    /// The first segment is a lexical package name selected by the caller.
    fn canonical_module_path(&self, path: &[SmolStr]) -> Option<ModulePath> {
        if self.indexed_module_at(path).is_some() {
            return Some(path.to_vec());
        }
        self.indexed_module_at(path.get(..1)?)?;
        self.module_origin(path, &mut Vec::new())
    }

    /// Follow imports from inside a package, not from the editor project's
    /// direct-dependency view. Relative paths never leave the host package.
    fn verify_import_root(&self, from: &[SmolStr], to: &[SmolStr]) -> Option<()> {
        let (owner, target) = (from.first()?, to.first()?);
        if owner != target {
            self.packages.dependency_package(owner, target)?;
        }
        Some(())
    }

    fn module_origin(
        &self,
        path: &[SmolStr],
        visiting: &mut Vec<(ModulePath, SmolStr)>,
    ) -> Option<ModulePath> {
        let (head, rest) = path.split_first()?;
        let mut current = vec![head.clone()];
        self.environment_module_at(&current)?;
        for name in rest {
            match self.member_origin(&current, name, visiting)? {
                QualifiedMember::Module(path) => current = path,
                QualifiedMember::Symbol { .. } => return None,
            }
        }
        Some(current)
    }

    /// Resolve a bound/re-exported qualified symbol to its actual provider.
    /// Never infer a binding solely from an export declaration or textual alias.
    pub(crate) fn qualified_member_origin(
        &self,
        module: &[SmolStr],
        name: &str,
    ) -> Option<QualifiedMember> {
        self.member_origin(module, &SmolStr::new(name), &mut Vec::new())
    }

    fn member_origin(
        &self,
        path: &[SmolStr],
        name: &SmolStr,
        visiting: &mut Vec<(ModulePath, SmolStr)>,
    ) -> Option<QualifiedMember> {
        const MAX_CHAIN: usize = 24;
        if visiting.len() >= MAX_CHAIN || visiting.iter().any(|(p, n)| p == path && n == name) {
            return None;
        }
        let module = self.environment_module_at(path)?;
        if module
            .submodules
            .iter()
            .any(|sub| sub.name == name.as_str())
        {
            let mut path = path.to_vec();
            path.push(name.clone());
            return Some(QualifiedMember::Module(path));
        }
        let kind = if name.starts_with('@') {
            module
                .macros
                .iter()
                .any(|m| m.name == name.as_str())
                .then_some(QualifiedMemberKind::Macro)
        } else if module.types.iter().any(|t| t.name == name.as_str()) {
            Some(QualifiedMemberKind::Type)
        } else if module.consts.iter().any(|c| c.name == name.as_str()) {
            Some(QualifiedMemberKind::Const)
        } else if module
            .functions
            .iter()
            .any(|f| f.owner.is_none() && f.name == name.as_str())
            && !module_imports(&module, name)
        {
            Some(QualifiedMemberKind::Function)
        } else {
            None
        };
        if let Some(kind) = kind {
            return Some(QualifiedMember::Symbol {
                module: path.to_vec(),
                name: name.clone(),
                kind,
            });
        }
        // An export can name a binding provided by a whole-module using. Do
        // not flood qualified completion with every opened module's exports.
        let reexported = module.exports.iter().any(|e| e.name == name.as_str());
        let binding = module
            .imported_names
            .iter()
            .filter(|n| *n == name.as_str())
            .count();
        if !reexported && binding == 0 {
            return None;
        }
        visiting.push((path.to_vec(), name.clone()));
        let result = (|| {
            let mut result = None;
            if binding != 0 {
                let imports = module
                    .import_bindings
                    .iter()
                    .filter(|i| i.local == name.as_str());
                // Unknown/dynamic declarations with the same alias cannot
                // make an otherwise provable duplicate safe.
                if imports.clone().count() != binding {
                    return None;
                }
                for import in imports {
                    let target = import_target(path, import.leading_dots, &import.components)?;
                    self.verify_import_root(path, &target)?;
                    let origin = if target.len() == 1 {
                        self.environment_module_at(&target)?;
                        QualifiedMember::Module(target)
                    } else {
                        let (last, parent) = target.split_last()?;
                        let provider = self.module_origin(parent, visiting)?;
                        self.member_origin(&provider, last, visiting)?
                    };
                    add_unique_member(&mut result, origin)?;
                }
            } else {
                for using in &module.usings {
                    let target = import_target(path, using.leading_dots, &using.components)?;
                    self.verify_import_root(path, &target)?;
                    let provider = self.module_origin(&target, visiting)?;
                    let opened = self.environment_module_at(&provider)?;
                    if module_exports(&opened, name) {
                        let origin = self.member_origin(&provider, name, visiting)?;
                        add_unique_member(&mut result, origin)?;
                    }
                }
                // Standard modules open Core and Base; baremodule still opens
                // Core, but not Base. Consider only this explicit re-export,
                // and reject conflicting binding identities across open modules.
                let systems: &[&str] = if module.bare {
                    &["Core"]
                } else {
                    &["Base", "Core"]
                };
                for system in systems {
                    if path.first().is_some_and(|head| head == *system) {
                        continue;
                    }
                    let provider = [SmolStr::new(system)];
                    if let Some(opened) = self.environment_module_at(&provider)
                        && module_exports(&opened, name)
                    {
                        let origin = self.member_origin(&provider, name, visiting)?;
                        add_unique_member(&mut result, origin)?;
                    }
                }
            }
            result
        })();
        visiting.pop();
        result
    }

    /// Whether a fully qualified package path names a harvested symbol.
    ///
    /// `None` means the root package is unknown, so absence cannot be proved.
    /// A known package yields `Some(false)` only after its submodule path and
    /// final value or macro name have both been checked. This is intentionally
    /// narrower than ordinary bare-name resolution: local module aliases and
    /// runtime-created modules remain unknown rather than becoming false
    /// positives for documentation checks.
    pub fn qualified_name_exists(&self, path: &[SmolStr], namespace: Namespace) -> Option<bool> {
        let (name, module_path) = path.split_last()?;
        let (head, rest) = module_path.split_first()?;
        let package = self
            .workspace
            .as_ref()
            .filter(|workspace| workspace.pkg.name == head.as_str())
            .map(|workspace| workspace.pkg.clone())
            .or_else(|| self.packages.package(head))?;
        let Some(module) = module_at(&package.root, rest) else {
            return Some(false);
        };
        let wanted = if namespace == Namespace::Macro && name.starts_with('@') {
            name.clone()
        } else {
            wanted_name(name, namespace)
        };
        Some(
            module_defines(module, &wanted, namespace)
                || module
                    .exports
                    .iter()
                    .any(|export| export.name == wanted.as_str())
                || (namespace == Namespace::Value
                    && module
                        .submodules
                        .iter()
                        .any(|submodule| submodule.name == wanted.as_str())),
        )
    }

    /// Every name visible at `offset`, in the shared masking order with shadowed
    /// names dropped: file bindings innermost-first, then `using`'d exports in
    /// source order, then Base/Core. For completion.
    pub fn visible(&self, offset: TextSize, namespace: Namespace) -> Vec<Candidate> {
        let mut seen: HashSet<SmolStr> = HashSet::new();
        let mut out: Vec<Candidate> = Vec::new();

        // Tiers 1 + 2: file bindings up the scope chain (stops at the first
        // global scope, like reads do).
        let completion_scope = self.model.completion_scope(offset);
        let mut cursor = Some(completion_scope.id);
        while let Some(id) = cursor {
            let scope = self.model.scope(id);
            let parameters_before = completion_scope.parameters_before(id);
            for &b in scope.bindings.iter().rev() {
                let binding = self.model.binding(b);
                if crate::semantic::CompletionScope::admits(binding, parameters_before)
                    && let Some(name) = namespaced_binding_name(binding, namespace)
                    && seen.insert(name.clone())
                {
                    out.push(Candidate {
                        name,
                        source: Source::Binding(b),
                    });
                }
            }
            cursor = if scope.kind.is_global() {
                None
            } else {
                scope.parent
            };
        }

        // Tier 2 (cross-file): same-module sibling top-level symbols of the
        // module enclosing this position, masked by anything bound in this file
        // already.
        if let Some(workspace) = &self.workspace
            && let Some(module) = module_at(
                &workspace.pkg.root,
                &self.full_module_path(workspace, self.model.scope_at(offset)),
            )
        {
            // Same-module top-level definitions, then the names a sibling file's
            // module-level `using`/`import` binds — both module globals.
            let definite: HashSet<&str> = match namespace {
                Namespace::Value => module
                    .types
                    .iter()
                    .map(|t| t.name.as_str())
                    .chain(module.consts.iter().map(|c| c.name.as_str()))
                    .chain(
                        module
                            .functions
                            .iter()
                            .filter(|f| f.methods.iter().any(|m| !m.is_generated))
                            .map(|f| f.name.as_str()),
                    )
                    .collect(),
                Namespace::Macro => HashSet::new(),
            };
            for name in defined_names(module, namespace)
                .into_iter()
                .filter(|name| {
                    namespace == Namespace::Macro
                        || definite.contains(name.as_str())
                        || !self
                            .export_provider(name, offset)
                            .is_some_and(|(_, provider)| {
                                module_declares_type_or_const(&provider, name)
                            })
                })
                .chain(imported_names(module, namespace))
            {
                if seen.insert(name.clone()) {
                    out.push(Candidate {
                        name,
                        source: Source::Workspace {
                            module: SmolStr::new(&module.name),
                        },
                    });
                }
            }
        }

        // Track duplicates only among the whole-module imports. Explicit
        // bindings and locals above them keep their existing precedence.
        let at = self.model.scope_at(offset);
        let mut using_paths = HashSet::new();
        let mut using_names = HashSet::new();
        let mut checked = HashSet::new();
        let mut ambiguous = HashSet::new();
        for (path, module) in self.visible_usings(at) {
            let display: SmolStr = path.rsplit('.').next().unwrap_or(&path).into();
            if !using_paths.insert(path) {
                continue;
            }
            for name in exported_names(&module, namespace) {
                if seen.insert(name.clone()) {
                    using_names.insert(name.clone());
                    out.push(Candidate {
                        name,
                        source: Source::Using {
                            module: display.clone(),
                        },
                    });
                } else if using_names.contains(&name)
                    && checked.insert(name.clone())
                    && self.opened_export(&name, self.visible_usings(at)).is_err()
                {
                    ambiguous.insert(name);
                }
            }
        }
        if !ambiguous.is_empty() {
            out.retain(|candidate| !ambiguous.contains(&candidate.name));
        }

        // Tier 4: Base/Core implicit.
        for module in ["Base", "Core"] {
            let Some(pkg) = self.packages.package(module) else {
                continue;
            };
            for name in exported_names(&pkg.root, namespace) {
                if seen.insert(name.clone()) {
                    out.push(Candidate {
                        name,
                        source: Source::System {
                            module: SmolStr::new(module),
                        },
                    });
                }
            }
        }

        out
    }

    /// Every occurrence, in this file, of a top-level symbol of the enclosing
    /// workspace package, keyed by `(module path, namespace, bare-or-@ name)`.
    /// Two sources unify under one key: this file's own module-global bindings (a
    /// file that *defines* the symbol, contributing its definition and intra-file
    /// uses) and its free reads that resolve to the workspace tier (a file that
    /// only *uses* it). Keying by name — not [`BindingId`], which is per-file — is
    /// what lets the aggregate stitch a defining file's occurrences together with
    /// a calling file's, including multi-file multiple dispatch (`function f end`
    /// plus methods of `f` across files); the module path in the key keeps
    /// same-named symbols in *different* modules apart.
    ///
    /// Empty when the file is not a workspace member. Qualified reads (`Pkg.foo`)
    /// are deferred: the model records only the whole chain's range, not the
    /// `foo` sub-span a precise rename needs.
    pub fn workspace_occurrences(&self) -> BTreeMap<OccurrenceKey, Vec<OccurrenceRec>> {
        let mut out: BTreeMap<OccurrenceKey, Vec<OccurrenceRec>> = BTreeMap::new();
        let Some(workspace) = &self.workspace else {
            return out;
        };

        // Defining files: occurrences of each module-global binding whose name the
        // module enclosing it (host module plus file-internal nested `module`s)
        // actually defines at top level. The `workspace_defines` gate matches exactly
        // what the workspace tier of `resolve` fires on, so a plain file-scope
        // global (`x = 1`) or an import the harvester skips is left out, keeping
        // this in lockstep with go-to-definition.
        for (i, binding) in self.model.bindings().iter().enumerate() {
            if !self.model.scope(binding.scope).kind.is_global() {
                continue;
            }
            let path = self.full_module_path(workspace, binding.scope);
            let Some(module) = module_at(&workspace.pkg.root, &path) else {
                continue;
            };
            for ns in [Namespace::Value, Namespace::Macro] {
                let Some(name) = namespaced_binding_name(binding, ns) else {
                    continue;
                };
                if !self.workspace_defines(module, &name, binding.def_range.start(), ns) {
                    continue;
                }
                let recs = out
                    .entry(OccurrenceKey {
                        package: SmolStr::new(&workspace.pkg.name),
                        module: path.clone(),
                        namespace: ns,
                        name,
                    })
                    .or_default();
                for occ in self.model.occurrences(BindingId(i as u32)) {
                    recs.push(OccurrenceRec {
                        range: occ.range,
                        is_def: occ.is_def,
                        access: occ.access,
                    });
                }
            }
        }

        // Using files: free reads that resolve to the workspace tier.
        for ident in self.model.idents() {
            if ident.binding.is_some() {
                continue;
            }
            let ns = if ident.is_macro {
                Namespace::Macro
            } else {
                Namespace::Value
            };
            if let Resolution::Workspace { module, name } =
                self.resolve(&ident.name, ident.range.start(), ns)
            {
                out.entry(OccurrenceKey {
                    package: SmolStr::new(&workspace.pkg.name),
                    module,
                    namespace: ns,
                    name,
                })
                .or_default()
                .push(OccurrenceRec {
                    range: ident.range,
                    is_def: false,
                    access: ident.access,
                });
            }
        }

        // Source order within each name, deduped by range for a stable, unique
        // result (defensive: the two sources never overlap in practice).
        for recs in out.values_mut() {
            recs.sort_by_key(|r| (r.range.start(), r.range.end()));
            recs.dedup_by_key(|r| (r.range.start(), r.range.end()));
        }
        out
    }

    /// The workspace top-level symbol the cursor at `offset` names, if any — a
    /// package global defined in this file, or a free read resolving to the
    /// workspace tier. `None` for a local, a library symbol, or a non-member
    /// file. The classification cross-file references and rename escalate on;
    /// it mirrors go-to-definition's cursor classification exactly.
    pub fn workspace_symbol_at(&self, offset: TextSize) -> Option<OccurrenceKey> {
        let workspace = self.workspace.as_ref()?;
        // An identifier occurrence: local when it binds, else a free read.
        if let Some(ident) = self.model.ident_at(offset) {
            if let Some(bid) = ident.binding {
                return self.binding_workspace_symbol(bid, workspace);
            }
            let ns = if ident.is_macro {
                Namespace::Macro
            } else {
                Namespace::Value
            };
            return match self.resolve(&ident.name, offset, ns) {
                Resolution::Workspace { module, name } => Some(OccurrenceKey {
                    package: SmolStr::new(&workspace.pkg.name),
                    module,
                    namespace: ns,
                    name,
                }),
                _ => None,
            };
        }
        // A definition site (the cursor sits on a name in its own definition).
        if let Some(bid) = self.model.binding_at(offset) {
            return self.binding_workspace_symbol(bid, workspace);
        }
        None
    }

    /// Whether a workspace symbol's declarations can all be renamed through the
    /// reference index. Generated methods have no editable declaration there,
    /// even when ordinary methods of the same function are recorded.
    pub fn can_rename_workspace_symbol(&self, symbol: &OccurrenceKey) -> bool {
        let Some(workspace) = &self.workspace else {
            return false;
        };
        if workspace.pkg.name != symbol.package.as_str() {
            return false;
        }
        let Some(module) = module_at(&workspace.pkg.root, &symbol.module) else {
            return false;
        };
        symbol.namespace != Namespace::Value
            || !module.functions.iter().any(|group| {
                group.name == symbol.name.as_str()
                    && group.methods.iter().any(|method| method.is_generated)
            })
    }

    /// `(module path, namespace, name)` when `bid` is a module-global the module
    /// enclosing it (host module plus file-internal nested `module`s) defines at
    /// top level — i.e. a package symbol other files can reference, not a plain
    /// local or a file-scope global the harvester skips. The gate matches
    /// `resolve`'s workspace tier, keeping references/rename in lockstep.
    fn binding_workspace_symbol(
        &self,
        bid: BindingId,
        workspace: &WorkspaceCtx,
    ) -> Option<OccurrenceKey> {
        let binding = self.model.binding(bid);
        if !self.model.scope(binding.scope).kind.is_global() {
            return None;
        }
        let path = self.full_module_path(workspace, binding.scope);
        let module = module_at(&workspace.pkg.root, &path)?;
        for ns in [Namespace::Value, Namespace::Macro] {
            if let Some(name) = namespaced_binding_name(binding, ns)
                && self.workspace_defines(module, &name, binding.def_range.start(), ns)
            {
                return Some(OccurrenceKey {
                    package: SmolStr::new(&workspace.pkg.name),
                    module: path.clone(),
                    namespace: ns,
                    name,
                });
            }
        }
        None
    }

    fn workspace_defines(
        &self,
        module: &ModuleIndex,
        wanted: &SmolStr,
        offset: TextSize,
        namespace: Namespace,
    ) -> bool {
        if !module_defines(module, wanted, namespace) {
            return false;
        }
        // Generated overloads alone do not establish a new binding over an
        // imported type. Explicit function declarations still mask its exports.
        namespace != Namespace::Value
            || module_declares_type_or_const(module, wanted)
            || module.functions.iter().any(|group| {
                group.name == wanted.as_str()
                    && group.methods.iter().any(|method| !method.is_generated)
            })
            || !self
                .export_provider(wanted, offset)
                .is_some_and(|(_, provider)| module_declares_type_or_const(&provider, wanted))
    }

    /// Tiers 1 + 2: the binding `wanted` reads to, resolving up the scope chain
    /// and stopping after the first global scope (module bodies do not see
    /// enclosing globals). Mirrors the builder's `resolve_read`.
    fn file_binding(
        &self,
        wanted: &SmolStr,
        at: ScopeId,
        namespace: Namespace,
    ) -> Option<BindingId> {
        let mut cursor = Some(at);
        while let Some(id) = cursor {
            let scope = self.model.scope(id);
            let hit = scope.bindings.iter().rev().copied().find(|&b| {
                namespaced_binding_name(self.model.binding(b), namespace).as_ref() == Some(wanted)
            });
            if hit.is_some() {
                return hit;
            }
            cursor = if scope.kind.is_global() {
                None
            } else {
                scope.parent
            };
        }
        None
    }

    /// All resolvable whole-module imports from the file and indexed siblings.
    fn visible_usings(&self, scope: ScopeId) -> impl Iterator<Item = UsingProvider> + '_ {
        let local = self.model.module_loads().iter().filter_map(move |load| {
            let module = self.using_module(load, scope)?;
            Some((load.path.components.join(".").into(), module))
        });
        let sibling = self
            .workspace
            .as_ref()
            .and_then(|workspace| {
                module_at(
                    &workspace.pkg.root,
                    &self.full_module_path(workspace, scope),
                )
            })
            .into_iter()
            .flat_map(|module| self.indexed_usings(&module.usings));
        local.chain(sibling)
    }

    fn indexed_usings<'b>(
        &'b self,
        usings: &'b [ModuleUsing],
    ) -> impl Iterator<Item = UsingProvider> + 'b {
        usings.iter().filter_map(|using| {
            let module = self.resolve_using(using)?;
            Some((using.components.join(".").into(), module))
        })
    }

    /// Check binding identity only when distinct visible module paths both
    /// claim this name. An export statement alone is not a binding, and two
    /// independently assigned constants can be `===` at runtime.
    fn opened_export(
        &self,
        wanted: &SmolStr,
        providers: impl Iterator<Item = UsingProvider>,
    ) -> Result<Option<UsingProvider>, ()> {
        let mut exports = providers.filter(|(_, module)| module_exports(module, wanted));
        let Some(first) = exports.next() else {
            return Ok(None);
        };
        let mut checked = HashSet::new();
        let mut identified = None;
        let mut multiple = false;
        for (path, module) in exports {
            if path == first.0 || !checked.insert(path) {
                continue;
            }
            if !multiple {
                identified = self.defined_export_origin(&first.1, wanted);
                multiple = true;
            }
            if let Some(origin) = self.defined_export_origin(&module, wanted) {
                if identified
                    .as_ref()
                    .is_some_and(|previous| previous != &origin)
                {
                    return Err(());
                }
                identified = Some(origin);
            }
        }
        Ok(Some(first))
    }

    /// Identity that does not require evaluating arbitrary Julia expressions.
    fn defined_export_origin(
        &self,
        module: &ModuleIndexHandle,
        wanted: &SmolStr,
    ) -> Option<QualifiedMember> {
        if !module.pkg.diagnostics.is_empty() {
            return None;
        }
        let mut path = vec![SmolStr::new(&module.pkg.name)];
        path.extend_from_slice(&module.rest);
        let origin = self.qualified_member_origin(&path, wanted)?;
        match &origin {
            QualifiedMember::Module(_) => Some(origin),
            QualifiedMember::Symbol {
                kind: QualifiedMemberKind::Const,
                ..
            } => None,
            QualifiedMember::Symbol {
                module,
                name,
                kind: QualifiedMemberKind::Function,
            } => self
                .indexed_module_at(module)?
                .functions
                .iter()
                .any(|group| {
                    group.owner.is_none()
                        && group.name == name.as_str()
                        && group.methods.iter().any(|method| !method.is_generated)
                })
                .then_some(origin),
            QualifiedMember::Symbol { .. } => Some(origin),
        }
    }

    /// The [`ModuleIndex`] a harvested whole-module `using` clause points at, or
    /// `None` for a relative/interpolated path or a module the library has not
    /// harvested. The [`ModuleUsing`] counterpart of
    /// [`using_module`](Self::using_module); the returned module owns its data
    /// via the package `Arc`.
    fn resolve_using(&self, using: &ModuleUsing) -> Option<Arc<ModuleIndexHandle>> {
        if using.leading_dots != 0 || using.components.is_empty() {
            return None;
        }
        let pkg = self.packages.package(&using.components[0])?;
        let rest: Vec<SmolStr> = using.components[1..].iter().map(SmolStr::new).collect();
        resolve_module_path(&pkg.root, &rest)?;
        Some(Arc::new(ModuleIndexHandle { pkg, rest }))
    }

    /// A whole-module `using` or implicit Base/Core module exporting `name`,
    /// independently of local and workspace bindings that mask those tiers.
    /// A method group can extend an imported type's constructors, so its
    /// presence alone cannot establish that the name refers to a function.
    pub fn export_module_providing(
        &self,
        name: &str,
        offset: TextSize,
        namespace: Namespace,
    ) -> Option<SmolStr> {
        let wanted = wanted_name(name, namespace);
        self.export_provider(&wanted, offset)
            .map(|(module, _)| module)
    }

    fn export_provider(
        &self,
        wanted: &SmolStr,
        offset: TextSize,
    ) -> Option<(SmolStr, Arc<ModuleIndexHandle>)> {
        match self.opened_export(wanted, self.visible_usings(self.model.scope_at(offset))) {
            Ok(Some(provider)) => Some(provider),
            Err(()) => None,
            Ok(None) => {
                let (module, pkg) = self.system_export(wanted)?;
                Some((
                    module,
                    Arc::new(ModuleIndexHandle {
                        pkg,
                        rest: Vec::new(),
                    }),
                ))
            }
        }
    }

    /// The Base/Core module exporting `name` (tier 4), asked *independently of*
    /// the masking order — the one question [`resolve`](Self::resolve) cannot
    /// answer for a name the file binds, since the binding is precisely what
    /// masks the tier. `shadowed-base-name` needs both halves: what the name
    /// means here, and what it would have meant.
    pub fn system_module_exporting(&self, name: &str, namespace: Namespace) -> Option<SmolStr> {
        self.system_export(&wanted_name(name, namespace))
            .map(|(module, _)| module)
    }

    /// Tier 4: `wanted` if Base or Core exports it (Base first).
    fn system_export(&self, wanted: &SmolStr) -> Option<(SmolStr, Arc<PackageIndex>)> {
        for module in ["Base", "Core"] {
            let pkg = self.packages.package(module)?;
            if module_exports(&pkg.root, wanted) {
                return Some((SmolStr::new(module), pkg));
            }
        }
        None
    }

    /// The [`ModuleIndex`] a whole-module `using` clause brings into scope at
    /// `at`, or `None` when the clause is not a resolvable whole-module `using`
    /// (an `import`, an item list, a relative/interpolated path, or a module the
    /// library has not harvested). The returned module owns its data via the
    /// package `Arc`, cloned once here.
    fn using_module(
        &self,
        load: &crate::semantic::ModuleLoad,
        at: ScopeId,
    ) -> Option<Arc<ModuleIndexHandle>> {
        if load.kind != LoadKind::Using || load.items.is_some() {
            return None;
        }
        if load.path.leading_dots != 0 || load.path.components.is_empty() {
            return None;
        }
        if !self.scope_visible(load.scope, at) {
            return None;
        }
        let pkg = self.packages.package(&load.path.components[0])?;
        // Confirm the sub-path exists before committing to the handle.
        resolve_module_path(&pkg.root, &load.path.components[1..])?;
        Some(Arc::new(ModuleIndexHandle {
            pkg,
            rest: load.path.components[1..].to_vec(),
        }))
    }

    /// Whether a statement in `decl_scope` is visible from `at`: `decl_scope` is
    /// reachable up the scope chain without crossing out of the first enclosing
    /// global scope — the same reach a read has.
    fn scope_visible(&self, decl_scope: ScopeId, at: ScopeId) -> bool {
        let mut cursor = Some(at);
        while let Some(id) = cursor {
            if id == decl_scope {
                return true;
            }
            let scope = self.model.scope(id);
            if scope.kind.is_global() {
                return false;
            }
            cursor = scope.parent;
        }
        false
    }
}

fn import_target(path: &[SmolStr], dots: u32, components: &[String]) -> Option<ModulePath> {
    if components.is_empty() {
        return None;
    }
    let mut target = if dots == 0 {
        vec![]
    } else {
        let keep = path.len().checked_sub(dots as usize - 1)?;
        if keep == 0 {
            return None;
        }
        path[..keep].to_vec()
    };
    target.extend(components.iter().map(SmolStr::new));
    Some(target)
}

fn add_unique_member(slot: &mut Option<QualifiedMember>, member: QualifiedMember) -> Option<()> {
    match slot {
        Some(previous) if *previous != member => None,
        Some(_) => Some(()),
        None => {
            *slot = Some(member);
            Some(())
        }
    }
}

/// Resolve a full module path returned by [`Resolution::Using`] without
/// depending on which file contains the `using` clause.
pub(crate) fn resolve_module<P: PackageSource + ?Sized>(
    packages: &P,
    path: &str,
) -> Option<ModuleIndexHandle> {
    let mut components = path.split('.');
    let pkg = packages.package(components.next()?)?;
    let rest: ModulePath = components.map(SmolStr::new).collect();
    module_at(&pkg.root, &rest)?;
    Some(ModuleIndexHandle { pkg, rest })
}

/// A resolved module that keeps its package `Arc` alive while consumers borrow
/// its [`ModuleIndex`]. Dereferences to the module it points at.
pub(crate) struct ModuleIndexHandle {
    pub(crate) pkg: Arc<PackageIndex>,
    rest: Vec<SmolStr>,
}

impl std::ops::Deref for ModuleIndexHandle {
    type Target = ModuleIndex;
    fn deref(&self) -> &ModuleIndex {
        // Construction verifies the path, and the immutable package keeps it
        // valid for every subsequent lookup.
        resolve_module_path(&self.pkg.root, &self.rest).expect("module sub-path verified")
    }
}

/// Walk `root`'s submodules along `path` by name (`["B", "C"]` from `A`'s root
/// reaches `A.B.C`); an empty `path` is `root` itself. The by-name counterpart
/// of [`resolve_module_path`], for member completion resolving a dotted
/// receiver (`A.B.`) against the library.
pub fn resolve_submodule<'m>(root: &'m ModuleIndex, path: &[&str]) -> Option<&'m ModuleIndex> {
    let mut current = root;
    for name in path {
        current = current.submodules.iter().find(|m| m.name == *name)?;
    }
    Some(current)
}

/// Walk `root`'s submodules along `rest` (`using A.B.C` → from `A`'s root, walk
/// `B` then `C`); an empty `rest` is `root` itself. The [`SmolStr`] alias of
/// [`module_at`].
fn resolve_module_path<'m>(root: &'m ModuleIndex, rest: &[SmolStr]) -> Option<&'m ModuleIndex> {
    module_at(root, rest)
}

/// Whether `module` `export`s `wanted` (not merely `public`s it — only exported
/// names are brought in by `using` or the implicit Base/Core tier).
fn module_exports(module: &ModuleIndex, wanted: &SmolStr) -> bool {
    module
        .exports
        .iter()
        .any(|e| e.visibility == Visibility::Exported && e.name == wanted.as_str())
}

/// Whether `module` *defines* `wanted` at top level (a function, type, or const
/// in [`Namespace::Value`]; a macro in [`Namespace::Macro`]). Unlike
/// [`module_exports`], visibility is irrelevant: within a module every top-level
/// binding is a global its own files see, exported or not. Names are stored bare
/// for values and `@`-prefixed for macros, matching `wanted`.
fn module_defines(module: &ModuleIndex, wanted: &SmolStr, namespace: Namespace) -> bool {
    match namespace {
        Namespace::Value => {
            module.functions.iter().any(|f| f.name == wanted.as_str())
                || module_declares_type_or_const(module, wanted)
        }
        Namespace::Macro => module.macros.iter().any(|m| m.name == wanted.as_str()),
    }
}

fn module_declares_type_or_const(module: &ModuleIndex, wanted: &SmolStr) -> bool {
    module.types.iter().any(|t| t.name == wanted.as_str())
        || module.consts.iter().any(|c| c.name == wanted.as_str())
}

/// Whether a name a module-level `using`/`import` binds is recorded for
/// `module` (see [`ModuleIndex::imported_names`]). Names are stored as typed —
/// bare for a value, `@`-prefixed for a macro — matching `wanted`.
fn module_imports(module: &ModuleIndex, wanted: &SmolStr) -> bool {
    module.imported_names.iter().any(|n| n == wanted.as_str())
}

/// The names a module-level `using`/`import` binds in `module`, in the given
/// namespace, as they would be typed. The completion counterpart of
/// [`module_imports`].
fn imported_names(module: &ModuleIndex, namespace: Namespace) -> Vec<SmolStr> {
    module
        .imported_names
        .iter()
        .filter(|n| in_namespace(n, namespace))
        .map(SmolStr::new)
        .collect()
}

/// Every name `module` defines at top level in `namespace`, as it would be typed
/// (macros keep `@`), in definition order. The completion counterpart of
/// [`module_defines`].
fn defined_names(module: &ModuleIndex, namespace: Namespace) -> Vec<SmolStr> {
    match namespace {
        Namespace::Value => module
            .functions
            .iter()
            .map(|f| f.name.as_str())
            .chain(module.types.iter().map(|t| t.name.as_str()))
            .chain(module.consts.iter().map(|c| c.name.as_str()))
            .map(SmolStr::new)
            .collect(),
        Namespace::Macro => module
            .macros
            .iter()
            .map(|m| SmolStr::new(&m.name))
            .collect(),
    }
}

/// The `export`ed names of `module` in the given namespace, as they would be
/// typed (macros keep `@`), in source order.
fn exported_names(module: &ModuleIndex, namespace: Namespace) -> Vec<SmolStr> {
    module
        .exports
        .iter()
        .filter(|e| e.visibility == Visibility::Exported && in_namespace(&e.name, namespace))
        .map(|e| SmolStr::new(&e.name))
        .collect()
}

/// The name to look up for `name` read in `namespace`: `@`-prefixed for macros
/// (the sigil the index and imported-macro bindings carry), bare for values.
fn wanted_name(name: &str, namespace: Namespace) -> SmolStr {
    match namespace {
        Namespace::Value => SmolStr::new(name),
        Namespace::Macro => SmolStr::new(format!("@{name}")),
    }
}

/// Whether a stored name (`println`, `@time`) belongs to `namespace`.
fn in_namespace(name: &str, namespace: Namespace) -> bool {
    match namespace {
        Namespace::Value => !name.starts_with('@'),
        Namespace::Macro => name.starts_with('@'),
    }
}

/// The name of `binding` in `namespace`, normalized to how it is typed (macros
/// `@`-prefixed), or `None` if the binding does not live in that namespace.
///
/// The model stores macro-definition bindings bare (`m`) but imported-macro
/// bindings with the sigil (`@foo`); this reconciles both to `@name`, matching
/// the builder's `resolve_macro_read`.
fn namespaced_binding_name(binding: &Binding, namespace: Namespace) -> Option<SmolStr> {
    match namespace {
        Namespace::Value => match binding.kind {
            BindingKind::Macro => None,
            BindingKind::Import if binding.name.starts_with('@') => None,
            _ => Some(binding.name.clone()),
        },
        Namespace::Macro => match binding.kind {
            BindingKind::Macro => Some(SmolStr::new(format!("@{}", binding.name))),
            BindingKind::Import if binding.name.starts_with('@') => Some(binding.name.clone()),
            _ => None,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::index::model::{DefLocation, ExportedName, Span};

    fn model_of(src: &str) -> SemanticModel {
        SemanticModel::build(&crate::parser::parse(src).cst)
    }

    fn loc() -> DefLocation {
        DefLocation {
            file: "src/x.jl".into(),
            range: Span { start: 0, end: 0 },
        }
    }

    /// A package whose root module exports `exports` (each `@name` is a macro).
    fn package(name: &str, exports: &[&str]) -> Arc<PackageIndex> {
        module_package(name, exports, Vec::new())
    }

    fn harvested_package(name: &str, source: &str) -> Arc<PackageIndex> {
        let parsed = crate::parser::parse(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut pkg = (*package(name, &[])).clone();
        pkg.root = crate::index::harvest_tree(&parsed.cst);
        pkg.root.name = name.into();
        Arc::new(pkg)
    }

    fn module_package(
        name: &str,
        exports: &[&str],
        submodules: Vec<ModuleIndex>,
    ) -> Arc<PackageIndex> {
        Arc::new(PackageIndex {
            name: name.to_string(),
            root: ModuleIndex {
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
                submodules,
                usings: Vec::new(),
                imported_names: Vec::new(),
                import_bindings: Vec::new(),
            },
            members: Vec::new(),
            member_modules: Default::default(),
            diagnostics: Vec::new(),
        })
    }

    fn submodule(name: &str, exports: &[&str]) -> ModuleIndex {
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
            import_bindings: Vec::new(),
        }
    }

    fn library(packages: &[Arc<PackageIndex>]) -> BTreeMap<String, Arc<PackageIndex>> {
        packages
            .iter()
            .map(|p| (p.name.clone(), Arc::clone(p)))
            .collect()
    }

    /// The offset just past the last occurrence of `needle` in `src`.
    fn after(src: &str, needle: &str) -> TextSize {
        TextSize::from((src.rfind(needle).unwrap() + needle.len()) as u32)
    }

    fn resolve(src: &str, name: &str, lib: &BTreeMap<String, Arc<PackageIndex>>) -> Resolution {
        let model = model_of(src);
        let offset = after(src, name);
        Resolver::new(&model, lib).resolve(name, offset, Namespace::Value)
    }

    #[test]
    fn local_binding_wins_over_everything() {
        let lib = library(&[package("Base", &["x"]), package("A", &["x"])]);
        let src = "using A\nfunction f()\n    x = 1\n    x\nend";
        let model = model_of(src);
        let offset = after(src, "    x");
        match Resolver::new(&model, &lib).resolve("x", offset, Namespace::Value) {
            Resolution::Binding(b) => {
                assert_eq!(model.binding(b).kind, BindingKind::Local);
            }
            other => panic!("expected the local binding, got {other:?}"),
        }
    }

    #[test]
    fn explicit_import_wins_over_using_and_base() {
        let lib = library(&[package("Base", &["f"]), package("A", &["f"])]);
        let src = "using A\nimport B: f\nf()";
        match resolve(src, "f", &lib) {
            Resolution::Binding(b) => {
                let model = model_of(src);
                assert_eq!(model.binding(b).kind, BindingKind::Import);
            }
            other => panic!("expected the explicit import, got {other:?}"),
        }
    }

    #[test]
    fn using_export_resolves_when_not_bound() {
        let lib = library(&[package("A", &["greet"])]);
        let src = "using A\ngreet()";
        assert_eq!(
            resolve(src, "greet", &lib),
            Resolution::Using {
                module: SmolStr::new("A"),
                name: SmolStr::new("greet"),
            }
        );
    }

    #[test]
    fn using_distinguishes_conflicting_exports_from_proven_reexports() {
        let lib = library(&[
            harvested_package(
                "A",
                "export f, x\nf() = 1\nconst x = 1
",
            ),
            harvested_package(
                "B",
                "export f, x\nf() = 2\nconst x = 1
",
            ),
            harvested_package(
                "Same",
                "using A: f\nexport f
",
            ),
            harvested_package(
                "Extend",
                "import A: f\nf(x) = x\nexport f
",
            ),
            harvested_package(
                "ConstAlias",
                "import A\nconst f = A.f\nexport f
",
            ),
        ]);
        for src in ["using A, B\nf()", "using B, A\nf()", "using A, A, B\nf()"] {
            assert_eq!(resolve(src, "f", &lib), Resolution::Ambiguous, "{src}");
            let model = model_of(src);
            let offset = after(src, "f");
            let resolver = Resolver::new(&model, &lib);
            assert!(
                !resolver
                    .visible(offset, Namespace::Value)
                    .iter()
                    .any(|c| c.name == "f"),
                "{src}"
            );
        }
        for src in [
            "using A, Same\nf()",
            "using Same, A\nf()",
            "using A, Extend\nf()",
            "using Extend, A\nf()",
            "using A, ConstAlias\nf()",
        ] {
            assert!(
                matches!(resolve(src, "f", &lib), Resolution::Using { .. }),
                "{src}"
            );
            let model = model_of(src);
            let offset = after(src, "f");
            assert!(
                Resolver::new(&model, &lib)
                    .visible(offset, Namespace::Value)
                    .iter()
                    .any(|c| c.name == "f"),
                "{src}"
            );
        }
        assert!(matches!(
            resolve("using A, B\nx", "x", &lib),
            Resolution::Using { .. }
        ));
        assert!(matches!(
            resolve("using A, B\nimport A: f\nf()", "f", &lib),
            Resolution::Binding(_)
        ));
    }

    #[test]
    fn using_detects_conflicts_with_an_indexed_sibling_import() {
        let a = harvested_package(
            "A",
            "export f\nf() = 1
",
        );
        let b = harvested_package(
            "B",
            "export f\nf() = 2
",
        );
        let ws = harvested_package(
            "Root", "using B
",
        );
        let lib = library(&[a, b]);
        let src = "using A\nf()";
        let model = model_of(src);
        let resolver = Resolver::new(&model, &lib).with_workspace(Some((ws, vec![])));
        assert_eq!(
            resolver.resolve("f", after(src, "f"), Namespace::Value),
            Resolution::Ambiguous
        );
    }

    #[test]
    fn using_export_masks_base() {
        let lib = library(&[package("Base", &["map"]), package("A", &["map"])]);
        let src = "using A\nmap()";
        assert_eq!(
            resolve(src, "map", &lib),
            Resolution::Using {
                module: SmolStr::new("A"),
                name: SmolStr::new("map"),
            }
        );
    }

    #[test]
    fn export_lookup_sees_names_masked_by_constructor_bindings() {
        let lib = library(&[
            package("Base", &["BaseType"]),
            package("Core", &["CoreType"]),
            module_package("A", &[], vec![submodule("B", &["UsedType"])]),
        ]);
        let src = "using A.B\nBaseType(x) = x\nCoreType(x) = x\nUsedType(x) = x\n\
                   helper(x) = x\nf(::BaseType, ::CoreType, ::UsedType, ::helper) = 1\n";
        let model = model_of(src);
        let resolver = Resolver::new(&model, &lib);
        for (name, module) in [
            ("BaseType", Some("Base")),
            ("CoreType", Some("Core")),
            ("UsedType", Some("A.B")),
            ("helper", None),
        ] {
            let offset = after(src, name);
            assert!(matches!(
                resolver.resolve(name, offset, Namespace::Value),
                Resolution::Binding(_)
            ));
            assert_eq!(
                resolver.export_module_providing(name, offset, Namespace::Value),
                module.map(SmolStr::new),
                "{name}"
            );
        }
    }

    #[test]
    fn export_lookup_respects_using_scope() {
        let lib = library(&[package("A", &["Helper"])]);
        let src = "module M\nusing A\nf(::Helper) = 1\nend\ng(::Helper) = 2\n";
        let model = model_of(src);
        let resolver = Resolver::new(&model, &lib);
        assert_eq!(
            resolver.export_module_providing("Helper", after(src, "f(::Helper"), Namespace::Value),
            Some(SmolStr::new("A"))
        );
        assert_eq!(
            resolver.export_module_providing("Helper", after(src, "g(::Helper"), Namespace::Value),
            None
        );
    }

    #[test]
    fn workspace_constructor_groups_preserve_imported_type_identity() {
        for declaration in ["abstract type Animal end", "const Animal = Vector{Int}"] {
            for (provider, load, module_path, nested) in [
                ("Creatures", "using Creatures\n", "Creatures", false),
                (
                    "Creatures",
                    "using Creatures.Types\n",
                    "Creatures.Types",
                    true,
                ),
                ("Base", "", "Base", false),
                ("Core", "", "Core", false),
            ] {
                let source = format!("export Animal\n{declaration}\n");
                let source = if nested {
                    format!("module Types\n{source}end\n")
                } else {
                    source
                };
                let mut lib = library(&[package("Base", &[]), package("Core", &[])]);
                lib.insert(provider.into(), harvested_package(provider, &source));
                let workspace = harvested_package(
                    "MyPkg",
                    &format!("{load}for op in (:Animal,)\n    @eval ($op)(x::Int) = x\nend\n"),
                );
                let src = "struct Dog <: Animal end\n";
                let model = model_of(src);
                let offset = after(src, "Animal");
                let resolver =
                    Resolver::new(&model, &lib).with_workspace(Some((workspace, Vec::new())));
                let expected = if load.is_empty() {
                    Resolution::System {
                        module: module_path.into(),
                        name: "Animal".into(),
                    }
                } else {
                    Resolution::Using {
                        module: module_path.into(),
                        name: "Animal".into(),
                    }
                };
                assert_eq!(
                    resolver.resolve("Animal", offset, Namespace::Value),
                    expected,
                    "{provider}, {load}, {declaration}"
                );
                let candidate = resolver
                    .visible(offset, Namespace::Value)
                    .into_iter()
                    .find(|candidate| candidate.name == "Animal")
                    .unwrap();
                let expected = if load.is_empty() {
                    Source::System {
                        module: module_path.into(),
                    }
                } else {
                    Source::Using {
                        module: module_path.rsplit('.').next().unwrap().into(),
                    }
                };
                assert_eq!(candidate.source, expected);
                assert!(resolver.workspace_symbol_at(offset).is_none());
            }
        }
    }

    #[test]
    fn workspace_declarations_still_mask_exported_constructor_names() {
        for (exported, local) in [
            ("abstract type Animal end", "struct Animal end"),
            ("abstract type Animal end", "const Animal = Vector{Int}"),
            ("Animal(x) = x", ""),
        ] {
            let lib = library(&[harvested_package(
                "Creatures",
                &format!("export Animal\n{exported}\n"),
            )]);
            let workspace = harvested_package(
                "MyPkg",
                &format!(
                    "using Creatures\n{local}\n\
                     for op in (:Animal,)\n    @eval ($op)(x::Int) = x\nend\n"
                ),
            );
            let src = "Animal(1)";
            let model = model_of(src);
            let offset = after(src, "Animal");
            let resolver =
                Resolver::new(&model, &lib).with_workspace(Some((workspace, Vec::new())));
            assert_eq!(
                resolver.resolve("Animal", offset, Namespace::Value),
                Resolution::Workspace {
                    module: Vec::new(),
                    name: "Animal".into(),
                },
                "{exported}, {local}"
            );
            let candidates: Vec<_> = resolver
                .visible(offset, Namespace::Value)
                .into_iter()
                .filter(|candidate| candidate.name == "Animal")
                .collect();
            assert_eq!(candidates.len(), 1);
            assert_eq!(
                candidates[0].source,
                Source::Workspace {
                    module: "MyPkg".into()
                }
            );
        }
    }

    #[test]
    fn workspace_functions_shadow_exported_types_and_constants() {
        for exported in ["abstract type Animal end", "const Animal = 1"] {
            for declaration in ["Animal(x) = x", "function Animal end"] {
                for generated in [
                    "",
                    "for op in (:Animal,)\n    @eval ($op)(x::Int) = x\nend\n",
                ] {
                    let lib = library(&[harvested_package(
                        "Creatures",
                        &format!("export Animal\n{exported}\n"),
                    )]);
                    let source = format!("using Creatures\n{declaration}\n{generated}Animal(1)\n");
                    let workspace = harvested_package("MyPkg", &source);
                    let caller = "Animal(1)";
                    for src in [&source[..], caller] {
                        let model = model_of(src);
                        let resolver = Resolver::new(&model, &lib)
                            .with_workspace(Some((Arc::clone(&workspace), Vec::new())));
                        let offset = after(src, "Animal");
                        if src == caller {
                            assert_eq!(
                                resolver.resolve("Animal", offset, Namespace::Value),
                                Resolution::Workspace {
                                    module: Vec::new(),
                                    name: "Animal".into(),
                                },
                                "{exported}, {declaration}, {generated}"
                            );
                            let candidate = resolver
                                .visible(offset, Namespace::Value)
                                .into_iter()
                                .find(|candidate| candidate.name == "Animal")
                                .unwrap();
                            assert!(matches!(candidate.source, Source::Workspace { .. }));
                        }
                        let symbol = resolver.workspace_symbol_at(offset).unwrap();
                        assert_eq!(symbol.name, "Animal");
                        let occurrences = resolver.workspace_occurrences();
                        let occurrences = &occurrences[&symbol];
                        assert!(occurrences.iter().any(|occ| !occ.is_def));
                        assert_eq!(occurrences.iter().any(|occ| occ.is_def), src != caller);
                    }
                }
            }
        }
    }

    #[test]
    fn sibling_nested_using_keeps_the_provider_path() {
        let lib = library(&[harvested_package(
            "Creatures",
            "module Types\nexport Animal\nabstract type Animal end\nend\n",
        )]);
        for constructor in [
            "",
            "for op in (:Animal,)\n    @eval ($op)(x::Int) = x\nend\n",
        ] {
            let workspace =
                harvested_package("MyPkg", &format!("using Creatures.Types\n{constructor}"));
            let src = "Animal(1)";
            let model = model_of(src);
            let resolver =
                Resolver::new(&model, &lib).with_workspace(Some((workspace, Vec::new())));
            assert_eq!(
                resolver.resolve("Animal", after(src, "Animal"), Namespace::Value),
                Resolution::Using {
                    module: "Creatures.Types".into(),
                    name: "Animal".into(),
                }
            );
        }
    }

    #[test]
    fn module_binds_its_own_name_but_not_an_ancestors() {
        // Julia scopes a module's own name inside it (`Outer` within module
        // `Outer`), but a nested submodule does not see its parent's name. The
        // workspace tier must resolve exactly the enclosing module's own name.
        let pkg = module_package("Outer", &[], vec![submodule("Inner", &[])]);
        let lib = library(&[]);
        let resolve_at = |src: &str, name: &str, host: ModulePath| {
            let model = model_of(src);
            let offset = after(src, name);
            Resolver::new(&model, &lib)
                .with_workspace(Some((Arc::clone(&pkg), host)))
                .resolve(name, offset, Namespace::Value)
        };

        // The root module's own name resolves.
        assert_eq!(
            resolve_at("Outer\n", "Outer", Vec::new()),
            Resolution::Workspace {
                module: Vec::new(),
                name: SmolStr::new("Outer"),
            }
        );
        // Inside the nested module, its own name resolves.
        assert_eq!(
            resolve_at("Inner\n", "Inner", vec![SmolStr::new("Inner")]),
            Resolution::Workspace {
                module: vec![SmolStr::new("Inner")],
                name: SmolStr::new("Inner"),
            }
        );
        // But the parent's name does not (Julia raises `UndefVarError`).
        assert_eq!(
            resolve_at("Outer\n", "Outer", vec![SmolStr::new("Inner")]),
            Resolution::Unresolved
        );
    }

    #[test]
    fn earliest_using_wins_in_source_order() {
        let lib = library(&[package("A", &["dup"]), package("B", &["dup"])]);
        let src = "using B\nusing A\ndup()";
        // `using B` is written first, so it wins.
        assert_eq!(
            resolve(src, "dup", &lib),
            Resolution::Using {
                module: SmolStr::new("B"),
                name: SmolStr::new("dup"),
            }
        );
    }

    #[test]
    fn base_implicit_resolves_without_a_using() {
        let lib = library(&[package("Base", &["println"])]);
        let src = "println()";
        assert_eq!(
            resolve(src, "println", &lib),
            Resolution::System {
                module: SmolStr::new("Base"),
                name: SmolStr::new("println"),
            }
        );
    }

    #[test]
    fn unknown_name_is_unresolved() {
        let lib = library(&[package("Base", &["println"])]);
        assert_eq!(resolve("nope()", "nope", &lib), Resolution::Unresolved);
    }

    #[test]
    fn qualified_name_existence_distinguishes_missing_from_unknown_packages() {
        let lib = library(&[
            package("Base", &["println", "@time"]),
            module_package("A", &[], vec![submodule("B", &["item"])]),
        ]);
        let model = model_of("");
        let resolver = Resolver::new(&model, &lib);
        let path = |parts: &[&str]| parts.iter().map(SmolStr::new).collect::<Vec<_>>();

        assert_eq!(
            resolver.qualified_name_exists(&path(&["Base", "println"]), Namespace::Value),
            Some(true)
        );
        assert_eq!(
            resolver.qualified_name_exists(&path(&["Base", "@time"]), Namespace::Macro),
            Some(true)
        );
        assert_eq!(
            resolver.qualified_name_exists(&path(&["A", "B", "item"]), Namespace::Value),
            Some(true)
        );
        assert_eq!(
            resolver.qualified_name_exists(&path(&["A", "B", "absent"]), Namespace::Value),
            Some(false)
        );
        assert_eq!(
            resolver.qualified_name_exists(&path(&["Unknown", "item"]), Namespace::Value),
            None
        );
    }

    #[test]
    fn item_using_does_not_bring_whole_module_exports() {
        // `using A: only` binds `only`; a sibling export `other` stays free.
        let lib = library(&[package("A", &["only", "other"])]);
        let src = "using A: only\nother()";
        assert_eq!(resolve(src, "other", &lib), Resolution::Unresolved);
    }

    #[test]
    fn import_does_not_bring_exports() {
        let lib = library(&[package("A", &["thing"])]);
        let src = "import A\nthing()";
        assert_eq!(resolve(src, "thing", &lib), Resolution::Unresolved);
    }

    #[test]
    fn using_submodule_resolves_its_exports() {
        let lib = library(&[module_package("A", &[], vec![submodule("B", &["inner"])])]);
        let src = "using A.B\ninner()";
        assert_eq!(
            resolve(src, "inner", &lib),
            Resolution::Using {
                module: SmolStr::new("A.B"),
                name: SmolStr::new("inner"),
            }
        );
    }

    #[test]
    fn using_in_module_does_not_leak_to_file_scope() {
        let lib = library(&[package("A", &["helper"])]);
        let src = "module M\nusing A\nend\nhelper()";
        assert_eq!(resolve(src, "helper", &lib), Resolution::Unresolved);
    }

    #[test]
    fn file_using_does_not_reach_into_a_module_body() {
        let lib = library(&[package("A", &["helper"])]);
        let src = "using A\nmodule M\nhelper()\nend";
        let model = model_of(src);
        let offset = after(src, "helper");
        assert_eq!(
            Resolver::new(&model, &lib).resolve("helper", offset, Namespace::Value),
            Resolution::Unresolved,
            "a top-level `using` does not apply inside a nested module"
        );
    }

    #[test]
    fn relative_using_is_not_resolved_against_the_library() {
        let lib = library(&[package("A", &["thing"])]);
        let src = "using .A\nthing()";
        assert_eq!(resolve(src, "thing", &lib), Resolution::Unresolved);
    }

    #[test]
    fn macro_resolves_in_the_macro_namespace() {
        let lib = library(&[package("Base", &["@time"])]);
        let src = "@time f()";
        let model = model_of(src);
        let offset = after(src, "@time");
        assert_eq!(
            Resolver::new(&model, &lib).resolve("time", offset, Namespace::Macro),
            Resolution::System {
                module: SmolStr::new("Base"),
                name: SmolStr::new("@time"),
            }
        );
    }

    #[test]
    fn value_and_macro_namespaces_do_not_cross() {
        let lib = library(&[package("Base", &["@time", "time"])]);
        let src = "time\n@time f()";
        let model = model_of(src);
        // The value `time` must not resolve via the macro export and vice versa.
        let value_off = after(src, "time\n");
        assert!(matches!(
            Resolver::new(&model, &lib).resolve("time", value_off, Namespace::Value),
            Resolution::System { name, .. } if name == "time"
        ));
    }

    #[test]
    fn imported_macro_binding_wins_for_macro_reads() {
        let lib = library(&[package("Base", &["@time"])]);
        let src = "using X: @time\n@time f()";
        let model = model_of(src);
        let offset = after(src, "@time f");
        match Resolver::new(&model, &lib).resolve("time", offset, Namespace::Macro) {
            Resolution::Binding(b) => assert_eq!(model.binding(b).kind, BindingKind::Import),
            other => panic!("expected the imported macro binding, got {other:?}"),
        }
    }

    // --- workspace tier (same-module cross-file siblings) ------------------

    /// A package whose root module defines value symbols `functions` and macro
    /// symbols `macros` (each `@name`), none of them exported — the shape of a
    /// package's own top-level globals a sibling file sees.
    fn workspace_pkg(name: &str, functions: &[&str], macros: &[&str]) -> Arc<PackageIndex> {
        use crate::index::model::{FunctionGroup, MacroDef};
        let mut pkg = (*package(name, &[])).clone();
        pkg.root.functions = functions
            .iter()
            .map(|f| FunctionGroup {
                name: f.to_string(),
                owner: None,
                methods: Vec::new(),
                doc: None,
            })
            .collect();
        pkg.root.macros = macros
            .iter()
            .map(|m| MacroDef {
                name: m.to_string(),
                params: Vec::new(),
                doc: None,
                loc: loc(),
            })
            .collect();
        Arc::new(pkg)
    }

    fn resolve_ws(
        src: &str,
        name: &str,
        lib: &BTreeMap<String, Arc<PackageIndex>>,
        workspace: Option<Arc<PackageIndex>>,
    ) -> Resolution {
        let model = model_of(src);
        let offset = after(src, name);
        Resolver::new(&model, lib)
            .with_workspace(workspace.map(|w| (w, Vec::new())))
            .resolve(name, offset, Namespace::Value)
    }

    /// A workspace package whose root module records the whole-module `using`
    /// paths `usings` and the module-level bound names `imported` — the load
    /// surface a sibling file's `include` splices into the module.
    fn workspace_pkg_loads(name: &str, usings: &[&[&str]], imported: &[&str]) -> Arc<PackageIndex> {
        let mut pkg = (*package(name, &[])).clone();
        pkg.root.usings = usings
            .iter()
            .map(|components| ModuleUsing {
                leading_dots: 0,
                components: components.iter().map(|c| c.to_string()).collect(),
            })
            .collect();
        pkg.root.imported_names = imported.iter().map(|n| n.to_string()).collect();
        Arc::new(pkg)
    }

    #[test]
    fn sibling_using_export_resolves() {
        // A sibling file's `using SparseArrays` opens its exports module-wide,
        // so `SparseMatrixCSC` resolves here as a `using`'d name (SLOPE.jl's
        // `cv.jl` reading a symbol a sibling `models.jl` `using`s in).
        let ws = workspace_pkg_loads("MyPkg", &[&["SparseArrays"]], &[]);
        let lib = library(&[package("SparseArrays", &["SparseMatrixCSC"])]);
        assert_eq!(
            resolve_ws(
                "f(::SparseMatrixCSC) = 1",
                "SparseMatrixCSC",
                &lib,
                Some(ws)
            ),
            Resolution::Using {
                module: SmolStr::new("SparseArrays"),
                name: SmolStr::new("SparseMatrixCSC"),
            }
        );
    }

    #[test]
    fn sibling_imported_name_resolves() {
        // Names a sibling's `import Foo` / `using Bar: baz` binds are module
        // globals here, resolving to the workspace-import tier.
        let ws = workspace_pkg_loads("MyPkg", &[], &["Foo", "baz"]);
        let lib = library(&[package("Base", &[])]);
        assert_eq!(
            resolve_ws("g() = Foo.thing()", "Foo", &lib, Some(ws.clone())),
            Resolution::WorkspaceImport {
                name: SmolStr::new("Foo")
            }
        );
        assert_eq!(
            resolve_ws("g() = baz()", "baz", &lib, Some(ws)),
            Resolution::WorkspaceImport {
                name: SmolStr::new("baz")
            }
        );
    }

    #[test]
    fn unresolvable_sibling_using_does_not_resolve() {
        // The sibling `using` targets an unharvested package, so no export
        // surface is known: the name stays unresolved (the file-level gate is
        // what suppresses a diagnostic, not the resolver).
        let ws = workspace_pkg_loads("MyPkg", &[&["Unharvested"]], &[]);
        let lib = library(&[package("Base", &[])]);
        assert_eq!(
            resolve_ws("f() = mystery()", "mystery", &lib, Some(ws)),
            Resolution::Unresolved
        );
    }

    #[test]
    fn sibling_import_is_not_a_workspace_occurrence() {
        // A workspace-import read must not enter the reverse-occurrence index:
        // its definition is the sibling's `import` site, not a package symbol.
        let ws = workspace_pkg_loads("MyPkg", &[], &["Foo"]);
        let model = model_of("g() = Foo.thing()");
        let lib = library(&[package("Base", &[])]);
        let occ = Resolver::new(&model, &lib)
            .with_workspace(Some((ws, Vec::new())))
            .workspace_occurrences();
        assert!(occ.is_empty(), "{occ:?}");
    }

    #[test]
    fn nested_module_using_resolves_only_inside_that_module() {
        // A `using` harvested into a nested `module Sub` opens its exports for
        // reads inside `Sub`, but not at the package root.
        let mut pkg = (*package("MyPkg", &[])).clone();
        pkg.root.submodules.push(submodule("Sub", &[]));
        pkg.root.submodules[0].usings.push(ModuleUsing {
            leading_dots: 0,
            components: vec!["SubDep".to_string()],
        });
        let ws = Arc::new(pkg);
        let lib = library(&[package("SubDep", &["helper"])]);

        // Inside `module Sub`, the read resolves through Sub's `using`.
        let src = "module Sub\nhelper()\nend";
        let model = model_of(src);
        let offset = after(src, "helper");
        assert_eq!(
            Resolver::new(&model, &lib)
                .with_workspace(Some((Arc::clone(&ws), Vec::new())))
                .resolve("helper", offset, Namespace::Value),
            Resolution::Using {
                module: SmolStr::new("SubDep"),
                name: SmolStr::new("helper"),
            }
        );
        // At the root, Sub's `using` is invisible.
        assert_eq!(
            resolve_ws("helper()", "helper", &lib, Some(ws)),
            Resolution::Unresolved
        );
    }

    #[test]
    fn has_unresolvable_using_gates_on_sibling_usings() {
        // With no using in this file, an unresolvable whole-module `using` in
        // the host module (a sibling file's) still bails the file.
        let model = model_of("f() = 1");
        let lib: BTreeMap<String, Arc<PackageIndex>> = library(&[package("Base", &[])]);
        let unresolvable = workspace_pkg_loads("MyPkg", &[&["Unharvested"]], &[]);
        let ws = (unresolvable, Vec::new());
        assert!(has_unresolvable_using(&model, &lib, Some(&ws)));

        // A resolvable sibling `using` does not gate.
        let resolvable = workspace_pkg_loads("MyPkg", &[&["SparseArrays"]], &[]);
        let lib2 = library(&[package("SparseArrays", &["SparseMatrixCSC"])]);
        let ws2 = (resolvable, Vec::new());
        assert!(!has_unresolvable_using(&model, &lib2, Some(&ws2)));
    }

    #[test]
    fn workspace_sibling_resolves_when_free() {
        // `bar` is defined in a sibling file (harvested into the workspace
        // package), not in this file: it resolves as a workspace symbol.
        let ws = workspace_pkg("MyPkg", &["bar"], &[]);
        let lib = library(&[package("Base", &[])]);
        assert_eq!(
            resolve_ws("bar()", "bar", &lib, Some(ws)),
            Resolution::Workspace {
                module: Vec::new(),
                name: SmolStr::new("bar")
            }
        );
    }

    #[test]
    fn workspace_sibling_masks_using_and_base() {
        // A same-module global outranks both a `using`'d export and Base.
        let ws = workspace_pkg("MyPkg", &["dup"], &[]);
        let lib = library(&[package("Base", &["dup"]), package("A", &["dup"])]);
        assert_eq!(
            resolve_ws("using A\ndup()", "dup", &lib, Some(ws)),
            Resolution::Workspace {
                module: Vec::new(),
                name: SmolStr::new("dup")
            }
        );
    }

    #[test]
    fn local_binding_still_wins_over_workspace() {
        // A shadowing local must not be captured by the workspace tier.
        let ws = workspace_pkg("MyPkg", &["x"], &[]);
        let lib = library(&[package("Base", &[])]);
        let src = "function f()\n    x = 1\n    x\nend";
        let model = model_of(src);
        let offset = after(src, "    x");
        match Resolver::new(&model, &lib)
            .with_workspace(Some((ws, Vec::new())))
            .resolve("x", offset, Namespace::Value)
        {
            Resolution::Binding(b) => assert_eq!(model.binding(b).kind, BindingKind::Local),
            other => panic!("expected the local binding, got {other:?}"),
        }
    }

    #[test]
    fn workspace_macro_resolves_in_macro_namespace() {
        let ws = workspace_pkg("MyPkg", &[], &["@sib"]);
        let lib = library(&[package("Base", &[])]);
        let src = "@sib f()";
        let model = model_of(src);
        let offset = after(src, "@sib");
        assert_eq!(
            Resolver::new(&model, &lib)
                .with_workspace(Some((ws, Vec::new())))
                .resolve("sib", offset, Namespace::Macro),
            Resolution::Workspace {
                module: Vec::new(),
                name: SmolStr::new("@sib")
            }
        );
    }

    #[test]
    fn workspace_names_appear_in_completion_between_locals_and_using() {
        let ws = workspace_pkg("MyPkg", &["sibling"], &[]);
        let lib = library(&[package("Base", &["println"]), package("A", &["greet"])]);
        let src = "using A\nfunction f(a)\n    b = 1\n    \nend";
        let model = model_of(src);
        let offset = after(src, "b = 1\n    ");
        let names: Vec<String> = Resolver::new(&model, &lib)
            .with_workspace(Some((ws, Vec::new())))
            .visible(offset, Namespace::Value)
            .into_iter()
            .map(|c| c.name.to_string())
            .collect();
        assert!(names.contains(&"sibling".to_string()), "{names:?}");
        // Ordering: local `b` < workspace `sibling` < using `greet` < Base.
        let pos = |n: &str| names.iter().position(|x| x == n).unwrap();
        assert!(pos("b") < pos("sibling"));
        assert!(pos("sibling") < pos("greet"));
        assert!(pos("greet") < pos("println"));
    }

    // --- completion enumeration --------------------------------------------

    fn visible_names(
        src: &str,
        needle: &str,
        lib: &BTreeMap<String, Arc<PackageIndex>>,
    ) -> Vec<String> {
        let model = model_of(src);
        let offset = after(src, needle);
        Resolver::new(&model, lib)
            .visible(offset, Namespace::Value)
            .into_iter()
            .map(|c| c.name.to_string())
            .collect()
    }

    #[test]
    fn visible_lists_all_tiers_in_masking_order() {
        let lib = library(&[package("Base", &["println"]), package("A", &["greet"])]);
        let src = "using A\nfunction f(a)\n    b = 1\n    \nend";
        let names = visible_names(src, "b = 1\n    ", &lib);
        for expected in ["a", "b", "f", "greet", "println"] {
            assert!(
                names.contains(&expected.to_string()),
                "missing {expected} in {names:?}"
            );
        }
        // Local scope names precede library names.
        assert!(names.iter().position(|n| n == "b") < names.iter().position(|n| n == "greet"));
        assert!(
            names.iter().position(|n| n == "greet") < names.iter().position(|n| n == "println")
        );
    }

    #[test]
    fn visible_drops_shadowed_names() {
        // A local `map` masks Base's `map`: `map` appears once, as the local.
        let lib = library(&[package("Base", &["map"])]);
        let src = "function f()\n    map = 1\n    \nend";
        let names = visible_names(src, "map = 1\n    ", &lib);
        assert_eq!(names.iter().filter(|n| *n == "map").count(), 1);
    }

    #[test]
    fn occurrence_keys_carry_the_dev_package() {
        // Two dev packages (two workspace folders) each define a root-level
        // `f`; the same source resolved as a member of each must yield keys
        // that differ in `package`, or the shared reverse index would bleed
        // references across folders.
        let src = "function f()\n    f()\nend\n";
        let model = model_of(src);
        let lib = library(&[]);
        let key_in = |pkg_name: &str| -> OccurrenceKey {
            let ws = workspace_pkg(pkg_name, &["f"], &[]);
            let keys: Vec<OccurrenceKey> = Resolver::new(&model, &lib)
                .with_workspace(Some((ws, Vec::new())))
                .workspace_occurrences()
                .into_keys()
                .collect();
            assert_eq!(keys.len(), 1, "one bucket for `f` in {pkg_name}");
            keys.into_iter().next().unwrap()
        };
        let a = key_in("PkgA");
        let b = key_in("PkgB");
        assert_eq!(a.package.as_str(), "PkgA");
        assert_eq!(b.package.as_str(), "PkgB");
        assert_eq!(
            (a.module.clone(), a.namespace, a.name.clone()),
            (b.module.clone(), b.namespace, b.name.clone())
        );
        assert_ne!(a, b, "same symbol shape, different package, distinct keys");
    }

    /// A flattened occurrence bucket: `(start, end, is_def)` per site, keyed by
    /// namespace and name.
    type OccMap = BTreeMap<(Namespace, SmolStr), Vec<(u32, u32, bool)>>;

    /// The occurrences keyed by `(namespace, name)` for `src`, resolved as a
    /// member of `workspace` against `lib`.
    fn workspace_occ(
        src: &str,
        workspace: &Arc<PackageIndex>,
        lib: &BTreeMap<String, Arc<PackageIndex>>,
    ) -> OccMap {
        let model = model_of(src);
        Resolver::new(&model, lib)
            .with_workspace(Some((Arc::clone(workspace), Vec::new())))
            .workspace_occurrences()
            .into_iter()
            .map(|(key, recs)| {
                let simple = recs
                    .iter()
                    .map(|r| (r.range.start().into(), r.range.end().into(), r.is_def))
                    .collect();
                ((key.namespace, key.name), simple)
            })
            .collect()
    }

    #[test]
    fn defining_file_reports_its_module_global() {
        // The file defines `f`; the def site plus the intra-file use are recorded.
        let ws = workspace_pkg("MyPkg", &["f"], &[]);
        let src = "function f()\n    f()\nend\n";
        let occ = workspace_occ(src, &ws, &library(&[]));
        let recs = occ
            .get(&(Namespace::Value, SmolStr::new("f")))
            .expect("f is a workspace symbol");
        // The definition (is_def) and the recursive call.
        assert_eq!(recs.len(), 2);
        assert!(recs.iter().any(|r| r.2), "the definition site is present");
        assert!(recs.iter().any(|r| !r.2), "the intra-file use is present");
    }

    #[test]
    fn using_file_reports_free_reads_of_a_workspace_symbol() {
        // This file does not define `f`, only calls it: a free read resolving to
        // the workspace tier, recorded as a non-def use.
        let ws = workspace_pkg("MyPkg", &["f"], &[]);
        let src = "g() = f() + f()\n";
        let occ = workspace_occ(src, &ws, &library(&[]));
        let recs = occ
            .get(&(Namespace::Value, SmolStr::new("f")))
            .expect("f resolves to the workspace");
        assert_eq!(recs.len(), 2, "both calls to f");
        assert!(recs.iter().all(|r| !r.2), "uses, not definitions");
    }

    #[test]
    fn a_shadowing_local_is_not_a_workspace_occurrence() {
        // A local `f` masks the workspace symbol: its uses bind locally and are
        // not reported as references to the package-level `f`.
        let ws = workspace_pkg("MyPkg", &["f"], &[]);
        let src = "function g()\n    f = 1\n    f + f\nend\n";
        let occ = workspace_occ(src, &ws, &library(&[]));
        assert!(
            !occ.contains_key(&(Namespace::Value, SmolStr::new("f"))),
            "the local f shadows the workspace symbol"
        );
    }

    #[test]
    fn non_member_file_reports_nothing() {
        // With no workspace set, nothing is a workspace occurrence.
        let model = model_of("f() = f()\n");
        let lib = library(&[]);
        let occ = Resolver::new(&model, &lib).workspace_occurrences();
        assert!(occ.is_empty());
    }

    #[test]
    fn macro_occurrences_use_the_macro_namespace() {
        let ws = workspace_pkg("MyPkg", &[], &["@m"]);
        // Defining file: `macro m() end` binds `m` in the macro namespace.
        let occ = workspace_occ("macro m()\nend\n", &ws, &library(&[]));
        assert!(occ.contains_key(&(Namespace::Macro, SmolStr::new("@m"))));
        // Using file: an `@m` free read resolves to the workspace macro.
        let occ2 = workspace_occ("f() = @m\n", &ws, &library(&[]));
        assert!(occ2.contains_key(&(Namespace::Macro, SmolStr::new("@m"))));
    }

    #[test]
    fn a_plain_global_is_not_a_workspace_occurrence() {
        // `x = 1` is a file-scope global, but the package does not define `x` at
        // top level (the harvester skips plain globals), so it stays intra-file.
        let ws = workspace_pkg("MyPkg", &["f"], &[]);
        let src = "x = 1\nf() = x\n";
        let occ = workspace_occ(src, &ws, &library(&[]));
        assert!(!occ.contains_key(&(Namespace::Value, SmolStr::new("x"))));
        assert!(occ.contains_key(&(Namespace::Value, SmolStr::new("f"))));
    }
}
