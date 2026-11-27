//! Keyword name completion for the direct semicolon-delimited argument slots of
//! ordinary calls. No keyword suggestions come from a nested value expression.

use std::{collections::BTreeSet, sync::Arc};

use lsp_types::{CompletionItem, CompletionItemKind, CompletionTextEdit, TextEdit};
use rowan::{TextRange, TextSize};
use smol_str::SmolStr;

use crate::ast::{AstNode, AstToken, CallExpr, Expr, HasArgList, KeywordArg, Parameters};
use crate::index::{PackageIndex, Param, harvest::extract_params};
use crate::parser::{is_ident_continue, is_ident_start};
use crate::resolve::{
    ModulePath, Namespace, PackageSource, QualifiedMember, Resolution, Resolver, module_at,
};
use crate::semantic::{Access, BindingId, BindingKind, SemanticModel};
use crate::syntax::{SyntaxKind, SyntaxNode};
use crate::text::{LineIndex, PositionEncoding};

pub(super) struct Site {
    call: CallExpr,
    edit: TextRange,
    // If '=' is present, whether it directly touches the edited name.
    existing_eq: Option<bool>,
    used: BTreeSet<String>,
}

pub(super) fn site_at(root: &SyntaxNode, offset: TextSize) -> Option<Site> {
    let at = root.token_at_offset(offset);
    let left = at.clone().left_biased();
    let right = at.right_biased();
    if [left.as_ref(), right.as_ref()]
        .into_iter()
        .flatten()
        .any(|t| {
            matches!(t.kind(), SyntaxKind::COMMENT | SyntaxKind::BLOCK_COMMENT)
                && t.text_range().start() < offset
                && offset <= t.text_range().end()
        })
    {
        return None;
    }
    let parameters = left
        .into_iter()
        .chain(right)
        .flat_map(|t| t.parent_ancestors())
        .find_map(|node| {
            let params = Parameters::cast(node)?;
            params
                .syntax()
                .text_range()
                .contains_inclusive(offset)
                .then_some(params)
        })?;
    let arg_list = parameters.syntax().parent()?;
    let call = CallExpr::cast(arg_list.parent()?)?;
    let args = call.arg_list()?;
    if args.syntax() != &arg_list || is_signature(&call) {
        return None;
    }

    let mut slot = None;
    let mut after_separator = false;
    let mut before_next_separator = true;
    let mut used: BTreeSet<String> = args
        .keyword_args()
        .filter_map(|arg| arg.name()?.ident().map(|name| name.text().to_string()))
        .collect();
    for el in parameters.syntax().children_with_tokens() {
        let range = el.text_range();
        let Some(node) = el.as_node() else {
            if matches!(el.kind(), SyntaxKind::SEMICOLON | SyntaxKind::COMMA) {
                if range.end() <= offset {
                    after_separator = true;
                } else {
                    before_next_separator = false;
                }
            }
            continue;
        };
        let keyword = KeywordArg::cast(node.clone());
        let expr = crate::ast::Arg::cast(node.clone()).and_then(|arg| arg.expr());
        let name = keyword
            .as_ref()
            .and_then(|kw| kw.name())
            .and_then(|name| name.ident())
            .or_else(|| expr.as_ref().and_then(Expr::name_ident));
        if let Some(name) = &name
            && name.syntax().text_range().contains_inclusive(offset)
        {
            let adjacent_eq = keyword.as_ref().map(|_| {
                name.syntax()
                    .next_token()
                    .is_some_and(|token| token.kind() == SyntaxKind::EQ)
            });
            slot = Some((name.syntax().text_range(), adjacent_eq));
        } else if let Some(name) = name {
            used.insert(name.text().to_string());
        } else if let Some(Expr::BinaryExpr(access)) = expr
            && access.op().is_some_and(|op| op.text() == ".")
            && let Some(name) = access.rhs().and_then(|rhs| rhs.name_ident())
        {
            // Julia's `f(; options.flag)` shorthand supplies keyword `flag`.
            used.insert(name.text().to_string());
        }
        if range.start() <= offset || before_next_separator {
            // A name/expression to the right without a delimiter already
            // occupies this same slot, so inserting at the whitespace is unsafe.
            after_separator = false;
        }
    }
    let (edit, existing_eq) =
        slot.or_else(|| after_separator.then(|| (TextRange::empty(offset), None)))?;
    Some(Site {
        call,
        edit,
        existing_eq,
        used,
    })
}

fn is_signature(call: &CallExpr) -> bool {
    let mut child = call.syntax().clone();
    while let Some(parent) = child.parent() {
        match parent.kind() {
            SyntaxKind::SIGNATURE => return true,
            SyntaxKind::ASSIGNMENT_EXPR => return parent.first_child() == Some(child),
            SyntaxKind::WHERE_EXPR | SyntaxKind::TYPE_ANNOTATION
                if parent.first_child() == Some(child.clone()) =>
            {
                child = parent;
            }
            _ => return false,
        }
    }
    false
}

impl Site {
    pub(super) fn explicit(&self) -> bool {
        self.existing_eq.is_some()
    }

    /// None means no reliable static signature; an empty list means all known
    /// names have already been used or the verified method has no keywords.
    pub(super) fn items<P: PackageSource>(
        &self,
        model: &SemanticModel,
        packages: &P,
        workspace: Option<&(Arc<PackageIndex>, ModulePath)>,
        root: &SyntaxNode,
        lines: &LineIndex,
        encoding: PositionEncoding,
    ) -> Option<Vec<CompletionItem>> {
        let resolver = Resolver::new(model, packages).with_workspace(workspace.cloned());
        let callee = self.call.callee()?;
        let argc = self.call.arg_list()?.args().try_fold(0, |n, arg| {
            (!matches!(arg.expr()?, Expr::SplatExpr(_))).then_some(n + 1)
        })?;
        let names = if let Some(ident) = callee.name_ident() {
            let name = ident.text();
            let offset = ident.syntax().text_range().start();
            match resolver.resolve(name, offset, Namespace::Value) {
                Resolution::Binding(id) if model.binding(id).kind == BindingKind::Function => {
                    local_keywords(model, root, workspace, id, argc)?
                }
                Resolution::Binding(id) if model.binding(id).kind == BindingKind::Import => {
                    let (path, name) = explicit_import(model, id)?;
                    indexed_keywords(&resolver, packages, workspace, &path, &name, argc)?
                }
                Resolution::System { module, name } | Resolution::Using { module, name } => {
                    let path = module.split('.').map(SmolStr::new).collect::<Vec<_>>();
                    indexed_keywords(&resolver, packages, workspace, &path, &name, argc)?
                }
                Resolution::Workspace { mut module, name } => {
                    module.insert(0, SmolStr::new(&workspace?.0.name));
                    indexed_keywords(&resolver, packages, workspace, &module, &name, argc)?
                }
                Resolution::Binding(id) if model.binding(id).kind == BindingKind::Type => {
                    let offset = model.binding(id).def_range.start();
                    let live = crate::index::harvest_tree(root);
                    let module =
                        module_at(&live, &model.enclosing_module_path(model.binding(id).scope))?;
                    let is_current = module
                        .types
                        .iter()
                        .any(|ty| ty.name == name && ty.loc.range.start == u32::from(offset));
                    if !is_current {
                        return None;
                    }
                    names_for_indexed_definition(module, name, argc)?
                }
                Resolution::WorkspaceImport { name } => {
                    let (package, host) = workspace?;
                    let mut module = vec![SmolStr::new(&package.name)];
                    module.extend(host.iter().cloned());
                    module.extend(model.enclosing_module_path(model.scope_at(offset)));
                    indexed_keywords(&resolver, packages, workspace, &module, &name, argc)?
                }
                _ => return None,
            }
        } else {
            let range = callee.syntax().text_range();
            let read = model
                .qualified_reads()
                .iter()
                .find(|q| q.range == range && !q.is_macro)?;
            let (name, receiver) = read.path.split_last()?;
            let offset = range.start();
            let head = receiver.first()?;
            if !matches!(head.as_str(), "Base" | "Core")
                && resolver.resolve(head, offset, Namespace::Value) == Resolution::Unresolved
            {
                return None;
            }
            let path = resolver.module_receiver_path(receiver, offset, Some(offset))?;
            indexed_keywords(&resolver, packages, workspace, &path, name, argc)?
        };
        let range = lsp_types::Range::new(
            lines.byte_to_position(self.edit.start().into(), encoding),
            lines.byte_to_position(self.edit.end().into(), encoding),
        );
        Some(
            names
                .into_iter()
                .filter(|name| !self.used.contains(name))
                .map(|name| {
                    // Julia tokenizes an adjacent `!=` as inequality, even
                    // when the exclamation mark is part of a valid name.
                    let bang = name.ends_with('!');
                    let label = if bang {
                        format!("{name} =")
                    } else {
                        format!("{name}=")
                    };
                    let new_text = match self.existing_eq {
                        None => label.clone(),
                        Some(true) if bang => format!("{name} "),
                        Some(_) => name.clone(),
                    };
                    CompletionItem {
                        label,
                        kind: Some(CompletionItemKind::FIELD),
                        detail: Some("keyword argument".into()),
                        sort_text: Some(format!("!fatou-keyword:{name}")),
                        filter_text: Some(name),
                        text_edit: Some(CompletionTextEdit::Edit(TextEdit { new_text, range })),
                        ..Default::default()
                    }
                })
                .collect(),
        )
    }
}

fn local_keywords(
    model: &SemanticModel,
    root: &SyntaxNode,
    workspace: Option<&(Arc<PackageIndex>, ModulePath)>,
    id: BindingId,
    argc: usize,
) -> Option<Vec<String>> {
    let binding = model.binding(id);
    // The semantic binding merges method declarations; any additional write
    // makes dispatch uncertain for this deliberately single-method feature.
    if model
        .occurrences(id)
        .any(|occ| !occ.is_def && occ.access != Access::Read)
    {
        return None;
    }
    if model.scope(binding.scope).kind.is_global()
        && let Some((pkg, host)) = workspace
    {
        let mut path = host.clone();
        path.extend(model.enclosing_module_path(binding.scope));
        if module_at(&pkg.root, &path).is_some_and(|module| {
            module.functions.iter().any(|f| {
                f.name == binding.name.as_str() && f.owner.is_none() && f.methods.len() > 1
            })
        }) {
            return None;
        }
    }
    let def = root
        .token_at_offset(binding.def_range.start())
        .right_biased()?;
    let call = def.parent_ancestors().find_map(CallExpr::cast)?;
    if !is_signature(&call) {
        return None;
    }
    let (positional, keywords) = extract_params(call.syntax());
    accepts_arity(&positional, argc).then(|| explicit_names(&keywords))
}

/// The resolver has already identified the exact in-file import binding.
pub(super) fn explicit_import(
    model: &SemanticModel,
    id: BindingId,
) -> Option<(ModulePath, SmolStr)> {
    let binding = model.binding(id);
    if model
        .occurrences(id)
        .any(|occ| !occ.is_def && occ.access != Access::Read)
    {
        return None;
    }
    let load = model
        .module_loads()
        .iter()
        .find(|load| load.scope == binding.scope && load.range.contains_range(binding.def_range))?;
    if load.path.leading_dots != 0 {
        return None;
    }
    let mut path = load.path.components.clone();
    let name = if let Some(items) = &load.items {
        items
            .iter()
            .find(|item| item.range.contains_range(binding.def_range))?
            .name
            .clone()
    } else {
        path.pop()?
    };
    (!path.is_empty()).then_some((path, name))
}

fn indexed_keywords<P: PackageSource>(
    resolver: &Resolver<'_, P>,
    packages: &P,
    workspace: Option<&(Arc<PackageIndex>, ModulePath)>,
    path: &[SmolStr],
    name: &str,
    argc: usize,
) -> Option<Vec<String>> {
    // Follow re-export / selected import identity to the owner, but never
    // assume that a same-spelled indexed package head is a bound receiver.
    let (path, name) = match resolver.qualified_member_origin(path, name) {
        Some(QualifiedMember::Symbol { module, name, .. }) => (module, name),
        Some(QualifiedMember::Module(_)) => return None,
        None => (path.to_vec(), SmolStr::new(name)),
    };
    let (head, tail) = path.split_first()?;
    let pkg = match workspace {
        Some((pkg, _)) if pkg.name == head.as_str() => Arc::clone(pkg),
        _ => packages.environment_package(head)?,
    };
    let module = module_at(&pkg.root, tail)?;
    if workspace.is_some_and(|(ws, _)| {
        let owner: Vec<_> = path.iter().map(SmolStr::as_str).collect();
        !ws.root.extension_groups(&owner, &name).is_empty()
    }) {
        return None;
    }
    names_for_indexed_definition(module, &name, argc)
}

fn names_for_indexed_definition(
    module: &crate::index::ModuleIndex,
    name: &str,
    argc: usize,
) -> Option<Vec<String>> {
    if module.consts.iter().any(|value| value.name == name) {
        return None;
    }
    let ty = module.types.iter().find(|ty| ty.name == name);
    let methods = module
        .functions
        .iter()
        .find(|f| f.name == name && f.owner.is_none())
        .map(|group| group.methods.as_slice())
        .unwrap_or(&[]);
    let candidates = methods
        .iter()
        .filter(|m| m.has_body && possible_arity(&m.params, argc));

    // Base.@kwdef defines a zero-positional constructor with exactly its
    // fields as keywords. An arbitrary macro or a field default is not proof.
    if argc == 0 && ty.is_some_and(|ty| ty.keyword_constructor) {
        return Some(ty?.fields.iter().map(|f| f.name.clone()).collect());
    }
    if ty.is_some_and(|ty| ty.fields.len() == argc && !ty.keyword_constructor) {
        // The default positional field constructor can be relevant; we
        // cannot prove it accepts additional keywords.
        return None;
    }
    let mut shared: Option<Vec<String>> = None;
    for m in candidates {
        // Hidden/generated signatures can change which keywords are valid.
        if m.is_generated || m.params.iter().any(|p| p.is_opaque) {
            return None;
        }
        let names = explicit_names(&m.keyword_params);
        match &mut shared {
            Some(shared) => shared.retain(|name| names.contains(name)),
            None => shared = Some(names),
        }
    }
    // Without argument-type inference, only propose names common to every
    // arity-compatible method. Keep the normal menu when that set is empty.
    shared.filter(|names| !names.is_empty())
}

fn possible_arity(params: &[Param], count: usize) -> bool {
    if params.iter().any(|p| p.is_opaque) {
        return true;
    }
    if let Some((last, fixed)) = params.split_last()
        && last.is_vararg
    {
        return count >= fixed.len() || fixed[count..].iter().all(|p| p.default.is_some());
    }
    accepts_arity(params, count)
}

fn accepts_arity(params: &[Param], count: usize) -> bool {
    !params
        .iter()
        .any(|param| param.is_opaque || param.is_vararg)
        && count <= params.len()
        && params[count..].iter().all(|param| param.default.is_some())
}

fn explicit_names(params: &[Param]) -> Vec<String> {
    params
        .iter()
        .filter(|param| !param.is_opaque && !param.is_vararg)
        .filter_map(|param| param.name.as_ref())
        .filter(|name| {
            let mut chars = name.chars();
            chars.next().is_some_and(is_ident_start) && chars.all(is_ident_continue)
        })
        .cloned()
        .collect()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::lsp::completion::compute_completions;

    const FIXTURE: &str = "function choose(x; option::Int=2, other=3, required, kws...)\n x\nend\noption = 1\nouter = 2\n";

    fn at(snippet: &str) -> (Vec<CompletionItem>, String) {
        at_with(snippet, &BTreeMap::new())
    }

    fn at_with(
        snippet: &str,
        packages: &BTreeMap<String, Arc<PackageIndex>>,
    ) -> (Vec<CompletionItem>, String) {
        let marked = format!("{FIXTURE}{snippet}");
        let offset = marked.find('|').unwrap();
        let source = marked.replacen('|', "", 1);
        let enc = PositionEncoding::Utf16;
        let position = LineIndex::new(&source).byte_to_position(offset, enc);
        (
            compute_completions(&source, position, enc, packages),
            source,
        )
    }

    fn keywords(items: &[CompletionItem]) -> Vec<&str> {
        items
            .iter()
            .filter(|item| item.detail.as_deref() == Some("keyword argument"))
            .map(|item| item.label.as_str())
            .collect()
    }

    fn apply(source: &str, item: &CompletionItem) -> String {
        let Some(CompletionTextEdit::Edit(edit)) = &item.text_edit else {
            panic!("missing standard completion textEdit");
        };
        let lines = LineIndex::new(source);
        let before = lines.position_to_byte(edit.range.start, PositionEncoding::Utf16);
        let after = lines.position_to_byte(edit.range.end, PositionEncoding::Utf16);
        format!("{}{}{}", &source[..before], edit.new_text, &source[after..])
    }

    #[test]
    fn keywords_at_semicolon_and_outer_commas_with_or_without_closing_paren() {
        for text in ["choose(1;|", "choose(1;|)", "choose(1;\n |)"] {
            let (items, source) = at(text);
            assert_eq!(
                keywords(&items),
                ["option=", "other=", "required="],
                "{text}"
            );
            assert_eq!(items[0].filter_text.as_deref(), Some("option"));
            assert!(items[0].sort_text.as_deref().unwrap() < "outer");
            assert!(apply(&source, &items[0]).contains("option="));
            assert!(items.iter().any(|item| item.label == "option"));
        }
        for text in [
            "choose(1; option=foo(1, 2),|",
            "choose(1; option=foo(1, 2), |)",
            "choose(1; option, |)",
            "choose(1; cfg.option, |)",
            "choose(1, option=2; |)",
            "choose(1; option=foo(1, 2),\n  |)",
        ] {
            let (items, _) = at(text);
            assert_eq!(keywords(&items), ["other=", "required="], "{text}");
        }
    }

    #[test]
    fn keywords_replace_whole_name_but_never_duplicate_existing_equal() {
        for (text, output) in [
            ("choose(1; op|Wrong)", "choose(1; option=)"),
            ("choose(1; op|Wrong=2)", "choose(1; option=2)"),
            ("choose(1; op| = 2)", "choose(1; option = 2)"),
            ("choose(1; |όνομα=2)", "choose(1; option=2)"),
            (
                "choose(1; option|=1, other=2)",
                "choose(1; option=1, other=2)",
            ),
        ] {
            let (items, source) = at(text);
            assert_eq!(items[0].label, "option=", "{text}");
            assert!(apply(&source, &items[0]).ends_with(output), "{text}");
            if text.contains('=') {
                assert!(!items.iter().any(|item| item.label == "outer"));
            }
        }
    }

    #[test]
    fn keywords_keep_rhs_splats_nested_and_ambiguous_contexts_conservative() {
        for text in [
            "choose(1; option=ou|)",
            "choose(1; ou|...)",
            "choose(1; option=foo(1, |))",
            "choose(1; cfg.ou|)",
            "choose(1, |)",
            r#"choose(1; "option|")"#,
            "choose(1; # option|\n)",
            "unresolved(1; |)",
            "choose(xs...; |)",
            "choose(1, 2; |)",
            "let choose = outer; choose(1; |); end",
            "choose(x::Int; different=1) = x\nchoose(1; |)",
            "function shell(x; opt|=2)\n x\nend",
            "shell(x; opt|=2) = x",
            "(; option|=1)",
        ] {
            assert!(keywords(&at(text).0).is_empty(), "{text}");
        }
        let (items, _) = at("choose(1; op|)");
        assert!(items.iter().any(|item| item.label == "option"));
        assert!(items.iter().any(|item| item.label == "option="));
        let (items, _) = at("unknown(1; option=choose(1; |))");
        assert_eq!(keywords(&items), ["option=", "other=", "required="]);
    }

    #[test]
    fn keyword_bang_keeps_the_equal_a_separate_julia_token() {
        for (text, output) in [
            ("flip(; |)", "flip(; activate! =)"),
            ("flip(; ac|=true)", "flip(; activate! =true)"),
            ("flip(; ac| = true)", "flip(; activate! = true)"),
        ] {
            let (items, source) = at(&format!("flip(; activate! = false) = 0\n{text}"));
            assert_eq!(keywords(&items), ["activate! ="], "{text}");
            assert!(apply(&source, &items[0]).ends_with(output), "{text}");
        }
    }

    #[test]
    fn keywords_for_known_indexed_function_but_not_shadowed_receiver() {
        let cst = crate::parser::parse("export runtool\nruntool(x; safe_mode=true) = x\n").cst;
        let mut root = crate::index::harvest_tree(&cst);
        root.name = "Tools".into();
        let pkg = PackageIndex {
            name: "Tools".into(),
            root,
            members: Vec::new(),
            member_modules: Default::default(),
            diagnostics: Vec::new(),
        };
        let lib = BTreeMap::from([("Tools".to_string(), Arc::new(pkg))]);
        for code in [
            "using Tools\nruntool(1; |)",
            "using Tools\nTools.runtool(1; |)",
            "using Tools: runtool\nruntool(1; |)",
            "import Tools: runtool as go\ngo(1; |)",
            "import Tools.runtool\nruntool(1; |)",
        ] {
            assert_eq!(keywords(&at_with(code, &lib).0), ["safe_mode="], "{code}");
        }
        assert!(keywords(&at_with("let Tools=outer; Tools.runtool(1; |); end", &lib).0).is_empty());
    }
    #[test]
    fn overlapping_overloads_and_statically_known_keyword_constructors() {
        let cst = crate::parser::parse(
            "export KDTree, Session, mixed\nstruct KDTree; a; b; c; end\nKDTree(x::AbstractMatrix; leafsize=20, sort=false)=KDTree(x,1,2)\nKDTree(x::AbstractVector, metric=identity; leafsize=20, mutable_data=false)=KDTree(x,1,2)\nBase.@kwdef struct Session\n options::Int=0\n id::Int\nend\nmixed(x::A; alpha=1)=x\nmixed(x::B; beta=2)=x"
        ).cst;
        let mut root = crate::index::harvest_tree(&cst);
        root.name = "Tools".into();
        let pkg = PackageIndex {
            name: "Tools".into(),
            root,
            members: Vec::new(),
            member_modules: Default::default(),
            diagnostics: Vec::new(),
        };
        let lib = BTreeMap::from([("Tools".to_string(), Arc::new(pkg))]);
        for (code, names) in [
            (
                "using Tools; KDTree(pts; leaf|size = 10)",
                vec!["leafsize="],
            ),
            (
                "using Tools: KDTree; KDTree(pts; leafs| = 10)",
                vec!["leafsize="],
            ),
            ("import Tools; Tools.KDTree(pts; |)", vec!["leafsize="]),
            (
                "using Tools; KDTree(pts, metric; |)",
                vec!["leafsize=", "mutable_data="],
            ),
            ("using Tools; mixed(thing; |)", vec![]),
            (
                "import Tools; Tools.Session(; opti|ons=0)",
                vec!["options=", "id="],
            ),
            (
                "using Tools: Session; Session(; |)",
                vec!["options=", "id="],
            ),
            ("Tools.Session(; |)", vec![]),
            ("let Tools = something; Tools.Session(; |); end", vec![]),
        ] {
            let (actual, source) = at_with(code, &lib);
            assert_eq!(keywords(&actual), names, "{code}");
            if code.contains("leaf|size") || code.contains("leafs|") {
                assert!(
                    apply(&source, &actual[0]).contains("leafsize = 10"),
                    "{code}"
                );
            }
        }
    }
}
