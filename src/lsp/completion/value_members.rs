//! Conservative property completion for lexically identified values, not
//! package-name fallbacks. Follow a small chain of directly declared fields.

use std::sync::Arc;

use lsp_types::{CompletionItem, CompletionItemKind};
use rowan::{TextRange, TextSize};
use smol_str::SmolStr;

use crate::ast::{
    AssignmentExpr, AstNode, AstToken, CallExpr, DocAttachment, Expr, TypeAnnotation, body_of,
};
use crate::index::{ModuleIndex, PackageIndex, TypeDef, TypeExpr, TypeKind, typeexpr::lower_type};
use crate::resolve::{
    ModulePath, Namespace, PackageSource, QualifiedMember, QualifiedMemberKind, Resolution,
    Resolver, module_at,
};
use crate::semantic::{Access, BindingId, BindingKind, SemanticModel};
use crate::syntax::{SyntaxKind, SyntaxNode};

pub(super) fn items<P: PackageSource>(
    model: &SemanticModel,
    root: &SyntaxNode,
    packages: &P,
    workspace: Option<&(Arc<PackageIndex>, ModulePath)>,
    receiver: &[String],
    start: TextSize,
) -> Option<Vec<CompletionItem>> {
    // A fixed bound makes the cost independent of nested/dynamic type graphs.
    if receiver.len() > 4 {
        return None;
    }
    let (head, fields) = receiver.split_first()?;
    let resolver = Resolver::new(model, packages).with_workspace(workspace.cloned());
    let ctx = Context {
        packages,
        workspace,
        resolver,
        model,
        root,
    };

    // The exact recorded identifier disambiguates a read in a scope
    // initializer. Never treat an unresolved spelling as an indexed value.
    let read = model.ident_at(start).filter(|read| {
        read.range.start() == start && read.name == head.as_str() && read.access == Access::Read
    });
    let id = if let Some(read) = read {
        read.binding?
    } else if let Resolution::Binding(id) = ctx.resolver.resolve(head, start, Namespace::Value) {
        id
    } else {
        return None;
    };
    let binding = model.binding(id);
    if !matches!(
        binding.kind,
        BindingKind::Param
            | BindingKind::KeywordParam
            | BindingKind::Local
            | BindingKind::Global
            | BindingKind::LetVar
            | BindingKind::Const
    ) || binding.def_range.end() > start
        || !ctx.unreassigned(id)
    {
        return None;
    }

    let def = exact_token(root, binding.def_range)?;
    let annotated = def.parent_ancestors().find_map(|node| {
        let annotation = TypeAnnotation::cast(node)?;
        (annotation.pattern()?.syntax().text_range() == binding.def_range)
            .then(|| annotation.ty())
            .flatten()
    });
    let (mut ty, constructor) = if let Some(annotation) = annotated {
        let offset = annotation.syntax().text_range().start();
        (
            ctx.lexical_type(&lower_type(annotation.syntax()), offset)?,
            false,
        )
    } else {
        // A plain unconditional assignment to a known struct constructor.
        // No arbitrary function inference; ignore broadcast calls, splats
        // and assignments hidden in a control flow block.
        let assign = def
            .parent_ancestors()
            .nth(1)
            .and_then(AssignmentExpr::cast)?;
        if assign.lhs()?.syntax().text_range() != binding.def_range
            || assign.op()?.text() != "="
            || assign.syntax().text_range().end() > start
        {
            return None;
        }
        let block = assign.syntax().parent()?;
        if !matches!(
            block.kind(),
            SyntaxKind::BLOCK | SyntaxKind::ROOT | SyntaxKind::TOPLEVEL_SEMICOLON
        ) || !block.text_range().contains(start)
        {
            return None;
        }
        let call = CallExpr::cast(assign.rhs()?.syntax().clone())?;
        let callee = call.callee()?;
        let offset = callee.syntax().text_range().start();
        let ty = ctx.lexical_type(&lower_type(callee.syntax()), offset)?;
        if !ctx.constructor_shape_is_consistent(&ty) {
            return None;
        }
        (ty, true)
    };

    for wanted in fields {
        let available = ctx.fields(&ty)?;
        let field = available.into_iter().find(|field| &field.name == wanted)?;
        let annotation = field.ty?;
        ty = match &ty {
            KnownType::Local(_) => ctx.lexical_type(&annotation, field.offset?)?,
            KnownType::Indexed { owner, .. } => ctx.indexed_type_from(owner, &annotation)?,
        };
    }
    Some(
        ctx.fields(&ty)?
            .into_iter()
            .map(|field| CompletionItem {
                label: field.name,
                kind: Some(CompletionItemKind::FIELD),
                detail: Some(
                    if constructor {
                        "field (constructor result)"
                    } else {
                        "field"
                    }
                    .into(),
                ),
                ..Default::default()
            })
            .collect(),
    )
}

fn exact_token(root: &SyntaxNode, range: TextRange) -> Option<crate::syntax::SyntaxToken> {
    let token = root.token_at_offset(range.start()).right_biased()?;
    (token.text_range() == range).then_some(token)
}

enum KnownType {
    Local(SyntaxNode),
    Indexed {
        package: Arc<PackageIndex>,
        owner: ModulePath,
        name: SmolStr,
    },
}

struct Field {
    name: String,
    ty: Option<TypeExpr>,
    offset: Option<TextSize>,
}

struct Context<'a, P: PackageSource> {
    packages: &'a P,
    workspace: Option<&'a (Arc<PackageIndex>, ModulePath)>,
    resolver: Resolver<'a, P>,
    model: &'a SemanticModel,
    root: &'a SyntaxNode,
}

impl<P: PackageSource> Context<'_, P> {
    fn unreassigned(&self, id: BindingId) -> bool {
        let def = self.model.binding(id).def_range;
        !self
            .model
            .occurrences(id)
            .any(|occ| !occ.is_def && occ.range != def && occ.access != Access::Read)
    }

    fn lexical_type(&self, ty: &TypeExpr, offset: TextSize) -> Option<KnownType> {
        let path = type_path(ty)?;
        let (name, receiver) = path.split_last()?;
        if let Some(head) = receiver.first() {
            if self.resolver.resolve(head, offset, Namespace::Value) == Resolution::Unresolved {
                return None;
            }
            let written: ModulePath = receiver.iter().map(SmolStr::new).collect();
            let owner = self
                .resolver
                .module_receiver_path(&written, offset, Some(offset))?;
            return self.indexed_type(&owner, name);
        }
        match self.resolver.resolve(name, offset, Namespace::Value) {
            Resolution::Binding(id) => {
                let binding = self.model.binding(id);
                match binding.kind {
                    BindingKind::Type if self.unreassigned(id) => {
                        let node = exact_token(self.root, binding.def_range)?
                            .parent_ancestors()
                            .find(|node| {
                                matches!(
                                    node.kind(),
                                    SyntaxKind::STRUCT_DEF
                                        | SyntaxKind::ABSTRACT_DEF
                                        | SyntaxKind::PRIMITIVE_DEF
                                )
                            })?;
                        (node.kind() == SyntaxKind::STRUCT_DEF).then_some(KnownType::Local(node))
                    }
                    BindingKind::Import => {
                        let (owner, name) = super::call_keywords::explicit_import(self.model, id)?;
                        self.indexed_type(&owner, &name)
                    }
                    _ => None,
                }
            }
            Resolution::Workspace { mut module, name } => {
                module.insert(0, SmolStr::new(&self.workspace?.0.name));
                self.indexed_type(&module, &name)
            }
            Resolution::WorkspaceImport { name } => {
                let (pkg, host) = self.workspace?;
                let mut owner = vec![SmolStr::new(&pkg.name)];
                owner.extend(host.iter().cloned());
                owner.extend(
                    self.model
                        .enclosing_module_path(self.model.scope_at(offset)),
                );
                self.indexed_type(&owner, &name)
            }
            Resolution::Using { module, name } | Resolution::System { module, name } => {
                let owner: ModulePath = module.split('.').map(SmolStr::new).collect();
                self.indexed_type(&owner, &name)
            }
            _ => None,
        }
    }

    fn indexed_type(&self, owner: &[SmolStr], name: &str) -> Option<KnownType> {
        match self.resolver.qualified_member_origin(owner, name)? {
            QualifiedMember::Symbol {
                module,
                name,
                kind: QualifiedMemberKind::Type,
            } => {
                let package = self.package(module.first()?)?;
                let def = find_type(&package, &module, &name)?;
                matches!(def.kind, TypeKind::Struct { .. }).then_some(KnownType::Indexed {
                    package,
                    owner: module,
                    name,
                })
            }
            _ => None,
        }
    }

    fn indexed_type_from(&self, owner: &[SmolStr], annotation: &TypeExpr) -> Option<KnownType> {
        let (name, receiver) = type_path(annotation)?.split_last()?;
        let mut module = owner.to_vec();
        for part in receiver {
            module = match self.resolver.qualified_member_origin(&module, part)? {
                QualifiedMember::Module(path) => path,
                _ => return None,
            };
        }
        self.indexed_type(&module, name)
    }

    fn package(&self, name: &str) -> Option<Arc<PackageIndex>> {
        self.workspace
            .filter(|(p, _)| p.name == name)
            .map(|(p, _)| Arc::clone(p))
            .or_else(|| self.packages.environment_package(name))
    }

    fn constructor_shape_is_consistent(&self, ty: &KnownType) -> bool {
        match ty {
            KnownType::Local(node) => {
                // A live custom inner/outer constructor can return an
                // unrelated value. Only infer the synthesized local one.
                let Some(name) = local_name(node) else {
                    return false;
                };
                if body_of(node).is_some_and(|body| body.children().any(|stmt| !is_field(&stmt))) {
                    return false;
                }
                !self
                    .model
                    .bindings()
                    .iter()
                    .any(|b| b.name == name && b.kind == BindingKind::Function)
                    && !self
                        .model
                        .qualified_reads()
                        .iter()
                        .any(|q| q.path.last().is_some_and(|n| n == &name))
            }
            KnownType::Indexed {
                package,
                owner,
                name,
            } => {
                let Some(module) = module_at(&package.root, &owner[1..]) else {
                    return false;
                };
                // Imported constructor result is a hint, not proof of dynamic
                // dispatch: opt out on declared conflicting signatures,
                // opaque/generated methods, or visible user extensions.
                find_type(package, owner, name).is_some_and(|ty| ty.constructor_shape)
                    && module
                        .functions
                        .iter()
                        .filter(|f| f.owner.is_none() && f.name == name.as_str())
                        .flat_map(|f| &f.methods)
                        .all(|method| {
                            !method.is_generated
                                && !method.params.iter().any(|p| p.is_opaque)
                                && method.return_type.as_ref().is_none_or(|ret| {
                                    type_path(ret)
                                        .and_then(|path| path.last())
                                        .is_some_and(|n| n == name.as_str())
                                })
                        })
                    && !self.workspace.is_some_and(|(ws, _)| {
                        let parts: Vec<_> = owner.iter().map(SmolStr::as_str).collect();
                        !ws.root.extension_groups(&parts, name).is_empty()
                    })
                    && !self
                        .model
                        .bindings()
                        .iter()
                        .any(|b| b.name == name.as_str() && b.kind == BindingKind::Function)
            }
        }
    }

    fn fields(&self, ty: &KnownType) -> Option<Vec<Field>> {
        match ty {
            KnownType::Local(node) => {
                let name = local_name(node)?;
                // Only run the live syntax walk when the property API is
                // actually referenced. The document may be large.
                if self.model.idents().iter().any(|r| property_method(&r.name))
                    || self
                        .model
                        .qualified_reads()
                        .iter()
                        .any(|r| r.path.last().is_some_and(|name| property_method(name)))
                {
                    let live = crate::index::harvest_tree(self.root);
                    if custom_properties(&live, &name, None) {
                        return None;
                    }
                }
                if self
                    .workspace
                    .is_some_and(|(pkg, _)| custom_properties(&pkg.root, &name, None))
                {
                    return None;
                }
                Some(body_of(node)?.children().filter_map(local_field).collect())
            }
            KnownType::Indexed {
                package,
                owner,
                name,
            } => {
                let def = find_type(package, owner, name)?;
                if custom_properties(&package.root, name, def.supertype.as_ref())
                    || self.workspace.is_some_and(|(ws, _)| {
                        !Arc::ptr_eq(ws, package)
                            && custom_properties(&ws.root, name, def.supertype.as_ref())
                    })
                {
                    return None;
                }
                Some(
                    def.fields
                        .iter()
                        .map(|field| Field {
                            name: field.name.clone(),
                            ty: field.type_annotation.clone(),
                            offset: None,
                        })
                        .collect(),
                )
            }
        }
    }
}

fn find_type<'a>(package: &'a PackageIndex, owner: &[SmolStr], name: &str) -> Option<&'a TypeDef> {
    module_at(&package.root, owner.get(1..)?)?
        .types
        .iter()
        .find(|ty| ty.name == name)
}

fn type_path(ty: &TypeExpr) -> Option<&[String]> {
    match ty {
        TypeExpr::Name { path } if !path.is_empty() => Some(path),
        TypeExpr::Applied { base, .. } => type_path(base),
        _ => None,
    }
}

fn local_name(node: &SyntaxNode) -> Option<String> {
    let signature = node
        .children()
        .find(|node| node.kind() == SyntaxKind::SIGNATURE)?;
    let mut name = signature.children().next()?;
    while matches!(
        name.kind(),
        SyntaxKind::BINARY_EXPR | SyntaxKind::CURLY_EXPR
    ) {
        name = name.first_child()?;
    }
    let expr = Expr::cast(name)?;
    Some(expr.name_ident()?.text().to_string())
}

fn is_field(stmt: &SyntaxNode) -> bool {
    local_field(stmt.clone()).is_some()
}

fn local_field(mut stmt: SyntaxNode) -> Option<Field> {
    if let Some(attachment) = DocAttachment::cast(stmt.clone()) {
        stmt = attachment.target().clone();
    }
    if stmt.kind() == SyntaxKind::CONST_STMT {
        stmt = stmt.first_child()?;
    }
    let expr = Expr::cast(stmt)?;
    let expr = if let Expr::AssignmentExpr(assign) = expr {
        assign.lhs()?
    } else {
        expr
    };
    if let Some(name) = expr.name_ident() {
        return Some(Field {
            name: name.text().to_string(),
            ty: None,
            offset: None,
        });
    }
    let Expr::TypeAnnotation(annotation) = expr else {
        return None;
    };
    let param = annotation.pattern()?;
    let name = param.name_ident()?.text().to_string();
    let ty = annotation.ty();
    Some(Field {
        name,
        ty: ty.as_ref().map(|ty| lower_type(ty.syntax())),
        offset: ty.map(|ty| ty.syntax().text_range().start()),
    })
}

fn property_method(name: &str) -> bool {
    matches!(name, "getproperty" | "propertynames")
}

fn custom_properties(module: &ModuleIndex, name: &str, supertype: Option<&TypeExpr>) -> bool {
    module
        .functions
        .iter()
        .filter(|f| property_method(&f.name))
        .any(|f| {
            f.methods.iter().any(|m| {
                m.has_body
                    && m.params.first().is_some_and(|p| {
                        fn overlaps(ty: &TypeExpr, name: &str) -> bool {
                            match ty {
                                TypeExpr::Name { path } => path
                                    .last()
                                    .is_some_and(|last| last == name || last == "Any"),
                                TypeExpr::Applied { base, .. } => overlaps(base, name),
                                TypeExpr::Union { members } => {
                                    members.iter().any(|ty| overlaps(ty, name))
                                }
                                TypeExpr::TypeVar { upper, .. } => {
                                    upper.as_deref().is_none_or(|ty| overlaps(ty, name))
                                }
                                TypeExpr::Raw { .. } => true,
                                TypeExpr::Tuple { .. } => false,
                            }
                        }
                        p.is_opaque
                            || p.type_annotation.as_ref().is_none_or(|ty| {
                                overlaps(ty, name)
                                    || supertype
                                        .and_then(type_path)
                                        .and_then(|p| p.last())
                                        .is_some_and(|sup| overlaps(ty, sup))
                            })
                    })
            })
        })
        || module
            .submodules
            .iter()
            .any(|m| custom_properties(m, name, supertype))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lsp::completion::compute_completions;
    use crate::text::{LineIndex, PositionEncoding};
    use std::collections::BTreeMap;

    fn run(code: &str, lib: &BTreeMap<String, Arc<PackageIndex>>) -> Vec<CompletionItem> {
        let offset = code.find('|').unwrap();
        let text = code.replacen('|', "", 1);
        let enc = PositionEncoding::Utf16;
        let at = LineIndex::new(&text).byte_to_position(offset, enc);
        compute_completions(&text, at, enc, lib)
    }

    fn fields(items: &[CompletionItem]) -> Vec<&str> {
        items
            .iter()
            .filter(|it| it.kind == Some(CompletionItemKind::FIELD))
            .map(|it| it.label.as_str())
            .collect()
    }

    #[test]
    fn typed_local_fields_chains_and_suffixes() {
        let lib = BTreeMap::new();
        let setup =
            "struct Unit\n value::Float64\nend\nstruct Point\n lon::Unit\n lat::Unit\nend\n";
        for (tail, names) in [
            ("function f(x::Point)\n x.lo|n\nend", vec!["lon", "lat"]),
            ("function f(x::Point)\n x.lon.va|lue\nend", vec!["value"]),
            ("x=Point(Unit(1.),Unit(2.)); x.lo|n", vec!["lon", "lat"]),
            ("function f(x::Point)\n x=123\n x.lo|n\nend", vec![]),
            ("function f(x)\n x.lo|n\nend", vec![]),
            ("function f(x::Point)\n x.unknown.|\nend", vec![]),
            (
                "Base.getproperty(x::Point,name::Symbol)=123\nfunction f(x::Point)\n x.lo|n\nend",
                vec![],
            ),
            ("Point(x::String)=42\nx=Point(\"bad\"); x.lo|n", vec![]),
        ] {
            let actual = run(&format!("{setup}{tail}"), &lib);
            assert_eq!(fields(&actual), names, "{tail}");
            if tail.contains("x.lo|n") && !names.is_empty() {
                assert!(
                    actual[0].text_edit.is_some(),
                    "replace an existing suffix safely"
                );
            }
        }
    }

    #[test]
    fn imported_struct_fields_but_not_unrelated_constructor_return() {
        let src = "export Arg, URI, FalseReturn, UnknownFactory\nstruct Arg\n target::String\nend\nstruct URI\n path::String\nend\nstruct FalseReturn\n unrelated::Int\nend\nFalseReturn(s::String)=7\nUnknownFactory(s::String)=URI(s)";
        let mut tree = crate::index::harvest_tree(&crate::parser::parse(src).cst);
        tree.name = "Tools".into();
        let p = PackageIndex {
            name: "Tools".into(),
            root: tree,
            members: Vec::new(),
            member_modules: Default::default(),
            diagnostics: Vec::new(),
        };
        let lib = BTreeMap::from([("Tools".to_string(), Arc::new(p))]);
        for (code, names) in [
            (
                "import Tools\nfunction f(x::Tools.Arg)\n x.tar|get\nend",
                vec!["target"],
            ),
            (
                "using Tools: Arg\nfunction f(x::Arg)\n x.tar|get\nend",
                vec!["target"],
            ),
            (
                "using Tools\nfunction f(x::Arg)\n x.tar|get\nend",
                vec!["target"],
            ),
            ("import Tools\nx=Tools.URI(\"a\"); x.pa|th", vec!["path"]),
            (
                "import Tools\nx=Tools.FalseReturn(\"a\"); x.un|related",
                vec![],
            ),
            (
                "import Tools\nx=Tools.UnknownFactory(\"a\"); x.pa|th",
                vec![],
            ),
            ("x=Tools.URI(\"a\"); x.pa|th", vec![]),
        ] {
            assert_eq!(fields(&run(code, &lib)), names, "{code}");
        }
    }
}
