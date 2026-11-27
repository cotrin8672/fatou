//! Automatic, non-executing inlay hints for proven initializer shapes. These
//! are explicitly not the result of Julia compiler inference.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use lsp_types::{InlayHint, InlayHintKind, InlayHintLabel, InlayHintTooltip, Range};
use rowan::{TextSize, WalkEvent};

use crate::ast::{AssignmentExpr, AstNode, AstToken, CallExpr, Expr, HasArgList};
use crate::incremental::Analysis;
use crate::resolve::{Namespace, PackageSource, Resolution, Resolver};
use crate::semantic::{Access, BindingId, SemanticModel};
use crate::syntax::{SyntaxKind, SyntaxNode};
use crate::text::{PositionEncoding, TextBuffer};

const MAX_HINTS: usize = 256;
const MAX_BYTES: usize = 1_048_576;

pub(super) fn hints_via_db(
    snapshot: &Analysis,
    path: &Path,
    text: &TextBuffer,
    range: Range,
    encoding: PositionEncoding,
) -> Vec<InlayHint> {
    if text.len() > MAX_BYTES {
        return Vec::new();
    }
    // A buffer desynchronized by a concurrent edit has no safe reusable
    // semantic model. The next versioned LSP request will read the new text.
    salsa::Cancelled::catch(std::panic::AssertUnwindSafe(|| {
        let file = snapshot.lookup_file(path)?;
        if snapshot.file_text(file) != text.text() {
            return None;
        }
        let root = snapshot.parsed_tree(file);
        let model = snapshot.semantic_model(file);
        let workspace = snapshot.workspace_member(path);
        let resolver = Resolver::new(model, snapshot).with_workspace_at(workspace, Some(path));
        Some(collect(&root, model, &resolver, text, range, encoding))
    }))
    .ok()
    .flatten()
    .unwrap_or_default()
}

fn collect<P: PackageSource>(
    root: &SyntaxNode,
    model: &SemanticModel,
    resolver: &Resolver<'_, P>,
    text: &TextBuffer,
    range: Range,
    encoding: PositionEncoding,
) -> Vec<InlayHint> {
    let lines = text.line_index();
    let start = TextSize::new(lines.position_to_byte(range.start, encoding) as u32);
    let stop = TextSize::new(lines.position_to_byte(range.end, encoding) as u32);
    let definitions: HashMap<_, _> = model
        .bindings()
        .iter()
        .enumerate()
        .filter(|(_, binding)| (start..stop).contains(&binding.def_range.end()))
        .map(|(i, binding)| (binding.def_range, BindingId(i as u32)))
        .collect();
    if definitions.is_empty() {
        return Vec::new();
    }
    let rewritten: HashSet<_> = model
        .idents()
        .iter()
        .filter(|occurrence| matches!(occurrence.access, Access::Write | Access::ReadWrite))
        .filter_map(|occurrence| occurrence.binding)
        .collect();
    let mut hints = Vec::new();
    let mut cursor = root.preorder();
    while let Some(event) = cursor.next() {
        let WalkEvent::Enter(node) = event else {
            continue;
        };
        if node.text_range().end() < start
            || node.text_range().start() >= stop
            || !matches!(
                node.kind(),
                SyntaxKind::ROOT
                    | SyntaxKind::BLOCK
                    | SyntaxKind::MODULE_DEF
                    | SyntaxKind::FUNCTION_DEF
                    | SyntaxKind::BEGIN_EXPR
                    | SyntaxKind::ASSIGNMENT_EXPR
            )
        {
            cursor.skip_subtree();
            continue;
        }
        let Some(assignment) = AssignmentExpr::cast(node) else {
            continue;
        };
        cursor.skip_subtree();
        let Some(identifier) = assignment.lhs().and_then(|lhs| lhs.name_ident()) else {
            continue;
        };
        if identifier.text() == "_"
            || !assignment
                .op()
                .is_some_and(|op| op.syntax().kind() == SyntaxKind::EQ)
        {
            continue;
        }
        let span = identifier.syntax().text_range();
        let Some(binding) = definitions.get(&span) else {
            continue;
        };
        if rewritten.contains(binding) {
            continue;
        }
        let Some(rhs) = assignment.rhs() else {
            continue;
        };
        let Some(ty) = initializer_type(&rhs, resolver) else {
            continue;
        };
        hints.push(InlayHint {
            position: lines.byte_to_position(usize::from(span.end()), encoding),
            label: InlayHintLabel::String(format!("::{ty}")),
            kind: Some(InlayHintKind::TYPE),
            text_edits: None,
            tooltip: Some(InlayHintTooltip::String(format!(
                "Static initializer type: {ty}\nFatou recognized a literal or a standard Julia constructor. This is not a Julia compiler inference result."
            ))),
            padding_left: None,
            padding_right: None,
            data: None,
        });
        if hints.len() == MAX_HINTS {
            break;
        }
    }
    hints
}

fn initializer_type<P: PackageSource>(rhs: &Expr, resolver: &Resolver<'_, P>) -> Option<String> {
    match rhs {
        Expr::Literal(literal) => {
            if literal.bool_token().is_some() {
                return Some("Bool".into());
            }
            let number = literal.numeric_token()?;
            match number.kind() {
                SyntaxKind::FLOAT
                    if number
                        .text()
                        .replace('_', "")
                        .parse::<f64>()
                        .ok()?
                        .is_finite() =>
                {
                    Some("Float64".into())
                }
                SyntaxKind::FLOAT32
                    if number
                        .text()
                        .replace('_', "")
                        .replace('f', "e")
                        .parse::<f32>()
                        .ok()?
                        .is_finite() =>
                {
                    Some("Float32".into())
                }
                // Only the portable machine-Int range; larger literals can
                // instead be Int64 (on 32-bit Julia), Int128 or BigInt.
                SyntaxKind::INTEGER if number.text().replace('_', "").parse::<i32>().is_ok() => {
                    Some("Int".into())
                }
                _ => None,
            }
        }
        Expr::StringLiteral(s)
            if s.prefix().is_none()
                && s.suffix().is_none()
                && s.interpolations().next().is_none() =>
        {
            Some("String".into())
        }
        Expr::CallExpr(c) => vector_type(c, resolver),
        _ => None,
    }
}

fn vector_type<P: PackageSource>(call: &CallExpr, resolver: &Resolver<'_, P>) -> Option<String> {
    fn builtin<P: PackageSource>(resolver: &Resolver<'_, P>, expr: &Expr, name: &str) -> bool {
        expr.name_ident().is_some_and(|ident| ident.text() == name)
            && matches!(resolver.resolve(name, expr.syntax().text_range().start(), Namespace::Value),
                Resolution::System { module, .. } if matches!(module.as_str(), "Base" | "Core"))
    }
    let Expr::CurlyExpr(callee) = call.callee()? else {
        return None;
    };
    let base = callee.base()?;
    if !builtin(resolver, &base, "Vector") {
        return None;
    }
    let type_arguments = callee.arg_list()?;
    let mut types = type_arguments.args();
    let element = types.next()?.expr()?;
    let name = element.name_ident()?;
    if types.next().is_some()
        || type_arguments.keyword_args().next().is_some()
        || !matches!(
            name.text(),
            "Float64" | "Float32" | "Int" | "ComplexF64" | "ComplexF32" | "Bool"
        )
        || !builtin(resolver, &element, name.text())
    {
        return None;
    }
    let list = call.arg_list()?;
    let mut args = list.args();
    if !builtin(resolver, &args.next()?.expr()?, "undef") || list.keyword_args().next().is_some() {
        return None;
    }
    let dim = args.next()?.expr()?;
    if args.next().is_some() {
        return None;
    }
    let known_dim = match &dim {
        Expr::Literal(n) => n.numeric_token().is_some_and(|n| {
            n.kind() == SyntaxKind::INTEGER && n.text().replace('_', "").parse::<i32>().is_ok()
        }),
        Expr::CallExpr(length) => {
            length
                .callee()
                .is_some_and(|callee| builtin(resolver, &callee, "length"))
                && length.arg_list().is_some_and(|args| {
                    args.args().count() == 1 && args.keyword_args().next().is_none()
                })
        }
        _ => false,
    };
    known_dim.then(|| format!("Vector{{{}}}", name.text()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::Position;

    fn hints(source: &str, range: Range) -> Vec<(u32, String)> {
        let root = crate::parser::parse(source).cst;
        let model = SemanticModel::build(&root);
        let library = crate::index::build_system_library(None);
        let resolver = Resolver::new(&model, &library.packages);
        collect(
            &root,
            &model,
            &resolver,
            &TextBuffer::from(source),
            range,
            PositionEncoding::Utf16,
        )
        .into_iter()
        .map(|h| {
            let InlayHintLabel::String(label) = h.label else {
                panic!("expected plain label")
            };
            (h.position.line, label)
        })
        .collect()
    }

    #[test]
    fn static_inlay_hints_are_for_proven_unmodified_initializers_only() {
        let text = "function run(u)\n            n = 2\n            κ = 200.0e6\n            a = Vector{Float64}(undef, length(u))\n            b = similar(a)\n            changed = 1\n            changed += 2\n            for i in u\n                iteration = 1\n            end\n            return a, κ, n, changed\n            end\n            function shadow(Vector, u)\n                a = Vector{Float64}(undef, length(u))\n                return a\n            end\n";
        assert_eq!(
            hints(text, Range::new(Position::new(0, 0), Position::new(15, 0))),
            vec![
                (1, "::Int".into()),
                (2, "::Float64".into()),
                (3, "::Vector{Float64}".into())
            ]
        );
        assert_eq!(
            hints(text, Range::new(Position::new(2, 0), Position::new(3, 0))),
            vec![(2, "::Float64".into())]
        );
    }
}
