//! Recover method templates from literal-symbol loops such as Base's
//! `for op in (:+, :min, :max); @eval ($op)(a, b, c, xs...) = ...; end`.
//! Both tuple and vector literals can supply the names.
//! The loop body must consist entirely of `@eval` method definitions, with
//! only the callee interpolated in each signature. All locations refer to
//! the original source, and executable interpolations remain unharvested.

use rowan::TextRange;

use crate::ast::{
    Arg, AstNode, AstToken, CallExpr, Expr, ForBinding, ForExpr, HasArgList, HasBody,
    Interpolation, MacroCall, Operator, body_of,
};
use crate::semantic::signature::peel_signature;
use crate::syntax::{SyntaxKind, SyntaxNode};

use super::{is_short_form_def, is_trivia, macro_args, node_name_text, signature_start};

pub(super) struct GeneratedMethods {
    pub(super) names: Vec<String>,
    pub(super) signatures: Vec<(SyntaxNode, TextRange)>,
}

pub(super) fn literal_eval_loop(node: &SyntaxNode) -> Option<GeneratedMethods> {
    let loop_expr = ForExpr::cast(node.clone())?;
    let mut bindings = node.children().filter_map(ForBinding::cast);
    let binding = bindings.next()?;
    if bindings.next().is_some() || binding.syntax().children().count() != 2 {
        return None;
    }
    let Expr::Name(variable) = binding.pattern()? else {
        return None;
    };
    let variable = variable.ident()?;
    let values = binding.iterable()?;
    if !matches!(values, Expr::TupleExpr(_) | Expr::VectExpr(_)) {
        return None;
    }
    let names = values
        .syntax()
        .children()
        .map(|arg| quoted_name(Arg::cast(arg)?.expr()?))
        .collect::<Option<Vec<_>>>()?;
    if names.is_empty() {
        return None;
    }

    let mut signatures = Vec::new();
    for statement in loop_expr.body()?.syntax().children() {
        let call = MacroCall::cast(statement)?;
        let path: Vec<_> = call
            .name()?
            .ident_tokens()
            .map(|t| t.text().to_string())
            .collect();
        let is_eval = match path.as_slice() {
            [name] => name == "eval",
            [owner, name] => owner == "Base" && name == "eval",
            _ => false,
        };
        if !is_eval {
            return None;
        }
        // Complex interpolation could reassign the loop variable before a
        // later template reads it, so validate the whole body before publishing.
        if call
            .syntax()
            .descendants()
            .filter_map(Interpolation::cast)
            .any(|interpolation| !is_loop_name(&interpolation, variable.text()))
        {
            return None;
        }
        let args = macro_args(call.syntax());
        let [target] = args.as_slice() else {
            return None;
        };
        if target.kind() == SyntaxKind::BEGIN_EXPR {
            for definition in body_of(target)?.children() {
                signatures.push(method_template(&definition, variable.text())?);
            }
        } else {
            signatures.push(method_template(target, variable.text())?);
        }
    }
    Some(GeneratedMethods { names, signatures })
}

fn quoted_name(expr: Expr) -> Option<String> {
    let Expr::QuoteSym(quote) = expr else {
        return None;
    };
    match quote.expr() {
        Some(Expr::Name(name)) => Some(name.ident()?.text().to_string()),
        Some(Expr::NonstandardIdentifier(name)) => node_name_text(name.syntax()),
        None => {
            let mut tokens = quote
                .syntax()
                .children_with_tokens()
                .filter_map(|el| el.into_token())
                .filter(|t| !is_trivia(t.kind()));
            if tokens.next()?.kind() != SyntaxKind::COLON {
                return None;
            }
            let operator = Operator::cast(tokens.next()?)?;
            tokens.next().is_none().then(|| operator.text().to_string())
        }
        _ => None,
    }
}

fn method_template(node: &SyntaxNode, variable: &str) -> Option<(SyntaxNode, TextRange)> {
    let signature = if node.kind() == SyntaxKind::FUNCTION_DEF {
        signature_start(node)?
    } else if is_short_form_def(node) {
        node.children().next()?
    } else {
        return None;
    };
    let (core, _, _) = peel_signature(signature.clone());
    let call = CallExpr::cast(core?)?;
    let Expr::Interpolation(name) = unparenthesized(call.callee()?)? else {
        return None;
    };
    if !is_loop_name(&name, variable)
        || signature
            .descendants()
            .filter_map(Interpolation::cast)
            .count()
            != 1
    {
        return None;
    }
    Some((signature, name.syntax().text_range()))
}

fn is_loop_name(interpolation: &Interpolation, variable: &str) -> bool {
    if let Some(ident) = interpolation.ident() {
        return ident.text() == variable;
    }
    let Some(Expr::Name(name)) = interpolation.expr().and_then(unparenthesized) else {
        return false;
    };
    name.ident().is_some_and(|ident| ident.text() == variable)
}

fn unparenthesized(mut expr: Expr) -> Option<Expr> {
    while let Expr::ParenExpr(paren) = expr {
        expr = paren.expr()?;
    }
    Some(expr)
}

/// Recognize a locally defined, exact one-argument macro whose entire return
/// is a quote with one unconditionally emitted struct. The struct name is the
/// supplied identifier; optional sibling definitions must be its constructors.
/// This recognizes e.g. a family of weight types, not arbitrary macro calls.
pub(super) fn named_struct_at_call(
    node: &SyntaxNode,
    name: &str,
    args: &[SyntaxNode],
) -> Option<(String, TextRange, SyntaxNode)> {
    let [argument] = args else { return None };
    if argument.kind() != SyntaxKind::NAME
        || MacroCall::cast(node.clone())?
            .name()?
            .ident_tokens()
            .count()
            != 1
    {
        return None;
    }
    let parent = node.parent()?;
    let mut defs = parent
        .children()
        .take_while(|child| child != node)
        .filter_map(|child| {
            let child = crate::ast::DocAttachment::cast(child.clone())
                .map(|doc| doc.target().clone())
                .unwrap_or(child);
            if child.kind() != SyntaxKind::MACRO_DEF {
                return None;
            }
            let signature = CallExpr::cast(signature_start(&child)?)?;
            let Expr::Name(callee) = signature.callee()? else {
                return None;
            };
            (callee.ident()?.text() == name).then_some((child, signature))
        });
    let (definition, signature) = defs.next()?;
    if defs.next().is_some() {
        return None;
    }
    let arg_list = signature.arg_list()?;
    let mut params = arg_list.args();
    let Expr::Name(parameter) = params.next()?.expr()? else {
        return None;
    };
    if params.next().is_some() || arg_list.keyword_args().next().is_some() {
        return None;
    }
    let parameter = parameter.ident()?;
    let body = only_child(&body_of(&definition)?)?;
    let quoted = if body.kind() == SyntaxKind::RETURN_EXPR {
        only_child(&body)?
    } else {
        body
    };
    if quoted.kind() != SyntaxKind::QUOTE_EXPR {
        return None;
    }
    let template = body_of(&quoted)?;
    let mut statements = template.children();
    let structure = statements.next()?;
    if structure.kind() != SyntaxKind::STRUCT_DEF {
        return None;
    }
    let mut head = signature_start(&structure)?;
    if head.kind() == SyntaxKind::BINARY_EXPR && super::has_subtype(&head) {
        head = head.children().next()?;
    }
    let head = interpolated_base(Expr::cast(head)?)?;
    if !is_template_arg(&head, parameter.text()) {
        return None;
    }
    // Definition-shaped trailing statements are allowed only when their
    // callee is the same template name. No arbitrary quote-time evaluation.
    for statement in statements {
        if !is_short_form_def(&statement) {
            return None;
        }
        let (signature, _, _) = peel_signature(statement.children().next()?);
        let callee = CallExpr::cast(signature?)?.callee()?;
        if !is_template_arg(&interpolated_base(callee)?, parameter.text()) {
            return None;
        }
    }
    // All interpolation in the result must be the parameter, or esc(parameter).
    // Evaluating other expressions could alter the template before emitting it.
    if quoted
        .descendants()
        .filter_map(Interpolation::cast)
        .any(|interpolated| !is_template_arg(&interpolated, parameter.text()))
    {
        return None;
    }
    Some((node_name_text(argument)?, argument.text_range(), structure))
}

fn only_child(node: &SyntaxNode) -> Option<SyntaxNode> {
    let mut children = node.children();
    let first = children.next()?;
    children.next().is_none().then_some(first)
}

fn interpolated_base(expr: Expr) -> Option<Interpolation> {
    match expr {
        Expr::Interpolation(node) => Some(node),
        Expr::CurlyExpr(curly) => match curly.base()? {
            Expr::Interpolation(node) => Some(node),
            _ => None,
        },
        _ => None,
    }
}

fn is_template_arg(arg: &Interpolation, name: &str) -> bool {
    if is_loop_name(arg, name) {
        return true;
    }
    let Some(Expr::CallExpr(call)) = arg.expr().and_then(unparenthesized) else {
        return false;
    };
    let Some(Expr::Name(callee)) = call.callee() else {
        return false;
    };
    if !callee.ident().is_some_and(|i| i.text() == "esc") {
        return false;
    }
    let Some(args) = call.arg_list() else {
        return false;
    };
    let mut iter = args.args();
    matches!(
        iter.next().and_then(|arg| arg.expr()),
        Some(Expr::Name(var)) if var.ident().is_some_and(|i| i.text() == name)
    ) && iter.next().is_none()
}
