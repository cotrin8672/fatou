//! Deliberately bounded source-only include discovery. A supported loop has
//! one name, literal string values and a body of include calls only. We do not
//! evaluate package code, call Julia, or follow loop expansions out of the
//! package tree.

use std::path::PathBuf;

use crate::ast::{
    Arg, AstNode, AstToken, CallExpr, Expr, ForBinding, ForExpr, HasArgList, HasBody, Interpolation,
};
use crate::syntax::{SyntaxKind, SyntaxNode};

const MAX_VALUES: usize = 256;
const MAX_CALLS: usize = 8;
const MAX_BYTES: usize = 4096;

pub(super) fn literal_loop_paths(node: &SyntaxNode, siblings: &SyntaxNode) -> Option<Vec<String>> {
    let body = ForExpr::cast(node.clone())?.body()?;
    let mut bindings = node.children().filter_map(ForBinding::cast);
    let binding = bindings.next()?;
    if bindings.next().is_some() || binding.syntax().children().count() != 2 {
        return None;
    }
    let Expr::Name(var) = binding.pattern()? else {
        return None;
    };
    let var = var.ident()?;
    let calls = body
        .syntax()
        .children()
        .take(MAX_CALLS + 1)
        .map(CallExpr::cast)
        .collect::<Option<Vec<_>>>()?;
    if calls.is_empty()
        || calls.len() > MAX_CALLS
        || !calls
            .iter()
            .all(|c| include_path(c, Some((var.text(), "sample"))).is_some())
    {
        return None;
    }
    let iterable = binding.iterable()?;
    let values = if let Expr::Name(name) = iterable {
        local_constant_values(siblings, node, name.ident()?.text())?
    } else {
        literal_values(iterable)?
    };
    values
        .iter()
        .flat_map(|value| {
            calls
                .iter()
                .map(|call| include_path(call, Some((var.text(), value))))
        })
        .collect()
}

fn local_constant_values(
    siblings: &SyntaxNode,
    target: &SyntaxNode,
    name: &str,
) -> Option<Vec<String>> {
    let mut result = None;
    for statement in siblings.children().take_while(|item| item != target) {
        if statement.kind() == SyntaxKind::CONST_STMT
            && let Some(assign) = statement.children().next()
            && assign.kind() == SyntaxKind::ASSIGNMENT_EXPR
        {
            let mut pair = assign.children();
            if let Some(Expr::Name(lhs)) = pair.next().and_then(Expr::cast)
                && lhs.ident().is_some_and(|i| i.text() == name)
            {
                result = literal_values(Expr::cast(pair.next()?)?);
                continue;
            }
        }
        // Julia const doesn't freeze a Vector's contents. Reject intervening
        // syntactic uses that may mutate or escape the binding (e.g. push!).
        if result.is_some()
            && statement
                .descendants_with_tokens()
                .filter_map(|e| e.into_token())
                .any(|t| t.kind() == SyntaxKind::IDENT && t.text() == name)
        {
            result = None;
        }
    }
    result
}

fn literal_values(expr: Expr) -> Option<Vec<String>> {
    if !matches!(expr, Expr::TupleExpr(_) | Expr::VectExpr(_)) {
        return None;
    }
    let all = expr
        .syntax()
        .children()
        .take(MAX_VALUES + 1)
        .map(|child| {
            let Expr::StringLiteral(text) = Arg::cast(child)?.expr()? else {
                return None;
            };
            if text.prefix().is_some() || text.interpolations().next().is_some() {
                return None;
            }
            let value = crate::project::literal_path(&text)?;
            // Loop elements must be portable, inert names; separators/traversal
            // must be explicitly spelled in the path syntax, never injected.
            (!value.is_empty()
                && value
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-'))
            .then_some(value)
        })
        .collect::<Option<Vec<_>>>()?;
    (!all.is_empty() && all.len() <= MAX_VALUES).then_some(all)
}

pub(super) fn include_path(call: &CallExpr, binding: Option<(&str, &str)>) -> Option<String> {
    if !named(call, "include") {
        return None;
    }
    let mut args = call.arg_list()?.args();
    let expr = args.next()?.expr()?;
    if args.next().is_some() {
        return None;
    }
    if let Expr::CallExpr(join) = expr {
        if !named(&join, "joinpath") {
            return None;
        }
        let mut path = PathBuf::new();
        let mut count = 0;
        for arg in join.arg_list()?.args() {
            count += 1;
            if count > 16 {
                return None;
            }
            let part = string(arg.expr()?, binding)?;
            if part.contains(['\\', ':', '\0']) || PathBuf::from(&part).is_absolute() {
                return None;
            }
            path.push(part);
        }
        let path = path.to_str()?;
        (!path.is_empty() && path.len() <= MAX_BYTES).then(|| path.to_string())
    } else {
        string(expr, binding)
    }
}

fn named(call: &CallExpr, want: &str) -> bool {
    matches!(call.callee(), Some(Expr::Name(n)) if n.ident().is_some_and(|i| i.text() == want))
}

fn string(expr: Expr, binding: Option<(&str, &str)>) -> Option<String> {
    let Expr::StringLiteral(literal) = expr else {
        return None;
    };
    // Triple-quote indentation and prefix macros are not part of this grammar.
    if literal.prefix().is_some()
        || literal.suffix().is_some()
        || literal.syntax().text().to_string().starts_with("\"\"\"")
    {
        return None;
    }
    let mut text = String::new();
    for el in literal.syntax().children_with_tokens() {
        match el {
            rowan::NodeOrToken::Token(t) if t.kind() == SyntaxKind::STRING_CONTENT => {
                text.push_str(&crate::parser::string_value(t.text()).ok()?);
            }
            rowan::NodeOrToken::Token(_) => {}
            rowan::NodeOrToken::Node(n) => {
                let interpolated = Interpolation::cast(n)?;
                let (variable, value) = binding?;
                let matches = interpolated.ident().is_some_and(|i| i.text() == variable)
                    || matches!(interpolated.expr().and_then(unparenthesized), Some(Expr::Name(n))
                        if n.ident().is_some_and(|i| i.text() == variable));
                if !matches {
                    return None;
                }
                text.push_str(value);
            }
        }
        if text.len() > MAX_BYTES {
            return None;
        }
    }
    (!text.is_empty()).then_some(text)
}

fn unparenthesized(mut expr: Expr) -> Option<Expr> {
    while let Expr::ParenExpr(paren) = expr {
        expr = paren.expr()?;
    }
    Some(expr)
}
