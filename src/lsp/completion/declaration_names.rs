//! Positive-only gates for identifier tokens that introduce a new name.
//! An ambiguous expression or an empty slot keeps normal completion.
use rowan::{TextRange, TextSize};

use crate::semantic::{BindingKind, SemanticModel};
use crate::syntax::{SyntaxKind, SyntaxNode};

use super::super::symbols::{is_trivia, op_token};

pub(super) fn introduces_name(root: &SyntaxNode, model: &SemanticModel, offset: TextSize) -> bool {
    let Some(token) = root.token_at_offset(offset).left_biased() else {
        return false;
    };
    let range = token.text_range();
    if token.kind() != SyntaxKind::IDENT || offset <= range.start() || offset > range.end() {
        return false;
    }
    let Some(name) = token
        .parent()
        .filter(|node| node.kind() == SyntaxKind::NAME)
    else {
        return false;
    };

    // Avoid scanning the binding arena for ordinary references in a body.
    // None of the supported syntactic name slots cross a block boundary.
    let mut possible_declaration = false;
    let mut crossed_body = false;
    let mut in_for_header = false;
    for node in name.ancestors() {
        match node.kind() {
            SyntaxKind::ROOT => break,
            SyntaxKind::BLOCK => crossed_body = true,
            SyntaxKind::ERROR
            | SyntaxKind::QUOTE_EXPR
            | SyntaxKind::QUOTE_SYM
            | SyntaxKind::INTERPOLATION => return false,
            SyntaxKind::FOR_BINDING if !crossed_body => in_for_header = true,
            SyntaxKind::DO_PARAMS
            | SyntaxKind::SIGNATURE
            | SyntaxKind::ARROW_EXPR
            | SyntaxKind::ASSIGNMENT_EXPR
            | SyntaxKind::LET_BINDINGS
            | SyntaxKind::CATCH_CLAUSE
            | SyntaxKind::LOCAL_STMT
                if !crossed_body =>
            {
                possible_declaration = true
            }
            _ => {}
        }
    }
    if is_explicit_named_tuple_key(&name)
        || (in_for_header && is_iteration_binding_name(name.clone(), range))
    {
        return true;
    }
    if !possible_declaration {
        return false;
    }
    let Some(binding) = model
        .binding_at(offset)
        .map(|id| model.binding(id))
        .filter(|binding| binding.def_range == range)
    else {
        return false;
    };

    match binding.kind {
        BindingKind::Param
        | BindingKind::KeywordParam
        | BindingKind::LetVar
        | BindingKind::CatchParam => true,
        BindingKind::Local => explicit_local_pattern(name),
        _ => false,
    }
}

/// Walk only the pattern's own syntactic children, then require the
/// iteration separator in that same clause. In the flat CST the equals form
/// is a single assignment node, whereas the other forms have the separator
/// between distinct nodes; this also handles mixed multi-clause headers.
fn is_iteration_binding_name(name: SyntaxNode, range: TextRange) -> bool {
    let mut clause = name;
    while let Some(parent) = clause.parent() {
        match parent.kind() {
            SyntaxKind::OUTER_BINDING | SyntaxKind::BLOCK | SyntaxKind::ROOT => return false,
            SyntaxKind::FOR_BINDING => {
                if clause.kind() == SyntaxKind::ASSIGNMENT_EXPR {
                    return op_token(&clause).is_some_and(|op| op.kind() == SyntaxKind::EQ)
                        && clause
                            .first_child()
                            .is_some_and(|child| child.text_range().contains_range(range));
                }
                return clause
                    .siblings_with_tokens(rowan::Direction::Next)
                    .skip(1)
                    .find(|element| {
                        !element
                            .as_token()
                            .is_some_and(|token| is_trivia(token.kind()))
                    })
                    .and_then(|element| element.into_token())
                    .is_some_and(|token| {
                        (token.kind() == SyntaxKind::IDENT && token.text() == "in")
                            || (token.kind().is_operator() && token.text() == "∈")
                    });
            }
            _ if contains_pattern_child(&parent, &clause) => clause = parent,
            _ => return false,
        }
    }
    false
}

/// A local assignment also creates a binding in the semantic model. Only an
/// explicit local declaration is covered here, and never its initializer.
fn explicit_local_pattern(mut pattern: SyntaxNode) -> bool {
    while let Some(parent) = pattern.parent() {
        if parent.kind() == SyntaxKind::LOCAL_STMT {
            return true;
        }
        if !contains_pattern_child(&parent, &pattern) {
            return false;
        }
        pattern = parent;
    }
    false
}

/// A wrapper that can continue a pattern, not an expression evaluated in
/// the same syntax (such as the right child of an initializer or annotation).
fn contains_pattern_child(parent: &SyntaxNode, pattern: &SyntaxNode) -> bool {
    match parent.kind() {
        SyntaxKind::ASSIGNMENT_EXPR | SyntaxKind::TYPE_ANNOTATION => {
            parent.first_child().as_ref() == Some(pattern)
        }
        SyntaxKind::TUPLE_EXPR
        | SyntaxKind::BARE_TUPLE_EXPR
        | SyntaxKind::PARAMETERS
        | SyntaxKind::ARG
        | SyntaxKind::SPLAT_EXPR
        | SyntaxKind::PAREN_EXPR => true,
        _ => false,
    }
}

/// An explicit field in a tuple expression is a new key, not a read of the
/// same spelling. A parenthesized assignment and a call's argument list
/// are distinct CST shapes. With no semicolon require entirely named items.
fn is_explicit_named_tuple_key(name: &SyntaxNode) -> bool {
    let Some(field) = name.parent() else {
        return false;
    };
    if field.kind() != SyntaxKind::KEYWORD_ARG
        || field.first_child().as_ref() != Some(name)
        || !op_token(&field).is_some_and(|op| op.kind() == SyntaxKind::EQ)
    {
        return false;
    }
    let Some(group) = field.parent() else {
        return false;
    };
    match group.kind() {
        SyntaxKind::PARAMETERS => group
            .parent()
            .is_some_and(|tuple| tuple.kind() == SyntaxKind::TUPLE_EXPR),
        SyntaxKind::TUPLE_EXPR => group
            .children()
            .all(|child| child.kind() == SyntaxKind::KEYWORD_ARG),
        _ => false,
    }
}
