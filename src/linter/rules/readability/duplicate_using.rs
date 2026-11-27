//! Report identical, unconditional `using` entries in one module/file.
//! Julia permits repeating a load; this is a readability warning, not a
//! runtime error or an assertion that two different exports are ambiguous.

use std::collections::HashSet;

use crate::linter::diagnostic::{Diagnostic, Severity};
use crate::linter::rules::{Example, Rule, RuleContext};
use crate::semantic::LoadKind;
use crate::syntax::SyntaxKind;

pub struct DuplicateUsing;

impl Rule for DuplicateUsing {
    fn id(&self) -> &'static str {
        "duplicate-using"
    }

    fn default_severity(&self) -> Severity {
        Severity::Warning
    }

    fn description(&self) -> &'static str {
        "Report an identical `using` entry repeated in the same module and file. Distinct modules, names, and aliases are not duplicates."
    }

    fn examples(&self) -> &'static [Example] {
        &[Example {
            caption: "The second `sin` repeats the original entry:",
            source: "using Base: sin, sin\n",
        }]
    }

    fn check_file(&self, ctx: &RuleContext<'_>, sink: &mut Vec<Diagnostic>) {
        let mut seen = HashSet::new();
        for load in ctx
            .model
            .module_loads()
            .iter()
            .filter(|load| load.kind == LoadKind::Using)
        {
            let Some(at) = load.root_range.map(|range| range.start()) else {
                continue;
            };
            let Some(token) = ctx.root.token_at_offset(at).right_biased() else {
                continue;
            };
            let Some(stmt) = token
                .parent_ancestors()
                .find(|node| node.kind() == SyntaxKind::USING_STMT)
            else {
                continue;
            };
            if stmt
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::INTERPOLATION | SyntaxKind::ERROR))
            {
                continue;
            }
            let unconditional = stmt.ancestors().skip(1).all(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::ROOT
                        | SyntaxKind::MODULE_DEF
                        | SyntaxKind::BLOCK
                        | SyntaxKind::BEGIN_EXPR
                )
            });
            let path = (
                load.scope,
                load.path.leading_dots,
                load.path.components.as_slice(),
            );
            let mut within_clause = HashSet::new();
            if let Some(items) = &load.items {
                for item in items {
                    let binding = Some((&item.name, item.alias.as_ref().unwrap_or(&item.name)));
                    if !within_clause.insert(binding)
                        || (unconditional && !seen.insert((path, binding)))
                    {
                        sink.push(Diagnostic::new(
                            self.id(),
                            item.range,
                            format!("duplicate using entry `{}`", item.name),
                        ));
                    }
                }
            } else if load.alias.is_none() && unconditional && !seen.insert((path, None)) {
                sink.push(Diagnostic::new(
                    self.id(),
                    load.range,
                    "duplicate using of the same module",
                ));
            }
        }
    }
}
