use std::collections::{BTreeMap, HashSet};

use fatou::lsp::compute_completions;
use fatou::text::{LineIndex, PositionEncoding};

fn completions_at(marked: &str) -> HashSet<String> {
    let offset = marked.find('|').expect("cursor mark");
    let source = marked.replacen('|', "", 1);
    let position = LineIndex::new(&source).byte_to_position(offset, PositionEncoding::Utf16);
    compute_completions(&source, position, PositionEncoding::Utf16, &BTreeMap::new())
        .into_iter()
        .map(|item| item.label)
        .collect()
}

fn check(marked: &str, expected: &[&str], forbidden: &[&str]) {
    let items = completions_at(marked);
    for &label in expected {
        assert!(items.contains(label), "missing {label} in {marked:?}");
    }
    for &label in forbidden {
        assert!(!items.contains(label), "unexpected {label} in {marked:?}");
    }
}

#[test]
fn let_and_loop_initializers_offer_only_existing_bindings() {
    check("let waitlocal = |\n  0\nend", &[], &["waitlocal"]);
    check("for waitlocal in |\n  0\nend", &[], &["waitlocal"]);
    check(
        "let firstlocal=1, secondlocal=firstl|\n  secondlocal\nend",
        &["firstlocal"],
        &["secondlocal"],
    );
    check("let newlocal=newl|\n  newlocal\nend", &[], &["newlocal"]);
    check(
        "outerlocal=1\nlet outerlocal=outerl|\n  outerlocal\nend",
        &["outerlocal"],
        &[],
    );
    check(
        "let outerlocal=1, nextlocal=map(innerlocal -> innerl|, [1])\n  nextlocal\nend",
        &["innerlocal", "outerlocal"],
        &["nextlocal"],
    );
    check(
        "for indexfirst in 1:2, indexsecond in (1:indexf|)\n  indexsecond\nend",
        &["indexfirst"],
        &["indexsecond"],
    );
    check(
        "for indexfirst in 1:2, indexsecond in 3:4\n  indexs|\nend",
        &["indexfirst", "indexsecond"],
        &[],
    );
}

#[test]
fn comprehension_and_generator_head_use_clause_bindings() {
    check("[iterl| for iterlocal in 1:3]", &["iterlocal"], &[]);
    check("sum(iterl| for iterlocal in 1:3)", &["iterlocal"], &[]);
    check(
        "Int[innerl| for outerlocal in 1:3 for innerlocal in 1:outerlocal]",
        &["innerlocal", "outerlocal"],
        &[],
    );
    check(
        "[map(innerlocal -> innerl|, [1]) for iterlocal in 1:3]",
        &["iterlocal", "innerlocal"],
        &[],
    );
    check(
        "[secondlocal for firstlocal in 1:2 for secondlocal in 1:firstl|]",
        &["firstlocal"],
        &["secondlocal"],
    );
    check(
        "[iterlocal for iterlocal in 1:3 if iterl| > 1]",
        &["iterlocal"],
        &[],
    );
    check(
        "[iterlocal for iterlocal in 1:3]\niterl|",
        &[],
        &["iterlocal"],
    );
}

#[test]
fn defaults_offer_only_preceding_parameters_and_enclosing_bindings() {
    check(
        "f(firstlocal, waitinglocal= | ) = firstlocal",
        &["firstlocal"],
        &["waitinglocal"],
    );
    check(
        "f(firstlocal, secondlocal=firstl|, thirdlocal=1) = firstlocal",
        &["firstlocal"],
        &["secondlocal", "thirdlocal"],
    );
    check(
        "f(firstlocal; beforelocal=1, nextlocal=(firstl|), laterlocal=3) = firstlocal",
        &["firstlocal", "beforelocal"],
        &["nextlocal", "laterlocal"],
    );
    check(
        "shadowlocal=7\nfunction f(firstlocal, shadowlocal=map(innerlocal -> innerl|, [1]))\n  bodylocal = 2\nend",
        &["shadowlocal", "firstlocal", "innerlocal"],
        &["bodylocal"],
    );
    check(
        "function f()\n  las|\n  lastlocal=1\nend",
        &["lastlocal"],
        &[],
    );
}
