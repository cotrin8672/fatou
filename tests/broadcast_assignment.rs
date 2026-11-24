//! Mutating elements does not bind a local name, including the bitwise forms.

use fatou::parser::parse;
use fatou::semantic::SemanticModel;

#[test]
fn dotted_updates_read_the_outer_binding() {
    for op in [".=", ".+=", ".&=", ".|=", ".⊻="] {
        let src = format!("gain = [4, 6]\nfunction run()\n    gain {op} 1\n    gain\nend\n");
        let parsed = parse(&src);
        assert!(parsed.diagnostics.is_empty(), "{op}: {:?}", parsed.diagnostics);
        let model = SemanticModel::build(&parsed.cst);
        let bindings: Vec<_> = model.bindings().iter().filter(|b| b.name == "gain").collect();
        assert_eq!(bindings.len(), 1, "{op} must not bind a new local");
        assert!(bindings[0].read, "{op} must read the existing binding");
    }
}
