//! Explicit, non-executing Julia compiler snapshot transport.
//! An editor supplies a snapshot after the user chooses an already trusted
//! Julia session. No filesystem discovery, package loading, or Julia child
//! process is initiated by opening a file or requesting inlay hints.

use std::path::Path;

use lsp_types::{InlayHint, InlayHintKind, InlayHintLabel, InlayHintTooltip, Range, Uri};
use serde::Deserialize;

use crate::parser::{is_ident_continue, is_ident_start};
use crate::text::{PositionEncoding, TextBuffer};

pub(super) const TARGET: &str = "fatou/compilerHintsTarget";
pub(super) const IMPORT: &str = "fatou/compilerHintsImport";
pub(super) const CLEAR: &str = "fatou/compilerHintsClear";

const MAX_SOURCE_BYTES: usize = 1_048_576;
const MAX_HINTS: usize = 256;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct Target {
    pub(super) uri: Uri,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct Import {
    pub(super) uri: Uri,
    pub(super) version: i32,
    pub(super) ticket: String,
    pub(super) snapshot: CompilerReport,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct CompilerReport {
    source: String,
    source_path: String,
    julia_version: String,
    world: String,
    signature: String,
    hints: Vec<ReportHint>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ReportHint {
    start_byte: usize,
    end_byte: usize,
    anchor: String,
    inferred_type: String,
    kind: HintKind,
}

#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "camelCase")]
enum HintKind {
    Assignment,
    Return,
}

pub(super) struct ImportedHints {
    pub(super) uri: Uri,
    pub(super) version: i32,
    hints: Vec<InlayHint>,
}

fn safe_display(s: &str, limit: usize) -> bool {
    !s.is_empty()
        && s.len() <= limit
        && !s.chars().any(|c| {
            c.is_control()
                || matches!(c, '\u{061c}' | '\u{200b}'..='\u{200f}' | '\u{2028}'..='\u{202e}'
                    | '\u{2060}'..='\u{2069}' | '\u{feff}')
        })
}

impl ImportedHints {
    pub(super) fn validate(
        uri: Uri,
        version: i32,
        snapshot: CompilerReport,
        buffer: &TextBuffer,
        encoding: PositionEncoding,
    ) -> Result<Self, &'static str> {
        // Exact UTF-8 equality is stronger than a non-cryptographic hash, and
        // the client does not supply a file path for the server to open.
        if snapshot.source.len() > MAX_SOURCE_BYTES {
            return Err("compiler hints source exceeds 1 MiB");
        }
        let reported = Path::new(&snapshot.source_path);
        if !reported.is_absolute() || !safe_display(&snapshot.source_path, 4096) {
            return Err("invalid absolute compiler source path");
        }
        // Round-trip through the existing URI codec to remove Windows'
        // verbatim/UNC spelling differences without touching disk.
        let normal = |path: &Path| {
            super::uri::from_path(path)
                .and_then(|uri| super::uri::to_path(&uri))
                .map(|p| crate::incremental::normalize_path(&p))
        };
        if normal(reported)
            .zip(super::uri::to_path(&uri).and_then(|p| normal(&p)))
            .is_none_or(|(a, b)| a != b)
        {
            return Err("compiler hints source path does not match the target URI");
        }
        if snapshot.source != buffer.text() {
            return Err("compiler hints source does not match the current buffer");
        }
        if snapshot.hints.len() > MAX_HINTS
            || !safe_display(&snapshot.julia_version, 64)
            || !safe_display(&snapshot.signature, 512)
            || snapshot.world.is_empty()
            || snapshot.world.len() > 24
            || !snapshot.world.bytes().all(|b| b.is_ascii_digit())
        {
            return Err("invalid compiler hints snapshot metadata");
        }
        let lines = buffer.line_index();
        let mut hints = Vec::with_capacity(snapshot.hints.len());
        for hint in snapshot.hints {
            if !safe_display(&hint.anchor, 256)
                || !safe_display(&hint.inferred_type, 512)
                || hint.start_byte >= hint.end_byte
                || buffer.text().get(hint.start_byte..hint.end_byte) != Some(hint.anchor.as_str())
            {
                return Err("compiler hint has an invalid source anchor or label");
            }
            let before = buffer.text()[..hint.start_byte]
                .rsplit('\n')
                .next()
                .unwrap_or("");
            let after = buffer.text()[hint.end_byte..]
                .split('\n')
                .next()
                .unwrap_or("");
            let role = match hint.kind {
                HintKind::Assignment => {
                    let mut chars = hint.anchor.chars();
                    let after = after.trim_start_matches([' ', '\t']);
                    if !chars.next().is_some_and(is_ident_start)
                        || !chars.all(is_ident_continue)
                        || !before.chars().all(|c| matches!(c, ' ' | '\t'))
                        || !after.starts_with('=')
                        || after.starts_with("==")
                        || after.starts_with("=>")
                    {
                        return Err("compiler hint has an invalid assignment anchor");
                    }
                    "assignment"
                }
                HintKind::Return => {
                    if hint.anchor != ")"
                        || !before.trim_start().starts_with("function ")
                        || !after.trim().is_empty()
                    {
                        return Err("compiler return hint must follow a simple function header");
                    }
                    "return"
                }
            };
            let explanation = match hint.inferred_type.as_str() {
                "Any" | "Core.Any" => {
                    "\nInference did not narrow this result beyond Any for this call signature."
                }
                "Union{}" => {
                    "\nThe compiler inferred no normal return for this call signature. This does not imply that it always throws."
                }
                _ => "",
            };
            let position = lines.byte_to_position(hint.end_byte, encoding);
            let mut chars = hint.inferred_type.chars();
            let mut compact: String = chars.by_ref().take(58).collect();
            if chars.next().is_some() {
                compact.push('…');
            }
            let tooltip = format!(
                "Julia compiler snapshot (inferred {role}): {}\nSpecialization (explicit argument types): {}\nJulia {} (world {}){explanation}",
                hint.inferred_type, snapshot.signature, snapshot.julia_version, snapshot.world,
            );
            hints.push(InlayHint {
                position,
                label: InlayHintLabel::String(format!("::{compact}")),
                kind: Some(InlayHintKind::TYPE),
                text_edits: None,
                tooltip: Some(InlayHintTooltip::String(tooltip)),
                padding_left: None,
                padding_right: None,
                data: None,
            });
        }
        hints.sort_by_key(|x| (x.position.line, x.position.character));
        if hints.windows(2).any(|w| w[0].position == w[1].position) {
            return Err("multiple compiler hints at the same source position");
        }
        Ok(Self {
            uri,
            version,
            hints,
        })
    }

    pub(super) fn len(&self) -> usize {
        self.hints.len()
    }

    pub(super) fn in_range(&self, range: Range) -> impl Iterator<Item = &InlayHint> {
        let key = |p: lsp_types::Position| (p.line, p.character);
        let start = key(range.start);
        let end = key(range.end);
        self.hints
            .iter()
            .filter(move |hint| (start..end).contains(&key(hint.position)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::Position;
    use serde_json::json;

    fn uri() -> Uri {
        super::super::uri::from_path(&std::env::temp_dir().join("Test.jl")).unwrap()
    }

    fn report(source: &str, hints: serde_json::Value) -> CompilerReport {
        serde_json::from_value(json!({
            "source": source, "sourcePath": super::super::uri::to_path(&uri()).unwrap(), "juliaVersion": "1.13.4", "world": "12345",
            "signature": "Example.f Tuple{Float64}", "hints": hints,
        }))
        .unwrap()
    }

    #[test]
    fn exact_unicode_anchor_encoded_for_client() {
        let uri = uri();
        let source = "𐐀 = 4\n";
        let hints = json!([{
            "startByte": 0, "endByte": 4, "anchor": "𐐀",
            "inferredType": "Int64", "kind": "assignment"
        }]);
        for (encoding, character) in [(PositionEncoding::Utf8, 4), (PositionEncoding::Utf16, 2)] {
            let snapshot = ImportedHints::validate(
                uri.clone(),
                7,
                report(source, hints.clone()),
                &TextBuffer::from(source),
                encoding,
            )
            .unwrap();
            let range = Range::new(Position::new(0, 0), Position::new(1, 0));
            let hint = snapshot.in_range(range).next().unwrap();
            assert_eq!(hint.position, Position::new(0, character));
            assert_eq!(hint.kind, Some(InlayHintKind::TYPE));
            assert!(hint.text_edits.is_none());
            assert!(matches! {&hint.label, InlayHintLabel::String(label) if label == "::Int64"});
        }
    }

    #[test]
    fn accepts_julia_combining_and_prime_names_without_extra_ellipsis() {
        for anchor in ["ûₖ", "P̃ₖᵘ", "δ′"] {
            let source = format!("{anchor} = 4\n");
            let hints = json!([{
                "startByte": 0, "endByte": anchor.len(), "anchor": anchor,
                "inferredType": "型", "kind": "assignment"
            }]);
            let snapshot = ImportedHints::validate(
                uri(),
                7,
                report(&source, hints),
                &TextBuffer::from(source.as_str()),
                PositionEncoding::Utf16,
            )
            .unwrap();
            let range = Range::new(Position::new(0, 0), Position::new(1, 0));
            let hint = snapshot.in_range(range).next().unwrap();
            assert_eq!(
                hint.position.character as usize,
                anchor.encode_utf16().count()
            );
            assert!(matches!(&hint.label, InlayHintLabel::String(label) if label == "::型"));
        }
    }

    #[test]
    fn reject_dirty_source_non_boundary_and_duplicate_anchors() {
        let uri = uri();
        let source = "β = 4\n";
        let buffer = TextBuffer::from(source);
        let hint = json!({
            "startByte": 0, "endByte": 2, "anchor": "β",
            "inferredType": "Int64", "kind": "assignment"
        });
        let check = |text, hints| {
            ImportedHints::validate(
                uri.clone(),
                2,
                report(text, hints),
                &buffer,
                PositionEncoding::Utf16,
            )
        };
        assert!(check("β = 5\n", json!([hint.clone()])).is_err());
        assert!(check(source, json!([hint.clone(), hint.clone()])).is_err());
        let mut split = hint.clone();
        split["endByte"] = json!(1);
        assert!(check(source, json!([split])).is_err());
        let mut unprintable = hint.clone();
        unprintable["inferredType"] = json!("Int64\u{202e}");
        assert!(check(source, json!([unprintable])).is_err());
        let range = Range::new(Position::new(0, 0), Position::new(1, 0));
        for (name, expected) in [
            ("Any", Some("did not narrow")),
            ("Union{}", Some("no normal return")),
            ("Union{Nothing, Int64}", None),
        ] {
            let mut found = hint.clone();
            found["inferredType"] = json!(name);
            let report = check(source, json!([found])).unwrap();
            let actual = report.in_range(range).next().unwrap();
            assert!(
                matches!(&actual.label, InlayHintLabel::String(label) if label == &format!("::{name}"))
            );
            let Some(InlayHintTooltip::String(tooltip)) = &actual.tooltip else {
                panic!("missing plain inference tooltip");
            };
            if let Some(phrase) = expected {
                assert!(tooltip.contains(phrase));
            } else {
                assert!(
                    !tooltip.contains("did not narrow") && !tooltip.contains("no normal return")
                );
            }
        }
        assert_eq!(check(source, json!([])).unwrap().len(), 0);
    }
}
