//! File-local Markdown navigation derived only from static docstring payloads.
//!
//! Definitions retain decoded offsets and static-payload ordinals. Source maps
//! belong to the current semantic model, so moving or re-escaping a docstring
//! does not invalidate Markdown parsing or leave cached source positions stale.

use std::collections::{BTreeMap, HashSet};
use std::sync::{Arc, OnceLock};

use fatou_parser::ast::{DocText, StaticDocText};
use fatou_parser::documentation::ast::{DocumenterLinkKind, FootnoteDefinition, Heading, Link};
use rowan::TextRange;
use rowan::ast::AstNode as _;

use crate::semantic::{SemanticDoc, SemanticModel};

/// Lazy GreenNodes over a stable sequence of decoded payloads. Source maps
/// remain in the current semantic model, so body edits and document movement
/// do not force a Markdown reparse. Only the requested payload is parsed.
pub(crate) struct DocumentationTrees {
    payloads: Arc<[String]>,
    trees: Vec<OnceLock<rowan::GreenNode>>,
}

impl DocumentationTrees {
    pub(crate) fn new(payloads: Arc<[String]>) -> Self {
        let trees = (0..payloads.len()).map(|_| OnceLock::new()).collect();
        Self { payloads, trees }
    }

    pub(crate) fn tree(
        &self,
        ordinal: usize,
        text: &str,
    ) -> Option<fatou_parser::documentation::syntax::SyntaxNode> {
        let payload = self.payloads.get(ordinal)?;
        if payload != text {
            return None;
        }
        let tree = self.trees[ordinal].get_or_init(|| {
            fatou_parser::documentation::parse(payload)
                .cst
                .green()
                .to_owned()
        });
        Some(fatou_parser::documentation::syntax::SyntaxNode::new_root(
            tree.clone(),
        ))
    }
}

impl PartialEq for DocumentationTrees {
    fn eq(&self, other: &Self) -> bool {
        self.payloads == other.payloads
    }
}

impl Eq for DocumentationTrees {}

#[cfg(test)]
#[test]
fn decoded_documentation_trees_are_lazy_and_match_the_current_payload() {
    let trees = DocumentationTrees::new(Arc::from([
        String::from("# First"),
        String::from("# Second"),
    ]));
    assert!(trees.trees.iter().all(|tree| tree.get().is_none()));
    assert!(trees.tree(0, "# Wrong").is_none());
    let first = trees.tree(0, "# First").unwrap();
    let again = trees.tree(0, "# First").unwrap();
    assert_eq!(first.to_string(), "# First");
    assert!(std::ptr::eq(first.green(), again.green()));
    assert!(trees.trees[1].get().is_none());
}

/// A Markdown destination in the current Julia file.
pub enum MarkdownReference {
    Anchor(String),
    Footnote(String),
}

#[derive(Debug, PartialEq, Eq)]
struct Definition {
    payload: usize,
    range: TextRange,
}

/// Anchor names and definitions, independent of Julia source positions.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct DocumentationIndex {
    names: Vec<String>,
    anchors: BTreeMap<String, Vec<Definition>>,
    footnotes: BTreeMap<String, Vec<Definition>>,
}

impl DocumentationIndex {
    /// Parse static payloads in source order, preserving first-match navigation
    /// and completion order, including heading text, slugs, and explicit IDs.
    pub fn build<'a>(payloads: impl IntoIterator<Item = &'a str>) -> Self {
        let mut index = Self::default();
        let mut seen = HashSet::new();
        for (payload, text) in payloads.into_iter().enumerate() {
            let markdown = fatou_parser::documentation::parse(text);
            for node in markdown.cst.descendants() {
                if let Some(link) = Link::cast(node.clone())
                    && let Some(documenter) = link.documenter_link()
                    && documenter.kind() == DocumenterLinkKind::Id
                    && let Some(target) = documenter.target()
                {
                    if seen.insert(target.to_string()) {
                        index.names.push(target.to_string());
                    }
                    if let Some(range) = documenter.target_range() {
                        insert_definition(&mut index.anchors, target.to_string(), payload, range);
                    }
                }
                if let Some(heading) = Heading::cast(node.clone()) {
                    for name in [heading.content(), heading.slug()] {
                        if !name.is_empty() && seen.insert(name.clone()) {
                            index.names.push(name.clone());
                        }
                        insert_definition(&mut index.anchors, name, payload, node.text_range());
                    }
                }
                if let Some(footnote) = FootnoteDefinition::cast(node) {
                    insert_definition(
                        &mut index.footnotes,
                        footnote.id(),
                        payload,
                        footnote.syntax().text_range(),
                    );
                }
            }
        }
        index
    }

    /// Unique completion names in their original traversal order.
    pub fn anchor_names(&self) -> &[String] {
        &self.names
    }

    /// Map the first matching definition through the current source maps.
    /// `model` must have the static payload sequence used to build this index.
    pub fn definition(
        &self,
        model: &SemanticModel,
        reference: &MarkdownReference,
    ) -> Option<TextRange> {
        let definitions = match reference {
            MarkdownReference::Anchor(id) => self.anchors.get(id),
            MarkdownReference::Footnote(id) => self.footnotes.get(id),
        }?;
        let mut documents = static_documentation(model).enumerate();
        for definition in definitions {
            let (_, (_, decoded)) =
                documents.find(|(ordinal, _)| *ordinal == definition.payload)?;
            if let Some(source) = decoded.source_map().source_range(definition.range) {
                return Some(source);
            }
        }
        None
    }
}

fn insert_definition(
    definitions: &mut BTreeMap<String, Vec<Definition>>,
    name: String,
    payload: usize,
    range: TextRange,
) {
    let entries = definitions.entry(name).or_default();
    // A failed source mapping falls through to the next docstring, never to
    // a later match in the same one.
    if entries.last().is_none_or(|entry| entry.payload != payload) {
        entries.push(Definition { payload, range });
    }
}

/// Iterate statically decoded attachments in source order. Opaque attachments
/// must not affect the ordinals used by the payload projection.
pub(crate) fn static_documentation(
    model: &SemanticModel,
) -> impl Iterator<Item = (&SemanticDoc, &StaticDocText)> {
    model
        .documentation()
        .iter()
        .filter_map(|doc| match &doc.text {
            DocText::Static(text) => Some((doc, text)),
            DocText::Opaque(_) | DocText::Invalid(_) => None,
        })
}
