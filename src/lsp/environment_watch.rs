//! A metadata-only fallback for external writes to the selected Julia
//! environment. The index loader samples these paths while idle, never on an
//! editor request or with a salsa snapshot held.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use lsp_types::{FileChangeType, FileEvent};

use crate::environment::{EnvContext, discover_project, find_manifest};

#[derive(PartialEq, Eq)]
struct Stamp {
    len: u64,
    modified: Option<SystemTime>,
    created: Option<SystemTime>,
}

/// Snapshot the selection as well as the stamps: creating or removing a
/// higher-priority Project/Manifest can change the selected paths.
#[derive(Default)]
pub(super) struct EnvironmentFiles(BTreeMap<PathBuf, Stamp>);

impl EnvironmentFiles {
    pub(super) fn scan(roots: &[PathBuf]) -> Self {
        let mut paths = BTreeSet::new();
        for root in roots {
            if let Some(project) = discover_project(&EnvContext::from_process(root.clone())) {
                if let Some(manifest) = project.parent().and_then(find_manifest) {
                    paths.insert(manifest);
                }
                paths.insert(project);
            }
        }
        Self(
            paths
                .into_iter()
                .filter_map(|path| Some((path.clone(), stamp(&path)?)))
                .collect(),
        )
    }

    pub(super) fn changes_to(&self, next: &Self) -> Vec<FileEvent> {
        self.0
            .keys()
            .chain(next.0.keys().filter(|path| !self.0.contains_key(*path)))
            .filter_map(|path| {
                let kind = match (self.0.get(path), next.0.get(path)) {
                    (None, Some(_)) => FileChangeType::CREATED,
                    (Some(_), None) => FileChangeType::DELETED,
                    (Some(old), Some(new)) if old != new => FileChangeType::CHANGED,
                    _ => return None,
                };
                Some(FileEvent::new(super::uri::from_path(path)?, kind))
            })
            .collect()
    }
}

fn stamp(path: &Path) -> Option<Stamp> {
    let metadata = std::fs::metadata(path).ok()?;
    Some(Stamp {
        len: metadata.len(),
        modified: metadata.modified().ok(),
        created: metadata.created().ok(),
    })
}
