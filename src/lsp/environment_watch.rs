//! A metadata-only fallback for external writes to the selected Julia
//! environment. The index loader samples these paths while idle, never on an
//! editor request or with a salsa snapshot held.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use lsp_types::{FileChangeType, FileEvent};

use crate::environment::{
    EnvContext, ManifestSelectionFields, discover_project, manifest_for_project_with,
    read_manifest_selection_fields,
};

#[derive(Clone, PartialEq, Eq)]
struct Stamp {
    len: u64,
    modified: Option<SystemTime>,
    created: Option<SystemTime>,
}

/// Snapshot the selection as well as the stamps: creating or removing a
/// higher-priority Project/Manifest can change the selected paths.
#[derive(Default)]
pub(super) struct EnvironmentFiles {
    watched: BTreeMap<PathBuf, Stamp>,
    project_cache: BTreeMap<PathBuf, (Stamp, ManifestSelectionFields)>,
}

impl EnvironmentFiles {
    pub(super) fn scan(roots: &[PathBuf], version: Option<&str>, prior: Option<&Self>) -> Self {
        let mut paths = BTreeSet::new();
        let mut project_cache = BTreeMap::new();
        for root in roots {
            let ctx = EnvContext::from_process(root.clone());
            if let Some(project) = discover_project(&ctx) {
                if let Some(manifest) =
                    manifest_for_project_with(&project, version, ctx.home.as_deref(), |path| {
                        if let Some((_, metadata)) = project_cache.get(path) {
                            let metadata: &ManifestSelectionFields = metadata;
                            return metadata.clone();
                        }
                        let Some(current) = stamp(path) else {
                            return ManifestSelectionFields::default();
                        };
                        let metadata = prior
                            .and_then(|prior| prior.project_cache.get(path))
                            .filter(|(old, _)| *old == current)
                            .map_or_else(
                                || read_manifest_selection_fields(path),
                                |(_, metadata)| metadata.clone(),
                            );
                        project_cache.insert(path.to_path_buf(), (current, metadata.clone()));
                        metadata
                    })
                {
                    paths.insert(manifest);
                }
                paths.insert(project);
            }
        }
        Self {
            watched: paths
                .into_iter()
                .filter_map(|path| Some((path.clone(), stamp(&path)?)))
                .collect(),
            project_cache,
        }
    }

    pub(super) fn changes_to(&self, next: &Self) -> Vec<FileEvent> {
        self.watched
            .keys()
            .chain(
                next.watched
                    .keys()
                    .filter(|path| !self.watched.contains_key(*path)),
            )
            .filter_map(|path| {
                let kind = match (self.watched.get(path), next.watched.get(path)) {
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
