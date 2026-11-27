//! `file:` URI ↔ filesystem path conversion.

use std::path::{Path, PathBuf};
use std::str::FromStr;

use lsp_types::Uri;

/// Convert a `file:` URI to a filesystem path, or `None` if it isn't a file
/// URI or has no scheme (e.g. an editor's `untitled:` buffer).
pub(crate) fn to_path(uri: &Uri) -> Option<PathBuf> {
    let scheme = uri.scheme()?;
    if !scheme.as_str().eq_ignore_ascii_case("file") {
        return None;
    }
    let decoded = uri
        .path()
        .as_estr()
        .decode()
        .into_string_lossy()
        .into_owned();
    #[cfg(windows)]
    if let Some(authority) = uri
        .authority()
        .filter(|authority| !authority.as_str().is_empty())
    {
        // Older Neovim puts a backslash UNC filename, percent-encoded, in
        // the authority slot. Accept that form without treating arbitrary
        // percent-encoded authorities as network hosts.
        if authority
            .as_str()
            .get(..6)
            .is_some_and(|prefix| prefix.eq_ignore_ascii_case("%5c%5c"))
        {
            let escaped = Uri::from_str(&format!("file:///{}", authority.as_str())).ok()?;
            let part = escaped.path().as_estr().decode().into_string_lossy();
            let joined = format!("{}{decoded}", part.strip_prefix('/')?).replace('/', "\\");
            let mut components = joined.strip_prefix(r"\\")?.splitn(3, '\\');
            let host = components.next()?;
            let share = components.next()?;
            if !valid_unc_host(host) || !valid_unc_share(share) {
                return None;
            }
            return Some(PathBuf::from(joined));
        }
        // A Windows file URI's authority is the UNC server, not disposable
        // metadata. Do not reinterpret URI credentials/ports as SMB paths.
        if authority.userinfo().is_some() || authority.port().is_some() {
            return None;
        }
        let host = authority.host().as_str();
        if !valid_unc_host(host) {
            return None;
        }
        if !host.eq_ignore_ascii_case("localhost") || !has_windows_drive(&decoded) {
            let share = decoded.strip_prefix('/')?.split('/').next()?;
            if !valid_unc_share(share) {
                return None;
            }
            return Some(PathBuf::from(format!(
                r"\\{host}{}",
                decoded.replace('/', "\\")
            )));
        }
    }
    Some(from_uri_path(&decoded))
}

#[cfg(windows)]
fn valid_unc_host(host: &str) -> bool {
    !host.is_empty()
        && host
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"-_.".contains(&byte))
        && host != "."
        && host != ".."
}

#[cfg(windows)]
fn valid_unc_share(share: &str) -> bool {
    !share.is_empty() && share != "." && share != ".." && !share.contains(['\\', ':', '\0'])
}

#[cfg(windows)]
fn from_uri_path(p: &str) -> PathBuf {
    // "/C:/Users/x" → "C:\Users\x"; without a drive letter the leading slash
    // stays, so "/work/x" maps to the rooted "\work\x" rather than a relative
    // path.
    let trimmed = if has_windows_drive(p) { &p[1..] } else { p };
    PathBuf::from(trimmed.replace('/', "\\"))
}

#[cfg(windows)]
fn has_windows_drive(p: &str) -> bool {
    let bytes = p.as_bytes();
    bytes.len() >= 3 && bytes[0] == b'/' && bytes[1].is_ascii_alphabetic() && bytes[2] == b':'
}

#[cfg(not(windows))]
fn from_uri_path(p: &str) -> PathBuf {
    PathBuf::from(p)
}

/// The directory the synthetic paths of non-`file:` URIs live under. Rooted, so
/// `incremental::normalize_path` resolves it against the filesystem root rather
/// than the server's working directory, where it could alias a real file the
/// server would then read from disk.
const NON_FILE_ROOT: &str = "fatou-non-file-uri";

/// The filesystem path the db tracks `uri` under. A non-`file:` URI (an
/// editor's `untitled:` buffer, a notebook cell) has no path of its own, so it
/// gets a synthetic one derived from the whole URI: injective, so two untitled
/// buffers no longer share a single input — and with it a single reparse base
/// each one's edits would knock the other off.
pub(crate) fn to_path_or_synthetic(uri: &Uri) -> PathBuf {
    to_path(uri).unwrap_or_else(|| {
        use std::fmt::Write;

        // Percent-escape everything outside the unreserved set, so distinct URIs
        // stay distinct and no separator (or `%`) survives to split the name
        // into components of its own.
        let mut name = String::new();
        for &byte in uri.as_str().as_bytes() {
            match byte {
                b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' => name.push(byte as char),
                _ => {
                    let _ = write!(name, "%{byte:02X}");
                }
            }
        }
        // Keeps extension-based handling working, and (with `.` escaped above)
        // leaves the name unable to spell `.` or `..`.
        name.push_str(".jl");
        synthetic_dir().join(name)
    })
}

/// The one directory [`to_path_or_synthetic`] mints into: [`NON_FILE_ROOT`]
/// directly under the filesystem root.
fn synthetic_dir() -> PathBuf {
    PathBuf::from(std::path::MAIN_SEPARATOR_STR).join(NON_FILE_ROOT)
}

/// Whether `path` is one of the synthetic stand-ins [`to_path_or_synthetic`]
/// mints, rather than a real filesystem path. Such a path only identifies a
/// buffer: nothing exists there to read, and no directory of the workspace is
/// implied, so relative paths must not be resolved against it.
///
/// The whole shape is checked, not just the directory name: a real
/// `/work/fatou-non-file-uri/x.jl` under someone's workspace is a file like any
/// other, and only the rooted single-component form is ever minted here.
pub(crate) fn is_synthetic(path: &Path) -> bool {
    path.parent() == Some(synthetic_dir().as_path())
}

/// The directory a relative path *inside* the document at `path` resolves
/// against: its parent. `None` when there is no such directory — a
/// [synthetic](is_synthetic) stand-in for a non-`file` URI names no real one,
/// and a parentless path names none either.
///
/// One definition, because two features ask it: a Julia document's `include`
/// paths and a manifest's `path` entries.
pub(crate) fn anchor_dir(path: &Path) -> Option<&Path> {
    if is_synthetic(path) {
        return None;
    }
    path.parent().filter(|dir| !dir.as_os_str().is_empty())
}

/// Build a `file:` URI for the absolute filesystem `path`, percent-encoding
/// characters outside the unreserved set. The inverse of [`to_path`]; used to
/// point a go-to-definition [`Location`](lsp_types::Location) at a depot source
/// file. `None` if the path is not valid UTF-8.
pub(crate) fn from_path(path: &Path) -> Option<Uri> {
    let text = path.to_str()?;
    let mut encoded = String::from("file://");
    // Preserve UNC authority; a drive path uses an empty authority and
    // leading slash. Canonicalized Windows paths can use the verbatim prefix.
    #[cfg(windows)]
    let text = text.replace('\\', "/");
    #[cfg(windows)]
    let text = if let Some(unc) = text
        .strip_prefix("//?/UNC/")
        .or_else(|| text.strip_prefix("//?/unc/"))
    {
        unc
    } else if let Some(verbatim) = text.strip_prefix("//?/") {
        let bytes = verbatim.as_bytes();
        if bytes.len() < 3 || !bytes[0].is_ascii_alphabetic() || &bytes[1..3] != b":/" {
            return None;
        }
        encoded.push('/');
        verbatim
    } else if text.starts_with("//./") {
        return None;
    } else if let Some(unc) = text.strip_prefix("//") {
        unc
    } else {
        if !text.starts_with('/') {
            encoded.push('/');
        }
        text.as_str()
    };
    for &byte in text.as_bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' | b'/' | b':' => {
                encoded.push(byte as char);
            }
            _ => encoded.push_str(&format!("%{byte:02X}")),
        }
    }
    Uri::from_str(&encoded).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    #[test]
    #[cfg(not(windows))]
    fn file_uri_decodes_to_path() {
        let uri = Uri::from_str("file:///work/some%20dir/a.jl").unwrap();
        assert_eq!(to_path(&uri), Some(PathBuf::from("/work/some dir/a.jl")));
    }

    #[test]
    #[cfg(windows)]
    fn drive_letter_uri_decodes_to_path() {
        let uri = Uri::from_str("file:///C:/work/a%20b.jl").unwrap();
        assert_eq!(to_path(&uri), Some(PathBuf::from("C:\\work\\a b.jl")));
        // Percent-encoded drive colons (as sent by VS Code) decode the same.
        let uri = Uri::from_str("file:///c%3A/work/a.jl").unwrap();
        assert_eq!(to_path(&uri), Some(PathBuf::from("c:\\work\\a.jl")));
    }

    #[test]
    #[cfg(windows)]
    fn unc_and_mapped_drive_uri_round_trip() {
        let uri = Uri::from_str("file://nixos/share/%E6%97%A5%20%23/probe.jl").unwrap();
        let path = PathBuf::from(r"\\nixos\share\日 #\probe.jl");
        assert_eq!(to_path(&uri).as_ref(), Some(&path));
        assert_eq!(from_path(&path).as_ref(), Some(&uri));
        assert_eq!(
            from_path(Path::new(r"\\?\UNC\nixos\share\日 #\probe.jl")).as_ref(),
            Some(&uri)
        );
        let old_uri = Uri::from_str("file:////nixos/share/%E6%97%A5%20%23/probe.jl").unwrap();
        assert_eq!(to_path(&old_uri).as_ref(), Some(&path));
        let neovim =
            Uri::from_str("file://%5c%5cnixos%5cshare%5c%E6%97%A5%20%23%5cprobe.jl").unwrap();
        assert_eq!(to_path(&neovim).as_ref(), Some(&path));
        let neovim_mixed =
            Uri::from_str("file://%5C%5Cnixos%5Cshare/%E6%97%A5%20%23/probe.jl").unwrap();
        assert_eq!(to_path(&neovim_mixed).as_ref(), Some(&path));
        assert!(to_path(&Uri::from_str("file://%5c%5c.%5cpipe%5cprobe.jl").unwrap()).is_none());
        for text in [
            "file:///Z:/dir/probe.jl",
            "file:///Z://dir/probe.jl",
            "file:///z%3A/dir/probe.jl",
        ] {
            let uri = Uri::from_str(text).unwrap();
            let path = to_path(&uri).unwrap();
            assert!(path.is_absolute(), "{path:?}");
            assert_eq!(path.extension().unwrap(), "jl");
            assert_eq!(to_path(&from_path(&path).unwrap()), Some(path));
        }
        assert!(to_path(&Uri::from_str("file://nixos:123/share/file.jl").unwrap()).is_none());
        assert!(to_path(&Uri::from_str("file://nixos//file.jl").unwrap()).is_none());
    }

    #[test]
    #[cfg(windows)]
    fn driveless_uri_stays_rooted() {
        let uri = Uri::from_str("file:///work/a.jl").unwrap();
        assert_eq!(to_path(&uri), Some(PathBuf::from("\\work\\a.jl")));
    }

    #[test]
    fn non_file_uri_has_no_path() {
        let uri = Uri::from_str("untitled:Untitled-1").unwrap();
        assert_eq!(to_path(&uri), None);
    }

    #[test]
    fn non_file_uris_map_to_distinct_rooted_paths() {
        use crate::incremental::normalize_path;

        let path = |text: &str| to_path_or_synthetic(&Uri::from_str(text).unwrap());
        let first = path("untitled:Untitled-1");

        assert_ne!(first, path("untitled:Untitled-2"));
        assert_ne!(first, path("vscode-notebook-cell:Untitled-1"));
        assert_eq!(first, path("untitled:Untitled-1"), "stable per URI");

        // One component under the reserved root: the URI's `:` and `/` are
        // escaped rather than carved into directories, and normalization can
        // neither climb out of the root nor fold the path into the working
        // directory.
        assert!(first.has_root(), "{first:?} should be rooted");
        assert_eq!(first.components().count(), 3, "root, dir, file: {first:?}");
        assert_eq!(first.extension().and_then(|e| e.to_str()), Some("jl"));
        let normalized = normalize_path(&first);
        assert!(
            normalized.ends_with(
                first
                    .strip_prefix(first.components().next().unwrap())
                    .unwrap()
            ),
            "normalization should keep the root's contents: {normalized:?}"
        );
        assert!(
            !normalized.starts_with(std::env::current_dir().expect("a working directory")),
            "a synthetic path must not land in the workspace: {normalized:?}"
        );

        // A `file:` URI keeps its real path.
        #[cfg(not(windows))]
        assert_eq!(path("file:///work/a.jl"), PathBuf::from("/work/a.jl"));
    }

    /// `is_synthetic` recognizes what `to_path_or_synthetic` mints and nothing
    /// else — a real workspace file that merely happens to sit in a directory
    /// of that name is a file like any other, and must keep anchoring its
    /// relative includes.
    #[test]
    fn only_the_minted_shape_counts_as_synthetic() {
        assert!(is_synthetic(&to_path_or_synthetic(
            &Uri::from_str("untitled:Untitled-1").unwrap()
        )));
        assert!(!is_synthetic(Path::new("relative")));
        assert!(!is_synthetic(
            &PathBuf::from(NON_FILE_ROOT).join("notes.jl")
        ));
        #[cfg(not(windows))]
        {
            assert!(!is_synthetic(Path::new("/work/a.jl")));
            assert!(!is_synthetic(Path::new(
                "/work/fatou-non-file-uri-notes/a.jl"
            )));
            // A real workspace directory that merely *ends* in the reserved
            // name is not the rooted single-component form, at any depth.
            assert!(!is_synthetic(Path::new("/work/fatou-non-file-uri/a.jl")));
            assert!(!is_synthetic(Path::new(
                "/work/proj/fatou-non-file-uri/a.jl"
            )));
            // Nor is a nested file under the reserved root itself.
            assert!(!is_synthetic(Path::new("/fatou-non-file-uri/sub/a.jl")));
        }
    }

    #[test]
    #[cfg(not(windows))]
    fn path_round_trips_through_uri() {
        let path = PathBuf::from("/home/x/.julia/packages/A b/src/A b.jl");
        let uri = from_path(&path).expect("file uri");
        // A space encodes to %20, and the URI decodes back to the exact path.
        assert!(uri.as_str().contains("%20"), "space should be encoded");
        assert_eq!(to_path(&uri), Some(path));
    }
}
