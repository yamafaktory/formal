//! Property specs the repository owns, rather than ones an LLM re-invents.
//!
//! Two independent extraction runs over one function produced six and seven
//! properties, agreed on the wording of none of them, and disagreed on the
//! direction of one — so nothing derived fresh each run can key a cache, and no
//! amount of string normalisation closes that. Writing the specs down once
//! removes the question: the same bytes every run, and a diff when someone
//! changes them.
//!
//! It also makes the claim reviewable. A verification tool whose properties are
//! re-invented per run cannot tell you what it checked last week.
//!
//! The risk a checked-in spec introduces is that the code moves and the property
//! does not, so a stale proof answers a question nobody is asking any more. Each
//! spec carries the function source it was written against, and a spec whose
//! source has since changed is reported rather than proved.

use std::{
    fs,
    path::{
        Path,
        PathBuf,
    },
};

use serde_json::Value;
use thiserror::Error;

use crate::{
    proof_cache::normalise_code,
    property::PropertySpec,
};

/// The spec format this formal understands.
pub const SPEC_VERSION: u64 = 1;

/// A JSON object, which is the shape every spec entry has.
type Object = serde_json::Map<String, Value>;

/// Fields without which a property describes nothing.
const REQUIRED: [&str; 4] = ["id", "function", "kind", "formal"];

/// The spec file cannot be trusted to describe anything.
///
/// Every message here reaches a caller as the `detail` of a 400, so the wording
/// is part of the HTTP surface rather than a developer convenience.
#[derive(Debug, Error)]
pub enum SpecError {
    /// The path names nothing on disk.
    #[error("no spec file at {0}")]
    NoSuchFile(PathBuf),

    /// The bytes are not JSON.
    #[error("{path} is not valid JSON: {reason}")]
    NotJson {
        /// The file that failed to parse.
        path: PathBuf,
        /// What the parser objected to.
        reason: String,
    },

    /// The JSON is not the shape a spec file has.
    #[error("{0} must be an object with a 'properties' list")]
    NotASpecFile(PathBuf),

    /// The file announces a format this formal does not read.
    #[error("{path} is version {found}, this formal understands {SPEC_VERSION}")]
    Version {
        /// The file that announced it.
        path: PathBuf,
        /// The version it announced.
        found: String,
    },

    /// There is nothing in the file to prove.
    #[error("{0} lists no properties")]
    NoProperties(PathBuf),

    /// One entry is not an object.
    #[error("{path}: property {index} is not an object")]
    NotAnObject {
        /// The file it is in.
        path: PathBuf,
        /// Its position in the list.
        index: usize,
    },

    /// One entry is missing fields it cannot do without.
    #[error("{path}: property {index} is missing {}", missing.join(", "))]
    MissingFields {
        /// The file it is in.
        path: PathBuf,
        /// Its position in the list.
        index: usize,
        /// The fields it does not have, in the order they are required.
        missing: Vec<String>,
    },

    /// Two properties share an id, and would share a verdict and a cache entry.
    #[error("{path}: duplicate property ids: {}", ids.join(", "))]
    DuplicateIds {
        /// The file they are in.
        path: PathBuf,
        /// The ids that appear more than once, sorted.
        ids: Vec<String>,
    },

    /// A path the server would resolve against the wrong directory.
    #[error(
        "{what} path must be absolute, got {path} — it is resolved by the server, whose working \
         directory is not the caller's, so a relative path may find a different file or none at all"
    )]
    NotAbsolute {
        /// What the path was for, as it should read in the message.
        what: String,
        /// The path as the caller gave it.
        path: PathBuf,
    },

    /// A proof file named by the caller could not be read.
    #[error("cannot read the proof for {property_id} at {path}: {reason}")]
    UnreadableProof {
        /// The property the proof was for.
        property_id: String,
        /// Where it was meant to be.
        path: PathBuf,
        /// What the filesystem said.
        reason: String,
    },
}

/// One property as it was read, with the source reference it was written against.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoadedSpec {
    /// The property itself.
    pub spec: PropertySpec,
    /// The file `function_code` was taken from, relative to the spec file.
    pub source_file: String,
    /// Whether that source has since changed.
    pub stale: bool,
}

/// A spec file, split into the properties still describing their source and the
/// properties that no longer do.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SpecFile {
    /// Where it was read from.
    pub path: PathBuf,
    /// Properties whose source still says what they were written against.
    pub live: Vec<LoadedSpec>,
    /// Properties whose source has moved on.
    pub stale: Vec<LoadedSpec>,
}

impl SpecFile {
    /// The properties worth opening a session with.
    #[must_use]
    pub fn specs(&self) -> Vec<&PropertySpec> {
        self.live.iter().map(|entry| &entry.spec).collect()
    }

    /// The ids to report rather than prove.
    #[must_use]
    pub fn stale_ids(&self) -> Vec<&str> {
        self.stale
            .iter()
            .map(|entry| entry.spec.id.as_str())
            .collect()
    }
}

/// `Path.expanduser()`.
fn expanduser(raw: &str) -> PathBuf {
    if let Some(home) = std::env::var_os("HOME").filter(|_| raw == "~" || raw.starts_with("~/")) {
        let home = PathBuf::from(home);
        return if raw == "~" {
            home
        } else {
            home.join(&raw[2..])
        };
    }
    PathBuf::from(raw)
}

fn require_absolute(path: &Path, what: &str) -> Result<(), SpecError> {
    if path.is_absolute() {
        return Ok(());
    }
    Err(SpecError::NotAbsolute {
        what: what.to_string(),
        path: path.to_path_buf(),
    })
}

/// A field as the required-field check sees it: present, a string, non-blank.
fn field(entry: &Object, name: &str) -> String {
    entry
        .get(name)
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_string()
}

fn read(path: &Path) -> Result<Vec<Value>, SpecError> {
    let text = fs::read_to_string(path).map_err(|_| SpecError::NoSuchFile(path.to_path_buf()))?;
    let payload: Value = serde_json::from_str(&text).map_err(|e| SpecError::NotJson {
        path: path.to_path_buf(),
        reason: e.to_string(),
    })?;

    let Some(object) = payload.as_object() else {
        return Err(SpecError::NotASpecFile(path.to_path_buf()));
    };
    let Some(entries) = object.get("properties") else {
        return Err(SpecError::NotASpecFile(path.to_path_buf()));
    };

    let version = object.get("version");
    if version.is_some_and(|v| v.as_u64() != Some(SPEC_VERSION)) {
        return Err(SpecError::Version {
            path: path.to_path_buf(),
            found: version
                .map(|v| {
                    v.as_str()
                        .map_or_else(|| v.to_string(), ToString::to_string)
                })
                .unwrap_or_default(),
        });
    }

    match entries.as_array() {
        Some(entries) if !entries.is_empty() => Ok(entries.clone()),
        _ => Err(SpecError::NoProperties(path.to_path_buf())),
    }
}

/// The entries as objects, which is also what says they are usable.
fn validate<'a>(entries: &'a [Value], path: &Path) -> Result<Vec<&'a Object>, SpecError> {
    let mut objects = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        let Some(entry) = entry.as_object() else {
            return Err(SpecError::NotAnObject {
                path: path.to_path_buf(),
                index,
            });
        };
        let missing: Vec<String> = REQUIRED
            .iter()
            .filter(|name| field(entry, name).trim().is_empty())
            .map(|name| (*name).to_string())
            .collect();
        if !missing.is_empty() {
            return Err(SpecError::MissingFields {
                path: path.to_path_buf(),
                index,
                missing,
            });
        }
        objects.push(entry);
    }

    let ids: Vec<String> = objects.iter().map(|entry| field(entry, "id")).collect();
    let mut duplicates: Vec<String> = ids
        .iter()
        .filter(|id| ids.iter().filter(|other| other == id).count() > 1)
        .cloned()
        .collect();
    duplicates.sort();
    duplicates.dedup();
    if !duplicates.is_empty() {
        return Err(SpecError::DuplicateIds {
            path: path.to_path_buf(),
            ids: duplicates,
        });
    }
    Ok(objects)
}

/// Whether the source this property was written against still says the same thing.
///
/// Compared as normalised text rather than parsed, so it holds for every language
/// formal accepts. A spec with no recorded source cannot go stale — there is
/// nothing to compare it against.
fn is_stale(entry: &Object, root: &Path) -> bool {
    let source_file = field(entry, "source_file");
    let function_code = field(entry, "function_code");
    if source_file.is_empty() || function_code.is_empty() {
        return false;
    }
    let Ok(current) = fs::read_to_string(root.join(source_file)) else {
        return true;
    };
    !normalise_code(&current).contains(&normalise_code(&function_code))
}

fn strings(entry: &Object, name: &str) -> Vec<String> {
    entry
        .get(name)
        .and_then(Value::as_array)
        .map(|items| {
            items
                .iter()
                .filter_map(|item| item.as_str().map(ToString::to_string))
                .collect()
        })
        .unwrap_or_default()
}

/// Read Lean proofs from disk so a caller need not marshal them into JSON.
///
/// Every caller so far has written a script for this: loading each `.lean` file,
/// escaping it into a JSON object and posting the batch. The server can already
/// read a spec file from an absolute path; reading the proofs beside it is the
/// same trust model and removes the script.
///
/// Pairs rather than a map, so the order the caller sent decides which unreadable
/// proof is the one reported.
///
/// # Errors
///
/// [`SpecError::NotAbsolute`] for a path the server would resolve against its own
/// directory, and [`SpecError::UnreadableProof`] for one it cannot read.
pub fn read_proofs(paths: &[(String, String)]) -> Result<Vec<(String, String)>, SpecError> {
    paths
        .iter()
        .map(|(property_id, raw)| {
            let path = expanduser(raw);
            require_absolute(&path, &format!("proof file for {property_id}"))?;
            let lean = fs::read_to_string(&path).map_err(|e| SpecError::UnreadableProof {
                property_id: property_id.clone(),
                path: path.clone(),
                reason: e.to_string(),
            })?;
            Ok((property_id.clone(), lean))
        })
        .collect()
}

/// Read a spec file, separating properties still describing their source from
/// those that are not.
///
/// `root` is what `source_file` is resolved against, and defaults to the
/// directory the spec file is in.
///
/// # Errors
///
/// Any [`SpecError`] but [`SpecError::UnreadableProof`] — a spec file that is
/// absent, relative, malformed, versioned for another formal, empty, or holding
/// a property that is incomplete or shares an id with another.
pub fn load(path: &str, root: Option<&Path>) -> Result<SpecFile, SpecError> {
    let path = expanduser(path);
    require_absolute(&path, "spec file")?;
    let root = root.map_or_else(
        || path.parent().unwrap_or(Path::new(".")).to_path_buf(),
        Path::to_path_buf,
    );

    let entries = read(&path)?;
    let objects = validate(&entries, &path)?;

    let mut file = SpecFile {
        path,
        ..SpecFile::default()
    };
    for entry in objects {
        let loaded = LoadedSpec {
            spec: PropertySpec {
                id: field(entry, "id"),
                description: field(entry, "description"),
                kind: field(entry, "kind"),
                function: field(entry, "function"),
                function_code: field(entry, "function_code"),
                formal: field(entry, "formal"),
                preconditions: strings(entry, "preconditions"),
                assumptions: strings(entry, "assumptions"),
            },
            source_file: field(entry, "source_file"),
            stale: is_stale(entry, &root),
        };
        if loaded.stale {
            file.stale.push(loaded);
        } else {
            file.live.push(loaded);
        }
    }
    Ok(file)
}
