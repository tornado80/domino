// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 35 (ADR 0006): what a **proof job** may assume about the export tree and what it may
//! touch.
//!
//! A proof job (`domino easycrypt prove`, `check-alignment`) never rewrites a file that belongs
//! to translation or to another equivalence. It looks at translation's files **by name only**:
//! a file that exists is taken to be what translation would have written, and its contents are
//! never read. A missing one is created by [`create_if_absent`], atomically and only if it is
//! still absent, so two jobs racing to create it cannot tear it.
//!
//! - [`create_if_absent`]: the create-if-absent helper.
//! - [`ensure_translation_files`]: every file of the export except the oracle lemma files
//!   `Eq_<L>_<R>_<O>.ec` (story 68; the glue `Eq_<L>_<R>.ec` is a translation file).
//! - [`SessionRecord`]: `session/Eq_<L>_<R>/<O>.record.json`, one for each oracle (story 68):
//!   its status, and (story 37) the script that lets a job resume it; (version 3) the closed
//!   nodes of an interrupted oracle. [`split_equivalence_record`] splits a record of the whole
//!   equivalence, as jobs wrote it before story 68.
//! - [`SavedTree`]: `session/Eq_<L>_<R>/<oracle>.tree.json`, the joint tree an interrupted oracle is
//!   resumed on (ADR 0008).
//! - [`remove_records_and_trees`]: what `domino easycrypt --force` does to both.
//! - [`ProofLock`], [`progress_dir`], [`check_no_live_jobs`] (story 36): one job per oracle
//!   (story 68).

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use serde_derive::{Deserialize, Serialize};

use crate::debug::lockstep::LockstepOutcome;
use crate::debug::lockstep_run::LockstepSummary;
use crate::writers::easycrypt::export::ExportedTheorem;

/// Creates `path` holding `text`, unless it already exists. Returns whether this call created
/// it.
///
/// The text goes to a temporary file in the same directory first, which is then hard-linked to
/// `path`: a link fails when the target exists, so this never replaces a file, and a concurrent
/// reader never sees half a file. If the link fails because another job created the file first,
/// that is success (`Ok(false)`). Never a `rename`, which replaces.
pub fn create_if_absent(path: &Path, text: &str) -> std::io::Result<bool> {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let dir = path
        .parent()
        .filter(|d| !d.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    std::fs::create_dir_all(dir)?;
    let name = path.file_name().expect("a file path").to_string_lossy();
    let tmp = dir.join(format!(
        ".{name}.{}.{}.tmp",
        std::process::id(),
        COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    let written = (|| {
        let mut file = std::fs::File::create(&tmp)?;
        file.write_all(text.as_bytes())?;
        file.sync_all()
    })();
    let linked = written.and_then(|()| std::fs::hard_link(&tmp, path));
    let _ = std::fs::remove_file(&tmp);
    match linked {
        Ok(()) => Ok(true),
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => Ok(false),
        Err(e) => Err(e),
    }
}

/// Whether `rel` is a lemma file of `exported` that a job owns: an oracle lemma file (story 68),
/// which the proof job of the oracle owns, or a side-invariant lemma file `SideInv_<C>_<O>.ec`
/// (story 69), which the side-invariant job of the composition owns, or a package lemma file
/// `PkgInv_<V>_<O>.ec`, `Frame_<V>_<O>.ec` or `PkgInv_<V>_init.ec` (story 76), which the
/// package-invariant job of the package owns. Every other file, the equivalence's glue
/// `Eq_<L>_<R>.ec`, its `Eq_<L>_<R>_Invariants.ec`, `SideInv_<C>.ec` and `PkgInv_<V>.ec`
/// included, is a translation file, created when missing.
pub fn is_oracle_file(exported: &ExportedTheorem, rel: &Path) -> bool {
    exported
        .equivalences
        .iter()
        .flat_map(|eq| eq.oracle_files.iter())
        .chain(
            exported
                .side_invariants
                .iter()
                .flat_map(|s| s.oracle_files.iter()),
        )
        .chain(
            exported
                .package_invariants
                .iter()
                .flat_map(|p| p.oracle_files.iter().chain(&p.frame_files)),
        )
        .any(|(_, file)| Path::new(file) == rel)
        || exported
            .package_invariants
            .iter()
            .any(|p| Path::new(&p.start_file) == rel)
}

/// Creates, in `theorem_out`, every file of `exported` that translation owns (all but the
/// oracle lemma files) and that is missing. Files that exist are not read. Says nothing: the
/// caller reports the paths it gets back (story 44).
pub fn ensure_translation_files(
    exported: &ExportedTheorem,
    theorem_out: &Path,
) -> std::io::Result<Vec<PathBuf>> {
    let mut created = Vec::new();
    for (rel, text) in &exported.files {
        if is_oracle_file(exported, rel) {
            continue;
        }
        if create_if_absent(&theorem_out.join(rel), text)? {
            created.push(rel.clone());
        }
    }
    Ok(created)
}

/// `<theorem_out>/session/Eq_<L>_<R>` (story 67): the protected files of one equivalence, its
/// session record and its saved joint trees. Not a run artifact: the overwrite check stops on
/// it, and only `--force` removes it.
pub fn session_dir(theorem_out: &Path, proof_file: &str) -> PathBuf {
    theorem_out
        .join("session")
        .join(proof_file.trim_end_matches(".ec"))
}

/// Where the session record of one oracle is written (story 68): `session/Eq_L_R/PKENC.record.json`.
pub fn oracle_record_path(theorem_out: &Path, proof_file: &str, oracle: &str) -> PathBuf {
    session_dir(theorem_out, proof_file).join(format!("{oracle}.record.json"))
}

/// The record of the whole equivalence, as jobs wrote it from story 67 to story 68:
/// `session/Eq_L_R/record.json`. Read by [`split_equivalence_record`], never written.
pub fn equivalence_record_path(theorem_out: &Path, proof_file: &str) -> PathBuf {
    session_dir(theorem_out, proof_file).join("record.json")
}

/// Where the saved joint tree of one oracle is written: `session/Eq_L_R/PKENC.tree.json`.
pub fn saved_tree_path(theorem_out: &Path, proof_file: &str, oracle: &str) -> PathBuf {
    session_dir(theorem_out, proof_file).join(format!("{oracle}.tree.json"))
}

/// The record's path before story 67: `Eq_L_R.session.json` beside the proof file. Read when
/// [`equivalence_record_path`] is missing, never written.
pub fn old_session_record_path(theorem_out: &Path, proof_file: &str) -> PathBuf {
    theorem_out.join(format!(
        "{}.session.json",
        proof_file.trim_end_matches(".ec")
    ))
}

/// The saved tree's path before story 67: `Eq_L_R.PKENC.tree.json`. Read when the new path is
/// missing, never written.
pub fn old_saved_tree_path(theorem_out: &Path, proof_file: &str, oracle: &str) -> PathBuf {
    theorem_out.join(format!(
        "{}.{oracle}.tree.json",
        proof_file.trim_end_matches(".ec")
    ))
}

/// The path to read: `new` if it exists; else `old` if it exists (said on one line); else
/// `new`. The caller always writes `new`, and never deletes `old`.
pub fn path_to_read(new: PathBuf, old: PathBuf) -> PathBuf {
    if !new.exists() && old.exists() {
        crate::debug::progress::eprintln_above_bars(&format!(
            "note: reading {} from its old path; from now on it is written to {}",
            old.display(),
            new.display()
        ));
        return old;
    }
    new
}

/// How far proving one oracle got.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OracleStatus {
    /// Ended without an `interrupted` admit (admits with any other reason count as done).
    Done,
    /// Sealed by a stop.
    Interrupted,
    /// Not reached.
    Pending,
}

/// One `admit` of a done oracle: what the report prints of it, without the goal text.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AdmitRecord {
    /// `N<k>`, `J<k>`, `S<k>` or `router`.
    pub node: String,
    /// The reason's slug (`stuck`, `domino-fails`, …).
    pub reason: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub claim: String,
    /// Domino's own verdict's slug (`verified`, `fails`, …).
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub domino: String,
}

/// What lockstep execution cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct LockstepRecord {
    pub joint_paths: usize,
    pub ms: u64,
}

/// One line of a closed node's script, as [`crate::easycrypt::tactics`] renders it: its depth is
/// relative to the node's first line, so it can be written back at any depth.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScriptLine {
    pub depth: usize,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub bullet: bool,
    pub sentence: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub comment: Option<String>,
}

/// A **closed node** of an interrupted oracle (story "resume an oracle from its saved joint
/// tree"): its proof was accepted and holds no `interrupted` admit. Only outermost ones are
/// recorded; a closed node's descendants are in its script.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClosedNode {
    /// `N<k>`.
    pub id: String,
    pub script: Vec<ScriptLine>,
    /// The admits inside the script, which the resumed oracle reports as its own.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub admits: Vec<AdmitRecord>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OracleRecord {
    pub name: String,
    pub status: OracleStatus,
    /// The oracle's bullet exactly as rendered into `Eq_*.ec`: only for `done` oracles of a
    /// version 2 record or later, and what resuming writes back.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub script: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub admits: Vec<AdmitRecord>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lockstep: Option<LockstepRecord>,
    /// Version 3, `interrupted` oracles only: the outermost closed nodes, which resuming keeps.
    /// (Version 2's `nodes` field is ignored when read.)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub closed: Vec<ClosedNode>,
    /// Version 3, `interrupted` oracles only: the [`SavedTree::id`] of the tree `closed` was
    /// proved on. Resuming walks only that tree.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tree_id: Option<String>,
}

impl OracleRecord {
    /// An entry with a status and nothing else.
    pub fn new(name: &str, status: OracleStatus) -> Self {
        OracleRecord {
            name: name.to_string(),
            status,
            script: None,
            admits: Vec::new(),
            lockstep: None,
            closed: Vec::new(),
            tree_id: None,
        }
    }

    /// Done, with the script that resuming writes back.
    pub fn is_resumable(&self) -> bool {
        self.status == OracleStatus::Done && self.script.is_some()
    }

    /// The node an interrupted oracle was proving when it stopped (`N<k>` or `router`): the
    /// node of its `interrupted` admit.
    pub fn in_flight(&self) -> Option<&str> {
        self.admits
            .iter()
            .find(|a| a.reason == "interrupted")
            .map(|a| a.node.as_str())
    }
}

/// `session/Eq_<L>_<R>/record.json`: what each oracle of one equivalence has got to, and enough of
/// its proof to write it back without proving it again (story 37).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SessionRecord {
    pub version: u32,
    pub theorem: String,
    pub left: String,
    pub right: String,
    /// The Domino version that wrote it (absent in version 1).
    #[serde(default)]
    pub domino: String,
    /// When, RFC 3339 UTC (absent in version 1).
    #[serde(default)]
    pub updated: String,
    /// Every oracle is done.
    pub complete: bool,
    pub oracles: Vec<OracleRecord>,
}

impl SessionRecord {
    pub const VERSION: u32 = 3;

    pub fn new(theorem: &str, left: &str, right: &str, oracles: Vec<OracleRecord>) -> Self {
        SessionRecord {
            version: Self::VERSION,
            theorem: theorem.to_string(),
            left: left.to_string(),
            right: right.to_string(),
            domino: env!("CARGO_PKG_VERSION").to_string(),
            updated: rfc3339_now(),
            complete: oracles.iter().all(|o| o.status == OracleStatus::Done),
            oracles,
        }
    }

    pub fn done(&self) -> usize {
        self.oracles
            .iter()
            .filter(|o| o.status == OracleStatus::Done)
            .count()
    }

    /// The entry for `name`.
    pub fn oracle(&self, name: &str) -> Option<&OracleRecord> {
        self.oracles.iter().find(|o| o.name == name)
    }

    /// The record of `name` alone, with this record's version: what an oracle's own record
    /// (story 68) holds. `None` when there is no entry for it.
    pub fn only(&self, name: &str) -> Option<SessionRecord> {
        let entry = self.oracle(name)?.clone();
        Some(SessionRecord {
            complete: entry.status == OracleStatus::Done,
            oracles: vec![entry],
            ..self.clone()
        })
    }

    /// The oracles' own records joined into the record of their equivalence, whose oracles are
    /// `oracles`: one entry for each, in that order, `pending` where no record has one. The
    /// version is the oldest of `records`. `None` when there are no records.
    pub fn join(records: &[SessionRecord], oracles: &[String]) -> Option<SessionRecord> {
        let first = records.first()?;
        let entries = oracles
            .iter()
            .map(|name| {
                records
                    .iter()
                    .find_map(|r| r.oracle(name))
                    .cloned()
                    .unwrap_or_else(|| OracleRecord::new(name, OracleStatus::Pending))
            })
            .collect::<Vec<_>>();
        Some(SessionRecord {
            version: records
                .iter()
                .map(|r| r.version)
                .min()
                .unwrap_or(first.version),
            complete: entries.iter().all(|o| o.status == OracleStatus::Done),
            oracles: entries,
            ..first.clone()
        })
    }

    /// Oracles that are done but have no script (a version 1 record): they cannot be resumed.
    pub fn done_without_script(&self) -> usize {
        self.oracles
            .iter()
            .filter(|o| o.status == OracleStatus::Done && o.script.is_none())
            .count()
    }

    pub fn to_json(&self) -> String {
        let mut text = serde_json::to_string_pretty(self).expect("a record serializes");
        text.push('\n');
        text
    }

    /// The record at `path`: `Ok(None)` when there is none.
    pub fn read(path: &Path) -> Result<Option<SessionRecord>, SessionRecordError> {
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(source) => {
                return Err(SessionRecordError::Read {
                    path: path.to_path_buf(),
                    message: source.to_string(),
                })
            }
        };
        serde_json::from_str(&text)
            .map(Some)
            .map_err(|source| SessionRecordError::Read {
                path: path.to_path_buf(),
                message: source.to_string(),
            })
    }

    /// The line printed when a proof job skips the equivalence this record describes.
    pub fn skip_line(&self, proof_file: &str) -> String {
        format!(
            "skipping {}: already proved ({} of {} oracles); --force re-proves it",
            stem_of(proof_file),
            self.done(),
            self.oracles.len()
        )
    }

    /// The line printed when a proof job resumes the equivalence this record describes.
    pub fn resume_line(&self, proof_file: &str) -> String {
        format!(
            "resuming {}: {} of {} oracles already proved",
            stem_of(proof_file),
            self.oracles.iter().filter(|o| o.is_resumable()).count(),
            self.oracles.len()
        )
    }

    /// The line printed when a version 1 record's done oracles cannot be resumed.
    pub fn version_1_line(&self, proof_file: &str) -> String {
        format!(
            "{}: the session record has no scripts (written before story 37); its {} proved \
             oracle(s) cannot be resumed and are proved again",
            stem_of(proof_file),
            self.done_without_script()
        )
    }
}

fn stem_of(proof_file: &str) -> &str {
    let stem = proof_file.trim_end_matches(".ec");
    stem.rsplit('/').next().unwrap_or(stem)
}

/// Now, as `YYYY-MM-DDTHH:MM:SSZ`.
fn rfc3339_now() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    rfc3339(secs)
}

/// Unix seconds as `YYYY-MM-DDTHH:MM:SSZ` (days to civil date after Howard Hinnant).
fn rfc3339(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        rem / 3600,
        rem % 3600 / 60,
        rem % 60
    )
}

#[derive(Debug, thiserror::Error)]
pub enum SessionRecordError {
    #[error(
        "cannot read the session record {}: {message} (it is not meant to be edited; `--force` \
         discards it)",
        path.display()
    )]
    Read { path: PathBuf, message: String },
    #[error("cannot write the session record {}: {message}", path.display())]
    Write { path: PathBuf, message: String },
}

/// Splits the record of the whole equivalence `proof_file` (written before story 68, at
/// [`equivalence_record_path`] or the older [`old_session_record_path`]) into one record for
/// each oracle, at [`oracle_record_path`]. An oracle that has its own record already keeps it:
/// each one is created only if absent, so two jobs that split at once write each file once.
/// The old record is not deleted. Returns how many oracle records were created.
pub fn split_equivalence_record(
    theorem_out: &Path,
    proof_file: &str,
) -> Result<usize, SessionRecordError> {
    let new = equivalence_record_path(theorem_out, proof_file);
    let old = old_session_record_path(theorem_out, proof_file);
    if !new.exists() && !old.exists() {
        return Ok(0);
    }
    let Some(whole) = SessionRecord::read(&path_to_read(new, old))? else {
        return Ok(0);
    };
    let mut created = 0;
    for entry in &whole.oracles {
        let path = oracle_record_path(theorem_out, proof_file, &entry.name);
        let record = whole.only(&entry.name).expect("an entry of the record");
        let wrote =
            create_if_absent(&path, &record.to_json()).map_err(|e| SessionRecordError::Write {
                path: path.clone(),
                message: e.to_string(),
            })?;
        created += usize::from(wrote);
    }
    Ok(created)
}

/// Deletes every file under `<theorem_out>/session/`, and every old-path `*.session.json` and
/// `*.tree.json` under `theorem_out` (translation with `--force`: the proofs they describe are
/// overwritten by skeletons). Returns how many were deleted.
pub fn remove_records_and_trees(theorem_out: &Path) -> std::io::Result<usize> {
    let session_root = theorem_out.join("session");
    let mut removed = 0;
    let mut stack = vec![theorem_out.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = match std::fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => return Err(e),
        };
        for entry in entries {
            let entry = entry?;
            let path = entry.path();
            if entry.file_type()?.is_dir() {
                stack.push(path);
            } else if path.starts_with(&session_root)
                || path
                    .file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.ends_with(".session.json") || n.ends_with(".tree.json"))
            {
                std::fs::remove_file(&path)?;
                removed += 1;
            }
        }
    }
    Ok(removed)
}

/// `session/Eq_<L>_<R>/<oracle>.tree.json` (ADR 0008): the joint tree lockstep execution built for one
/// oracle, saved before the oracle's first sentence is sent, so that resuming the oracle walks
/// the very tree its closed nodes were proved against.
#[derive(Debug, Serialize, Deserialize)]
pub struct SavedTree {
    pub version: u32,
    pub oracle: String,
    /// New with every tree written: the session record names the tree its closed nodes were
    /// proved on, so a tree written by a later lockstep execution is never paired with them.
    #[serde(default)]
    pub id: String,
    /// The Domino version that wrote it (not part of the fingerprint).
    pub domino: String,
    /// Hex of the hash of everything the tree was built from (see
    /// [`crate::debug::lockstep_fingerprint`]).
    pub fingerprint: String,
    /// The same, one hash per part (`code`, `constants`, `randomness`, `invariants`), so a stale
    /// tree can say what changed.
    #[serde(default)]
    pub fingerprint_parts: std::collections::BTreeMap<String, String>,
    pub outcome: LockstepOutcome,
    pub summary: LockstepSummary,
    /// The names of the loaded state relations: the walk unfolds `StateRelation_<name>`.
    #[serde(default)]
    pub relations: Vec<String>,
    /// The names of the helper `define-fun`s: the walk unfolds `Helper_<name>`. Empty in a tree
    /// saved before story 59.
    #[serde(default)]
    pub helpers: Vec<String>,
}

impl SavedTree {
    pub const VERSION: u32 = 1;

    /// A fresh [`SavedTree::id`]: the time and the process, unique to every tree written.
    pub fn new_id() -> String {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        format!("{nanos:x}-{:x}", std::process::id())
    }

    /// The tree as its file holds it: compact, one line.
    pub fn to_json(&self) -> String {
        let mut text = serde_json::to_string(self).expect("a tree serializes");
        text.push('\n');
        text
    }

    /// The tree at `path`: `Ok(None)` when there is none, an error when it cannot be read, does
    /// not parse, or has a version this Domino does not know.
    pub fn read(path: &Path) -> Result<Option<SavedTree>, SavedTreeError> {
        let error = |message: String| SavedTreeError {
            path: path.to_path_buf(),
            message,
        };
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(error(e.to_string())),
        };
        #[derive(Deserialize)]
        struct Version {
            version: u32,
        }
        let version = serde_json::from_str::<Version>(&text)
            .map_err(|e| error(e.to_string()))?
            .version;
        if version != Self::VERSION {
            return Err(error(format!(
                "version {version}, but this Domino reads version {}",
                Self::VERSION
            )));
        }
        serde_json::from_str(&text)
            .map(Some)
            .map_err(|e| error(e.to_string()))
    }
}

#[derive(Debug, thiserror::Error)]
#[error("cannot read the saved joint tree {}: {message}", path.display())]
pub struct SavedTreeError {
    pub path: PathBuf,
    pub message: String,
}

// ----------------------------------------------------------------------------------------
// Story 36: one job per equivalence
// ----------------------------------------------------------------------------------------

/// `<theorem_out>/progress/Eq_<L>_<R>`: everything the proof jobs of one equivalence write that
/// is not a proof file or a record: the equivalence's page and report, the oracles' locks
/// (`<O>.lock`), and one folder for each oracle (`<O>/`: its page, transcript, report and
/// temporary files). `stem` is the glue's name without `.ec`.
pub fn progress_dir(theorem_out: &Path, stem: &str) -> PathBuf {
    theorem_out.join("progress").join(stem)
}

/// The lock of one oracle (story 68): `progress/Eq_<L>_<R>/<O>.lock`.
pub fn oracle_lock_path(theorem_out: &Path, stem: &str, oracle: &str) -> PathBuf {
    progress_dir(theorem_out, stem).join(format!("{oracle}.lock"))
}

/// What a lock file holds: who took it and when (shown to the user, never compared).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct LockContent {
    pid: u32,
    /// Seconds since the Unix epoch.
    started: u64,
}

impl LockContent {
    /// The job this lock text names, if it parses and its pid is alive.
    fn live_job(text: &str, job: &str) -> Option<LiveJob> {
        let c = serde_json::from_str::<LockContent>(text).ok()?;
        pid_is_alive(c.pid).then(|| LiveJob {
            job: job.to_string(),
            pid: c.pid,
            started: c.started,
        })
    }
}

/// A running proof job on `job`, as its lock says: `Eq_<L>_<R>/<O>` for an oracle's lock,
/// `Eq_<L>_<R>` for the lock of a whole equivalence (before story 68).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiveJob {
    pub job: String,
    pub pid: u32,
    /// Seconds since the Unix epoch.
    pub started: u64,
}

impl std::fmt::Display for LiveJob {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} is being proved by pid {} (since {})",
            self.job,
            self.pid,
            clock(self.started)
        )
    }
}

#[derive(Debug, thiserror::Error)]
pub enum LockError {
    #[error("{0}; wait for it or stop it")]
    Held(LiveJob),
    #[error(
        "proof jobs are running under this export, and translation would replace files under \
         them (even with `--force`): {}; wait for them or stop them",
        .0.iter().map(|j| j.to_string()).collect::<Vec<_>>().join("; ")
    )]
    JobsRunning(Vec<LiveJob>),
    #[error("cannot take the lock {}: {source}", path.display())]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

/// The lock files this process holds, so that the second Ctrl-C (which exits from a signal
/// handler, without unwinding) can remove them too: [`release_all_locks`].
static HELD: std::sync::Mutex<Vec<PathBuf>> = std::sync::Mutex::new(Vec::new());

/// The lock of one oracle, [`oracle_lock_path`] (story 68). Removed when dropped, so on every
/// way out of the oracle the process controls: success, error, skip, the first Ctrl-C.
#[derive(Debug)]
pub struct ProofLock {
    path: PathBuf,
}

impl ProofLock {
    /// Takes the lock file `path` (its folder is created if missing) for `job`, the name a
    /// refusal shows.
    ///
    /// The file is created with [`create_if_absent`], holding this process's pid and the start
    /// time. If it exists and its pid is alive, the job is refused ([`LockError::Held`]). If the
    /// pid is dead the lock is stale (a `kill -9`, a crash) and is taken over silently. A pid
    /// that was reused by another process makes a stale lock look live: the start time in the
    /// message is there for the user to judge, nothing more is tried.
    pub fn acquire(path: &Path, job: &str) -> Result<ProofLock, LockError> {
        let path = path.to_path_buf();
        let io = |source| LockError::Io {
            path: path.clone(),
            source,
        };
        let mine = LockContent {
            pid: std::process::id(),
            started: now(),
        };
        let text = serde_json::to_string(&mine).expect("a lock serializes") + "\n";
        for _ in 0..3 {
            if create_if_absent(&path, &text).map_err(io)? {
                HELD.lock().unwrap().push(path.clone());
                return Ok(ProofLock { path });
            }
            let seen = match std::fs::read_to_string(&path) {
                Ok(text) => text,
                // released between the two calls: try again
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                Err(e) => return Err(io(e)),
            };
            if let Some(live) = LockContent::live_job(&seen, job) {
                return Err(LockError::Held(live));
            }
            // stale (or unreadable): remove it, unless somebody replaced it since it was read
            if std::fs::read_to_string(&path).ok().as_deref() == Some(seen.as_str()) {
                match std::fs::remove_file(&path) {
                    Ok(()) => {}
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                    Err(e) => return Err(io(e)),
                }
            }
        }
        Err(io(std::io::Error::other("the lock keeps changing hands")))
    }
}

impl Drop for ProofLock {
    fn drop(&mut self) {
        HELD.lock().unwrap().retain(|p| p != &self.path);
        let _ = std::fs::remove_file(&self.path);
    }
}

/// Removes every lock this process holds. For the second Ctrl-C, which ends the process from
/// the signal handler; a normal exit drops the [`ProofLock`]s instead.
pub fn release_all_locks() {
    if let Ok(held) = HELD.lock() {
        for path in held.iter() {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// The jobs under `theorem_out` whose lock names a live pid: the oracles' locks
/// `progress/Eq_<L>_<R>/<O>.lock`, and an equivalence's `progress/Eq_<L>_<R>/lock` of a job
/// before story 68. Stale locks are ignored.
pub fn live_jobs(theorem_out: &Path) -> std::io::Result<Vec<LiveJob>> {
    let entries = match std::fs::read_dir(theorem_out.join("progress")) {
        Ok(entries) => entries,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(e),
    };
    let mut jobs = Vec::new();
    for entry in entries {
        let entry = entry?;
        let equivalence = entry.file_name().to_string_lossy().into_owned();
        let Ok(locks) = std::fs::read_dir(entry.path()) else {
            continue;
        };
        for lock in locks {
            let lock = lock?;
            let name = lock.file_name().to_string_lossy().into_owned();
            let job = match name.strip_suffix(".lock") {
                Some(oracle) => format!("{equivalence}/{oracle}"),
                None if name == "lock" => equivalence.clone(),
                None => continue,
            };
            if let Ok(text) = std::fs::read_to_string(lock.path()) {
                jobs.extend(LockContent::live_job(&text, &job));
            }
        }
    }
    jobs.sort_by(|a, b| a.job.cmp(&b.job));
    Ok(jobs)
}

/// Translation's check (story 36 §3.3): refuses, `--force` or not, while a proof job under any
/// of `theorem_outs` holds a live lock.
pub fn check_no_live_jobs(theorem_outs: &[PathBuf]) -> Result<(), LockError> {
    let mut all = Vec::new();
    for out in theorem_outs {
        let theorem = out
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned();
        let jobs = live_jobs(out).map_err(|source| LockError::Io {
            path: out.join("progress"),
            source,
        })?;
        all.extend(jobs.into_iter().map(|mut j| {
            j.job = format!("{theorem}/{}", j.job);
            j
        }));
    }
    if all.is_empty() {
        Ok(())
    } else {
        Err(LockError::JobsRunning(all))
    }
}

fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

/// `kill(pid, 0)`: the process exists (a process we may not signal counts as alive).
#[cfg(unix)]
fn pid_is_alive(pid: u32) -> bool {
    if pid == 0 || pid > i32::MAX as u32 {
        return false;
    }
    // SAFETY: signal 0 only checks for existence and permission.
    let rc = unsafe { libc::kill(pid as libc::pid_t, 0) };
    rc == 0 || std::io::Error::last_os_error().raw_os_error() == Some(libc::EPERM)
}

#[cfg(not(unix))]
fn pid_is_alive(_pid: u32) -> bool {
    true
}

/// Local `HH:MM` of a Unix time.
#[cfg(unix)]
fn clock(secs: u64) -> String {
    let t = secs as libc::time_t;
    // SAFETY: `tm` is written by `localtime_r`, which only reads `t`.
    let tm = unsafe {
        let mut tm: libc::tm = std::mem::zeroed();
        if libc::localtime_r(&t, &mut tm).is_null() {
            return format!("{secs}");
        }
        tm
    };
    format!("{:02}:{:02}", tm.tm_hour, tm.tm_min)
}

#[cfg(not(unix))]
fn clock(secs: u64) -> String {
    format!("{secs}")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(test: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("domino-job-{test}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    /// An export with the files `files` and one equivalence whose oracle `O` has the lemma
    /// file `Eq_L_R_O.ec`.
    fn exported_with(files: &[&str]) -> ExportedTheorem {
        let mut exported = ExportedTheorem::default();
        for f in files {
            exported
                .files
                .insert(PathBuf::from(f), format!("text of {f}"));
        }
        exported
            .equivalences
            .push(crate::writers::easycrypt::export::EquivalenceReport {
                proofstep: 0,
                left_name: "L".into(),
                right_name: "R".into(),
                invariants_file: "Eq_L_R_Invariants.ec".into(),
                proof_file: "Eq_L_R.ec".into(),
                oracle_files: vec![("O".into(), "Eq_L_R_O.ec".into())],
                oracle_count: 1,
                admit_count: 1,
                oracle_set_mismatch: None,
                state_relations: vec![],
                helpers: vec![],
                side_compositions: vec![],
            });
        exported
    }

    #[test]
    fn only_the_oracle_lemma_files_are_proof_files() {
        let exported = exported_with(&[]);
        assert!(is_oracle_file(&exported, Path::new("Eq_L_R_O.ec")));
        assert!(!is_oracle_file(&exported, Path::new("Eq_L_R.ec")));
        assert!(!is_oracle_file(
            &exported,
            Path::new("Eq_L_R_Invariants.ec")
        ));
        assert!(!is_oracle_file(&exported, Path::new("Types.ec")));
    }

    #[test]
    fn ensure_translation_files_creates_the_missing_glue_and_invariants_but_not_an_oracle_file() {
        let dir = scratch("invariants");
        let exported = exported_with(&[
            "Eq_L_R.ec",
            "Eq_L_R_O.ec",
            "Eq_L_R_Invariants.ec",
            "Types.ec",
        ]);
        let created = ensure_translation_files(&exported, &dir).unwrap();
        assert_eq!(
            created,
            vec![
                PathBuf::from("Eq_L_R.ec"),
                PathBuf::from("Eq_L_R_Invariants.ec"),
                PathBuf::from("Types.ec")
            ]
        );
        assert!(!dir.join("Eq_L_R_O.ec").exists());
        assert_eq!(
            std::fs::read_to_string(dir.join("Eq_L_R_Invariants.ec")).unwrap(),
            "text of Eq_L_R_Invariants.ec"
        );
    }

    #[test]
    fn two_threads_creating_the_same_file_both_succeed_and_it_holds_one_complete_copy() {
        let dir = scratch("race");
        let text = "line of text\n".repeat(200_000);
        for round in 0..20 {
            let path = dir.join(format!("Types{round}.ec"));
            let created: Vec<bool> = std::thread::scope(|s| {
                let handles: Vec<_> = (0..2)
                    .map(|_| s.spawn(|| create_if_absent(&path, &text).unwrap()))
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            });
            assert_eq!(created.iter().filter(|c| **c).count(), 1, "one creator");
            assert_eq!(std::fs::read_to_string(&path).unwrap(), text);
        }
        // no temporary file is left behind
        let leftovers: Vec<_> = std::fs::read_dir(&dir)
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n.to_string_lossy().ends_with(".tmp"))
            .collect();
        assert!(leftovers.is_empty(), "{leftovers:?}");
    }

    #[test]
    fn an_existing_file_is_never_replaced_or_read() {
        let dir = scratch("existing");
        let path = dir.join("Types.ec");
        assert!(create_if_absent(&path, "first").unwrap());
        assert!(!create_if_absent(&path, "second").unwrap());
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "first");
    }

    #[test]
    fn the_record_round_trips_and_says_what_it_holds() {
        let mut a = OracleRecord::new("A", OracleStatus::Done);
        a.script = Some("+ proc; inline.\n  auto.\n".into());
        a.admits = vec![AdmitRecord {
            node: "N7".into(),
            reason: "stuck".into(),
            claim: "invariant".into(),
            domino: "verified".into(),
        }];
        a.lockstep = Some(LockstepRecord {
            joint_paths: 23,
            ms: 41200,
        });
        let record = SessionRecord::new(
            "T",
            "L",
            "R",
            vec![
                a,
                OracleRecord::new("B", OracleStatus::Interrupted),
                OracleRecord::new("C", OracleStatus::Pending),
            ],
        );
        assert!(!record.complete);
        assert_eq!(record.version, 3);
        let parsed: SessionRecord = serde_json::from_str(&record.to_json()).unwrap();
        assert_eq!(parsed, record);
        assert!(record.to_json().contains(r#""status": "interrupted""#));
        // only done oracles carry a script
        assert_eq!(record.to_json().matches("\"script\"").count(), 1);
        assert_eq!(
            record.resume_line("Eq_L_R.ec"),
            "resuming Eq_L_R: 1 of 3 oracles already proved"
        );
        let all: Vec<_> = record
            .oracles
            .iter()
            .map(|o| OracleRecord::new(&o.name, OracleStatus::Done))
            .collect();
        let all = SessionRecord::new("T", "L", "R", all);
        assert!(all.complete);
        assert_eq!(
            all.skip_line("Eq_L_R.ec"),
            "skipping Eq_L_R: already proved (3 of 3 oracles); --force re-proves it"
        );
    }

    fn line(depth: usize, bullet: bool, sentence: &str) -> ScriptLine {
        ScriptLine {
            depth,
            bullet,
            sentence: sentence.into(),
            comment: None,
        }
    }

    #[test]
    fn an_interrupted_oracle_keeps_its_closed_nodes_and_names_its_in_flight_node() {
        let mut b = OracleRecord::new("B", OracleStatus::Interrupted);
        b.admits = vec![
            AdmitRecord {
                node: "J2".into(),
                reason: "stuck".into(),
                claim: "stuck/partner-not-at-head".into(),
                domino: "verified".into(),
            },
            AdmitRecord {
                node: "N7".into(),
                reason: "interrupted".into(),
                claim: "open-goal".into(),
                domino: "n/a".into(),
            },
        ];
        b.closed = vec![ClosedNode {
            id: "N3".into(),
            script: vec![
                line(0, true, "if."),
                line(1, true, "auto => /#."),
                ScriptLine {
                    comment: Some("(* domino: J2 stuck *)".into()),
                    ..line(1, true, "admit.")
                },
            ],
            admits: vec![b.admits[0].clone()],
        }];
        b.tree_id = Some("18a-2f".into());
        let record = SessionRecord::new("T", "L", "R", vec![b]);
        assert_eq!(record.version, 3);
        let json = record.to_json();
        assert_eq!(
            serde_json::from_str::<SessionRecord>(&json).unwrap(),
            record
        );
        // an interrupted oracle has no script, only its closed nodes
        assert!(!json.contains("\"script\": \""), "{json}");
        assert_eq!(record.oracles[0].in_flight(), Some("N7"));
        assert_eq!(
            OracleRecord::new("C", OracleStatus::Pending).in_flight(),
            None
        );
    }

    #[test]
    fn a_version_2_record_reads_without_closed_nodes() {
        let text = r#"{"version": 2, "theorem": "T", "left": "L", "right": "R", "complete": false,
            "domino": "0.1.0", "updated": "2026-01-01T00:00:00Z",
            "oracles": [{"name": "A", "status": "interrupted",
              "admits": [{"node": "N4", "reason": "interrupted"}],
              "nodes": [{"id": "N0", "tactics": ["sp 1 1."]}]}]}"#;
        let record: SessionRecord = serde_json::from_str(text).unwrap();
        assert_eq!(record.version, 2);
        assert!(record.oracles[0].closed.is_empty());
        assert_eq!(record.oracles[0].in_flight(), Some("N4"));
    }

    /// The smallest joint tree with every kind of thing in it: a stuck point, a pruned child, a
    /// terminal pair with a failed relation, and a node that was not explored.
    const OUTCOME: &str = r#"{
      "tree": {"nodes": [
        {"index": 0, "kind": "split",
         "left": {"head": {"kind": "branch", "label": 3}, "consumed": [[1, 2]], "plumbing": "done-guard"},
         "right": {"head": {"kind": "branch", "label": 4}, "consumed": [], "plumbing": null},
         "answers": [{"query": "left-then-possible", "answer": "sat"}],
         "children": [
           {"left": {"label": 3, "decision": "then"}, "right": null, "outcome": {"kind": "explored", "node": 1}},
           {"left": {"label": 3, "decision": "else"}, "right": null,
            "outcome": {"kind": "pruned", "answer": {"query": "q", "answer": "unsat"}}},
           {"left": null, "right": null, "outcome": {"kind": "not-explored"}}
         ],
         "pair": null, "stuck": "S1"},
        {"index": 1, "kind": "terminal-pair",
         "left": {"head": {"kind": "return", "label": 9}, "consumed": [], "plumbing": null},
         "right": {"head": {"kind": "abort", "label": 7}, "consumed": [], "plumbing": null},
         "answers": [], "children": [], "pair": "J1", "stuck": null}
      ]},
      "pairs": [{"id": "J1", "node": 1,
        "left": {"steps": [{"label": 3, "line": "if x", "decision": "then"}],
                 "terminal": {"label": 9, "line": "return x", "is_abort": false},
                 "lines": [[1, 9]],
                 "effect": {"returns": "x", "state": [{"pkg_inst": "P",
                   "changed": [{"field": "T", "value": "T[k -> v]", "table": {"base": "T", "entries": [{"key": "k", "value": "v"}]}}],
                   "unchanged": ["c"]}],
                   "rand": [{"point": "P.o.r", "ty": "Bits(256)", "draws": 1}],
                   "wheres": [{"name": "w", "value": "f(x)"}], "truncated": false}},
        "right": {"steps": [], "terminal": {"label": 7, "line": "abort", "is_abort": true}, "lines": [], "effect": null},
        "claims": [
          {"claim": "equal-output", "verdict": {"kind": "verified"}},
          {"claim": "invariant", "verdict": {"kind": "goal-fails", "model": "models/J1.smt2"},
           "parts": [{"name": "StateRelation_rel", "verdict": {"kind": "inconclusive", "model": null}},
                         {"name": "StateRelation_other", "verdict": {"kind": "unreachable", "reason": {"kind": "dependency-false", "dependency": "no-abort"}}}]}
        ]}],
      "stuck": [{"id": "S1", "node": 0, "side": "right", "label": 4, "left_label": 3, "right_label": 4,
                 "sample": "P.o.r", "draw": 0, "reason": "pairing-sat-not-valid"}],
      "stop_reason": {"kind": "completed"}
    }"#;

    const SUMMARY: &str = r#"{"joint_paths": 1, "nodes": 2, "pruned_children": 1,
      "node_kinds": {"split": 1, "terminal-pair": 1},
      "claims": [{"claim": "equal-output", "verified": 1, "unreachable": 0, "unreachable_dependency": 0, "goal_fails": 0, "inconclusive": 0}],
      "verdict_combos": [{"verdicts": ["verified", "goal-fails", "not-checked"], "count": 1}],
      "relation_failures": {"rel": 1}, "stuck_points": 1}"#;

    fn saved_tree() -> SavedTree {
        SavedTree {
            version: SavedTree::VERSION,
            oracle: "PKENC".into(),
            id: SavedTree::new_id(),
            domino: "0.1.0".into(),
            fingerprint: "00ff".into(),
            fingerprint_parts: [("code".to_string(), "0f".to_string())].into(),
            outcome: serde_json::from_str(OUTCOME).unwrap(),
            summary: serde_json::from_str(SUMMARY).unwrap(),
            relations: vec!["rel".into()],
            helpers: vec!["same-bit".into()],
        }
    }

    #[test]
    fn a_saved_joint_tree_reads_back_as_it_was_written() {
        let dir = scratch("tree");
        std::fs::create_dir_all(&dir).unwrap();
        let path = saved_tree_path(&dir, "Eq_L_R.ec", "PKENC");
        assert!(path.ends_with("session/Eq_L_R/PKENC.tree.json"));
        assert!(oracle_record_path(&dir, "Eq_L_R.ec", "PKENC")
            .ends_with("session/Eq_L_R/PKENC.record.json"));
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        assert!(matches!(SavedTree::read(&path), Ok(None)));
        let tree = saved_tree();
        std::fs::write(&path, tree.to_json()).unwrap();
        let read = SavedTree::read(&path).unwrap().expect("a tree");
        // every field survives: the outcome and the summary as their JSON
        let value = |t: &SavedTree| serde_json::to_value(t).unwrap();
        assert_eq!(value(&read), value(&tree));
        assert_eq!(
            serde_json::to_value(&read.outcome).unwrap(),
            serde_json::from_str::<serde_json::Value>(&outcome_in_story_50_names()).unwrap()
        );
        assert_eq!(read.outcome.stuck[0].side, "right");
        assert_eq!(read.summary.verdict_combos[0].verdicts[2], "not-checked");
    }

    /// [`OUTCOME`] is spelled as before story 50; this is how it is written now.
    fn outcome_in_story_50_names() -> String {
        OUTCOME
            .replace("\"plumbing\"", "\"exit_guard\"")
            .replace("\"done-guard\"", "\"done-flag\"")
    }

    #[test]
    fn a_tree_saved_before_the_exit_guard_rename_reads_and_writes_the_new_names() {
        let tree = saved_tree();
        let left = &tree.outcome.tree.nodes[0].left;
        assert_eq!(
            left.exit_guard,
            Some(crate::debug::lockstep::ExitGuardKind::DoneFlag)
        );
        let written = tree.to_json();
        assert!(
            written.contains("\"exit_guard\":\"done-flag\""),
            "{written}"
        );
        assert!(
            !written.contains("plumbing") && !written.contains("done-guard"),
            "{written}"
        );
    }

    #[test]
    fn a_tree_of_an_unknown_version_or_unreadable_is_an_error_not_a_tree() {
        let dir = scratch("tree-bad");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("Eq_L_R.A.tree.json");
        let mut newer = serde_json::to_value(saved_tree()).unwrap();
        newer["version"] = 2.into();
        std::fs::write(&path, newer.to_string()).unwrap();
        let err = SavedTree::read(&path).unwrap_err().to_string();
        assert!(err.contains("version 2"), "{err}");
        std::fs::write(&path, "{ not json").unwrap();
        assert!(SavedTree::read(&path).is_err());
    }

    #[test]
    fn a_version_1_record_reads_with_statuses_only() {
        let text = r#"{"version": 1, "theorem": "T", "left": "L", "right": "R", "complete": false,
            "oracles": [{"name": "A", "status": "done"}, {"name": "B", "status": "pending"}]}"#;
        let record: SessionRecord = serde_json::from_str(text).unwrap();
        assert_eq!(record.version, 1);
        assert_eq!(record.done(), 1);
        assert_eq!(record.done_without_script(), 1);
        assert!(!record.oracles[0].is_resumable());
    }

    #[test]
    fn the_old_path_is_read_only_when_the_new_one_is_missing() {
        let dir = scratch("old-path");
        std::fs::create_dir_all(&dir).unwrap();
        let new = equivalence_record_path(&dir, "Eq_A_B.ec");
        let old = old_session_record_path(&dir, "Eq_A_B.ec");
        assert!(old.ends_with("Eq_A_B.session.json"));
        assert_eq!(path_to_read(new.clone(), old.clone()), new);
        std::fs::write(&old, "x").unwrap();
        assert_eq!(path_to_read(new.clone(), old.clone()), old);
        std::fs::create_dir_all(new.parent().unwrap()).unwrap();
        std::fs::write(&new, "x").unwrap();
        assert_eq!(path_to_read(new.clone(), old), new);
    }

    #[test]
    fn a_record_of_the_whole_equivalence_is_split_into_one_record_per_oracle_on_first_use() {
        let dir = scratch("split");
        let mut a = OracleRecord::new("A", OracleStatus::Done);
        a.script = Some("+ proc; inline. auto.".into());
        let b = OracleRecord::new("B", OracleStatus::Interrupted);
        let whole = SessionRecord::new("T", "L", "R", vec![a.clone(), b]);
        // story 67's path; B already has a record of its own, which stays
        let path = equivalence_record_path(&dir, "Eq_L_R.ec");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, whole.to_json()).unwrap();
        let own_b = SessionRecord::new(
            "T",
            "L",
            "R",
            vec![OracleRecord::new("B", OracleStatus::Done)],
        );
        std::fs::write(oracle_record_path(&dir, "Eq_L_R.ec", "B"), own_b.to_json()).unwrap();

        assert_eq!(split_equivalence_record(&dir, "Eq_L_R.ec").unwrap(), 1);
        let read = |o: &str| {
            SessionRecord::read(&oracle_record_path(&dir, "Eq_L_R.ec", o))
                .unwrap()
                .unwrap()
        };
        assert_eq!(read("A").oracles, vec![a]);
        assert!(read("A").complete);
        assert_eq!(read("A").version, whole.version);
        assert_eq!(read("B"), own_b);
        // the old record stays, and splitting again creates nothing
        assert!(path.exists());
        assert_eq!(split_equivalence_record(&dir, "Eq_L_R.ec").unwrap(), 0);
        let names = ["A", "B", "C"].map(String::from);
        let joined = SessionRecord::join(&[read("B"), read("A")], &names[..2]).unwrap();
        assert_eq!(
            joined
                .oracles
                .iter()
                .map(|o| o.name.as_str())
                .collect::<Vec<_>>(),
            ["A", "B"]
        );
        assert!(joined.complete);
        // an oracle without a record is pending, so the equivalence is not complete
        let joined = SessionRecord::join(&[read("A"), read("B")], &names).unwrap();
        assert_eq!(
            joined.oracles[2],
            OracleRecord::new("C", OracleStatus::Pending)
        );
        assert!(!joined.complete);
        assert!(SessionRecord::join(&[], &names).is_none());
        assert_eq!(
            split_equivalence_record(&scratch("split-none"), "Eq_L_R.ec").unwrap(),
            0
        );
    }

    #[test]
    fn timestamps_are_rfc_3339() {
        assert_eq!(rfc3339(0), "1970-01-01T00:00:00Z");
        assert_eq!(rfc3339(1_709_210_096), "2024-02-29T12:34:56Z");
        assert_eq!(rfc3339(4_102_444_799), "2099-12-31T23:59:59Z");
    }

    #[test]
    fn removing_records_deletes_every_session_json_and_tree_json_under_the_directory_and_nothing_else(
    ) {
        let dir = scratch("remove");
        std::fs::create_dir_all(dir.join("sub")).unwrap();
        std::fs::create_dir_all(dir.join("session/Eq_A_B")).unwrap();
        std::fs::create_dir_all(dir.join("progress/Eq_A_B")).unwrap();
        for f in [
            "Eq_A_B.session.json",
            "Eq_A_B.PKENC.tree.json",
            "sub/Eq_C_D.session.json",
            "session/Eq_A_B/record.json",
            "session/Eq_A_B/PKENC.tree.json",
            "Eq_A_B.ec",
            "progress/Eq_A_B/report.txt",
        ] {
            std::fs::write(dir.join(f), "x").unwrap();
        }
        // story 67: the old and the new paths both go
        assert_eq!(remove_records_and_trees(&dir).unwrap(), 5);
        assert!(dir.join("Eq_A_B.ec").exists());
        assert!(dir.join("progress/Eq_A_B/report.txt").exists());
        assert!(!dir.join("session/Eq_A_B/record.json").exists());
        assert!(!dir.join("Eq_A_B.session.json").exists());
        assert!(!dir.join("Eq_A_B.PKENC.tree.json").exists());
        assert_eq!(remove_records_and_trees(&dir.join("missing")).unwrap(), 0);
    }

    /// A pid that certainly belongs to no process: a child that has been waited for.
    fn dead_pid() -> u32 {
        let mut child = std::process::Command::new("true").spawn().unwrap();
        let pid = child.id();
        child.wait().unwrap();
        pid
    }

    fn write_lock(path: &Path, pid: u32) {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let c = LockContent {
            pid,
            started: now(),
        };
        std::fs::write(path, serde_json::to_string(&c).unwrap()).unwrap();
    }

    #[test]
    fn a_lock_held_by_a_live_pid_refuses_and_names_it() {
        let out = scratch("lock-live");
        let path = oracle_lock_path(&out, "Eq_L_R", "O");
        assert!(path.ends_with("progress/Eq_L_R/O.lock"));
        write_lock(&path, std::process::id());
        let err = ProofLock::acquire(&path, "Eq_L_R/O").unwrap_err();
        let text = err.to_string();
        assert!(
            text.starts_with(&format!(
                "Eq_L_R/O is being proved by pid {} (since ",
                std::process::id()
            )),
            "{text}"
        );
        assert!(text.ends_with("); wait for it or stop it"), "{text}");
        // the refused job leaves the holder's lock alone
        assert!(path.exists());
    }

    #[test]
    fn a_lock_held_by_a_dead_pid_is_taken_over_and_removed_on_drop() {
        let path = oracle_lock_path(&scratch("lock-dead"), "Eq_L_R", "O");
        write_lock(&path, dead_pid());
        let lock = ProofLock::acquire(&path, "Eq_L_R/O").unwrap();
        let text = std::fs::read_to_string(&path).unwrap();
        let c: LockContent = serde_json::from_str(&text).unwrap();
        assert_eq!(c.pid, std::process::id());
        // and while it is held, a second job is refused
        assert!(matches!(
            ProofLock::acquire(&path, "Eq_L_R/O"),
            Err(LockError::Held(_))
        ));
        // the lock of another oracle of the equivalence is another file
        let other = oracle_lock_path(&scratch("lock-dead"), "Eq_L_R", "P");
        drop(ProofLock::acquire(&other, "Eq_L_R/P").unwrap());
        drop(lock);
        assert!(!path.exists());
    }

    #[test]
    fn an_unreadable_lock_is_stale() {
        let path = oracle_lock_path(&scratch("lock-junk"), "Eq_L_R", "O");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, "not json").unwrap();
        let lock = ProofLock::acquire(&path, "Eq_L_R/O").unwrap();
        assert!(path.exists());
        drop(lock);
        assert!(!path.exists());
    }

    #[test]
    fn translation_sees_live_locks_only() {
        let out = scratch("lock-translation");
        write_lock(&oracle_lock_path(&out, "Eq_A_B", "O"), std::process::id());
        write_lock(&oracle_lock_path(&out, "Eq_C_D", "O"), dead_pid());
        // the lock of a whole equivalence, as a job before story 68 took it
        write_lock(&out.join("progress/Eq_E_F/lock"), std::process::id());
        let jobs = live_jobs(&out).unwrap();
        let names: Vec<&str> = jobs.iter().map(|j| j.job.as_str()).collect();
        assert_eq!(names, ["Eq_A_B/O", "Eq_E_F"]);
        let err = check_no_live_jobs(std::slice::from_ref(&out))
            .unwrap_err()
            .to_string();
        assert!(err.contains("Eq_A_B/O is being proved by pid"), "{err}");
        assert!(!err.contains("Eq_C_D"), "{err}");
        std::fs::remove_dir_all(out.join("progress/Eq_A_B")).unwrap();
        std::fs::remove_dir_all(out.join("progress/Eq_E_F")).unwrap();
        check_no_live_jobs(std::slice::from_ref(&out)).unwrap();
        check_no_live_jobs(&[out.join("missing")]).unwrap();
    }
}
