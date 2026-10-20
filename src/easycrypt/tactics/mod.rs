// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino easycrypt prove`: proofs from lockstep execution (story 27).
//!
//! Each oracle is a lemma of its own, `Eq_<L>_<R>_<O>.ec` (story 68, ADR 0013), proved by its
//! own EasyCrypt process; up to [`TacticsOptions::jobs`] oracles of an equivalence at once
//! ([`oracles`]). For each selected oracle: run lockstep execution on the oracle (`domino debug
//! --easycrypt`'s engine, its artifacts written the same way), then walk the joint tree alongside
//! a live EasyCrypt session ([`driver`]), send each step, read the goals back as JSON, and write
//! down what EasyCrypt accepted as the proof of the oracle lemma. What could not be closed is an
//! `admit` labelled with the claim, the invariant relation, the `J`/`S` id and what Domino itself
//! concluded. The equivalence's own `Eq_<L>_<R>.ec` only joins the oracle lemmas; it is a
//! translation file, and no proof job touches it.
//!
//! **The file on disk is what has been proved so far** (story 33): the oracle file and its
//! report are rewritten together, atomically, after the oracle (or, with
//! [`WriteGranularity::Node`], after every joint node, or, with [`WriteGranularity::Tactic`], the
//! default, after every accepted sentence, the oracle **sealed**). Nothing compiles the written
//! file during a run (ADR 0005): every sentence in it was accepted by the live session.
//!
//! **Ctrl-C** (story 34, [`TacticsOptions::stop`]) stops the run where it stands: the running
//! EasyCrypt sentences are interrupted, lockstep execution stops at its next node, the oracles in
//! flight are sealed and written, no other oracle is started, and the result says so
//! ([`Interrupted`]).
//!
//! **An unanswered interrupt** (`SessionError::Unresponsive`: EasyCrypt did not answer the
//! interrupts [`Session::send`] kept sending) seals the oracle in flight like a Ctrl-C and gives
//! its EasyCrypt up, but the job goes on: its next oracle has a fresh EasyCrypt anyway (a
//! **respawn**). After [`MAX_RESPAWNS`] of them the next one ends the job
//! ([`EquivalenceTactics::ended_early`]). An answer that shows EasyCrypt *swallowed* an interrupt
//! is warned about once per run ([`SwallowWatch`]).
//!
//! **Resuming an interrupted oracle** (ADR 0008, [`ResumeMode`]): lockstep execution's joint tree
//! is saved under `session/Eq_<L>_<R>/<oracle>.tree.json`, beside the session record, before the
//! oracle's first sentence. An oracle the record holds as `interrupted` is walked again on that saved tree, its
//! closed nodes kept, instead of being proved from scratch.
//!
//! - [`script`]: the accepted sentences, bullets and indentation.
//! - [`goals`]: reading goals from the JSON.
//! - [`driver`]: the prover.
//! - [`oracles`]: the proof job of one equivalence, its workers, and its page with one row for
//!   each oracle, `progress/Eq_<L>_<R>/index.html`.
//! - [`live`], `live::page`: the live page of one oracle, `progress/Eq_<L>_<R>/<O>/index.html`
//!   (story 28, 36).
//!
//! **Side-invariant jobs** (story 69, ADR 0014): the side-invariant lemmas of a composition,
//! `SideInv_<C>_<O>.ec`, are proved the same way, one oracle at a time, along the side tree of
//! one-sided execution (symbolic-execution story 25) and in a `hoare` judgement ([`JobKind`]).
//! Their records, saved trees and locks are `session/SideInv_<C>/<O>.record.json`,
//! `<O>.tree.json` and `progress/SideInv_<C>/<O>.lock`. A proof job never proves side invariants:
//! `--proofstep` stops when the side-invariant files of its compositions are missing, and a
//! whole-theorem run proves the compositions in parallel with the equivalences.
//!
//! **Package-invariant jobs** (story 76, ADR 0016): `prove --pkg-inv P` proves the package
//! lemmas of each variant `<V>` of package `P`. The package-invariant lemma of each oracle,
//! `PkgInv_<V>_<O>.ec`, is walked as a side-invariant lemma is, along the package tree
//! (symbolic-execution story 29), with no router and each import call an open call
//! (`call (_: true)`, ADR 0017). Its records, saved trees and locks are under `PkgInv_<V>`.
//! Then the frame lemmas and the start lemma are checked ([`fixed`]).
//!
//! `domino easycrypt export` never gets here.

mod driver;
mod fixed;
mod goals;
mod live;
mod oracles;
mod script;

use std::fmt::Write as _;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use thiserror::Error;

use crate::debug::lockstep::LockstepOutcome;
use crate::debug::lockstep_fingerprint::{describe_part, Fingerprint};
use crate::debug::lockstep_run::{run_lockstep_command, LockstepDebugOptions, LockstepSummary};
use crate::debug::pkg_run::{pkg_debug_dir, pkg_fingerprint, run_pkg_command};
use crate::debug::progress::eprintln_above_bars;
use crate::debug::side_run::{run_side_command, side_debug_dir, side_fingerprint};
use crate::gamehops::equivalence::smtrewrite::without_custom_smt_warning;
use crate::project::Project;
use crate::theorem::Theorem;
use crate::transforms::theorem_transforms::EasyCryptTransform;
use crate::transforms::TheoremTransform;
use crate::util::smtsolver::SmtSolverBackend;
use crate::writers::easycrypt::export::{
    EquivalenceReport, ExportedTheorem, PkgInvReport, SideInvReport,
};
use crate::writers::easycrypt::invariant::{
    invariant_ops, leaf_part_ops, package_invariant_ops, side_invariant_ops,
};
use crate::writers::easycrypt::lower::inline_oracle_ec;
use crate::writers::easycrypt::progress::{ExportObserver, NopExportObserver};
use crate::writers::easycrypt::EcExportError;

use super::check::{
    describe_mismatch, ok_or_reject, sentences_until_proof, CheckError, EquivalenceSetup,
};
use super::job::{
    equivalence_record_path, is_oracle_file, old_saved_tree_path, old_session_record_path,
    oracle_record_path, path_to_read, saved_tree_path, split_equivalence_record, ClosedNode,
    LockError, LockstepRecord, OracleRecord, OracleStatus, SavedTree, SessionRecord,
    SessionRecordError,
};
use super::json::Goal;
use super::session::{Session, SessionError, SessionEvent, Want, JSON_BRANCH};
use super::transcript::{Role, SentenceCtx};

pub use super::transcript::{EcTranscriptMode, GOAL_CONCL_CAP, GOAL_HYPS_CAP};
pub use live::{strip_timings, LiveConfig, LiveHandle};

pub use driver::{Admit, AdmitReason, DominoView, OracleStats, Timeouts};
use driver::{Judgement, OracleTree, Prover, Resume, Sealed};

#[derive(Debug, Error)]
pub enum TacticsError {
    #[error(transparent)]
    Session(#[from] SessionError),
    #[error(transparent)]
    Check(#[from] CheckError),
    #[error(transparent)]
    Export(#[from] crate::writers::easycrypt::EcExportError),
    #[error(transparent)]
    Transform(#[from] crate::transforms::theorem_transforms::EquivalenceTransformError),
    #[error(transparent)]
    Record(#[from] SessionRecordError),
    #[error(transparent)]
    Lock(#[from] LockError),
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("invalid `ssp.toml`: {0}")]
    Config(String),
    /// `prove --pkg-inv P` for a package without package invariants, or none of the theorem.
    #[error("package `{package}` has no package lemmas in this theorem: the theorem does not use it, or it has no package invariant")]
    NoPackageInvariants { package: String },
    /// `prove --side-inv C` for a composition without side invariants, or none of the theorem.
    #[error("composition `{composition}` has no side invariants in this theorem: no package of it has a package invariant, and it has no game invariant")]
    NoSideInvariants { composition: String },
}

#[derive(Debug, Clone)]
pub struct TacticsOptions {
    /// Only this proofstep (index into the theorem's game hops).
    pub proofstep: Option<usize>,
    /// Only this exported oracle: the rest keep `+ proc; inline. admit.`.
    pub oracle: Option<String>,
    /// How long one EasyCrypt sentence may run (`--ec-timeout`).
    pub ec_timeout: Duration,
    /// Lemma names for the last `smt(…)` fallbacks: `ssp.toml` `[easycrypt] smt_hints`.
    pub smt_hints: Vec<String>,
    /// Per-query timeout of the lockstep engine's solver, in milliseconds.
    pub lockstep_timeout_ms: Option<u64>,
    /// The quick close, `auto => /#.` on every program goal (§3.3). Off only to exercise the walk.
    pub quick_close: bool,
    /// The most time splitting one leaf by meaning may take before its remaining parts are
    /// admitted; `None` (the default) for no limit.
    pub leaf_budget: Option<Duration>,
    /// What `ec-transcript.jsonl` keeps of EasyCrypt's answers (`--ec-transcript`).
    pub ec_transcript: EcTranscriptMode,
    /// How often `Eq_*.ec` and its report are written (`--write-granularity`).
    pub write_granularity: WriteGranularity,
    /// Set by a Ctrl-C handler to stop the run (story 34). The run then stops where it stands,
    /// seals the oracle in flight and returns normally, its result [`Interrupted`].
    pub stop: Option<Arc<AtomicBool>>,
    /// `prove --force` (story 35): discard the equivalence's session record and restart its
    /// proof from the skeleton, instead of skipping it. Never rewrites a translation file.
    pub force: bool,
    /// `prove --resume`: how an oracle the session record holds as `interrupted` is resumed.
    pub resume: ResumeMode,
    /// Whether the run says, on stderr, which translation files it wrote for each equivalence it
    /// proves (story 44). Off for `--progress none`, and in library use.
    pub announce_stages: bool,
    /// `prove --jobs N` (story 68): how many oracles of an equivalence are proved at once, each
    /// in an EasyCrypt process of its own. 0 counts as 1.
    pub jobs: usize,
    /// `prove --side-inv C` (story 69): only the side-invariant job of composition `C` (its
    /// Domino name), and no equivalence.
    pub side_inv: Option<String>,
    /// `prove --pkg-inv P` (story 76): only the package-invariant job of package `P` (its Domino
    /// name), for each of its variants, and nothing else.
    pub pkg_inv: Option<String>,
}

/// How a proof job resumes an oracle the session record holds as `interrupted` (`--resume`,
/// ADR 0008). Done oracles are resumed as story 37 resumes them under every mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ResumeMode {
    /// Walk the saved joint tree; each closed node's goal is closed with `admit.` and its recorded
    /// script goes into the file, not checked again.
    #[default]
    Trust,
    /// As `trust`, but each closed node's recorded script is sent again; a rejected sentence
    /// makes the node be proved live.
    Replay,
    /// Prove the oracle from scratch, lockstep execution included.
    Restart,
}

impl ResumeMode {
    /// The mode as `--resume` spells it, and as the report and the page show it.
    pub fn slug(self) -> &'static str {
        match self {
            ResumeMode::Trust => "trust",
            ResumeMode::Replay => "replay",
            ResumeMode::Restart => "restart",
        }
    }
}

impl TacticsOptions {
    fn stop_requested(&self) -> bool {
        self.stop
            .as_ref()
            .is_some_and(|s| s.load(Ordering::Relaxed))
    }
}

/// Where a Ctrl-C stopped a tactics run (story 34), or where a job ended early
/// ([`EquivalenceTactics::ended_early`]). Oracles finished before keep their scripts, oracles not
/// reached keep `+ proc; inline. admit.`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Interrupted {
    /// While the proof was being opened, or between two oracles.
    NoOracleInFlight,
    /// During the oracle's lockstep execution, before it sent anything: it keeps its
    /// `+ proc; inline. admit.`.
    Lockstep { oracle: String },
    /// While the oracle was being proved: it was sealed with `admits` admits labelled
    /// `interrupted`, at `node` (`N<k>`, or `router`).
    Sealed {
        oracle: String,
        admits: usize,
        node: String,
    },
}

impl std::fmt::Display for Interrupted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Interrupted::NoOracleInFlight => write!(f, "no oracle was in flight"),
            Interrupted::Lockstep { oracle } => {
                write!(f, "during lockstep execution of {oracle}, nothing sealed")
            }
            Interrupted::Sealed {
                oracle,
                admits,
                node,
            } => write!(f, "sealed {oracle} with {admits} admits at node {node}"),
        }
    }
}

/// The most times one proof job goes on, with a fresh EasyCrypt for its next oracle, after an
/// EasyCrypt left an interrupt unanswered (a **respawn**). The next unanswered interrupt ends the
/// job, as a Ctrl-C would.
const MAX_RESPAWNS: usize = 2;

/// EasyCrypt left an interrupt unanswered while an oracle was proved: the oracle was sealed where
/// the walk stood and its EasyCrypt given up; the job's next oracle gets a fresh one (or the job
/// ended there).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unanswered {
    pub oracle: String,
    /// The joint node the walk was in, as the oracle's `interrupted` admits name it.
    pub node: String,
    /// How many `SIGINT`s went unanswered, and over how long.
    pub signals: usize,
    pub waited: Duration,
    /// The job ended here ([`EquivalenceTactics::ended_early`]): no oracle was started after it.
    pub ended_job: bool,
}

impl std::fmt::Display for Unanswered {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "EasyCrypt left an interrupt unanswered at {} ({} signals over {} s); oracle sealed, ",
            self.node,
            self.signals,
            self.waited.as_secs()
        )?;
        if self.ended_job {
            write!(f, "EasyCrypt not respawned, the job ends")
        } else {
            write!(f, "EasyCrypt given up, the next oracle gets a fresh one")
        }
    }
}

/// The warning for an answer that shows EasyCrypt swallowed an interrupt, given at most once per
/// run ([`SwallowWatch`]). `head` is the start of the message that shows it.
fn swallow_warning(head: &str) -> String {
    format!(
        "EasyCrypt swallowed an interrupt (`{head}`). Rebuild it from branch \
         `{JSON_BRANCH}` (story `easycrypt-never-swallows-an-interrupt`); until then, \
         interrupted attempts can run far past their time and proof jobs may need respawns."
    )
}

/// Looks at every answer of a run for an interrupt EasyCrypt swallowed
/// ([`Response::swallowed_interrupt`](super::json::Response::swallowed_interrupt)) and warns on
/// stderr the first time. The answer itself is left as it is: `ok` and `error` are truthful about
/// EasyCrypt's state.
#[derive(Clone, Default)]
struct SwallowWatch(Arc<std::sync::Mutex<Option<String>>>);

impl SwallowWatch {
    /// The warning, the first time an answer shows a swallowed interrupt; `None` after that.
    fn see(&self, response: &super::json::Response) -> Option<String> {
        let head = response.swallowed_interrupt()?;
        let mut seen = self.0.lock().unwrap();
        if seen.is_some() {
            return None;
        }
        let warning = swallow_warning(&head);
        *seen = Some(warning.clone());
        Some(warning)
    }

    fn warning(&self) -> Option<String> {
        self.0.lock().unwrap().clone()
    }
}

/// When a tactics run writes `Eq_*.ec` and its report (story 33). Both are one mechanism: seal
/// the oracle in flight, write, continue.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriteGranularity {
    /// After each oracle (the default): nothing is open then, so the seal changes nothing.
    Oracle,
    /// After every joint node too, the oracle in flight sealed: to watch a long oracle's proof
    /// accumulate.
    Node,
    /// After every sentence EasyCrypt accepts (story 38, the default): a `kill -9` loses at most
    /// the sentence in flight. Rejected, timed-out and interrupted sentences are never written.
    Tactic,
}

impl Default for TacticsOptions {
    fn default() -> Self {
        TacticsOptions {
            proofstep: None,
            oracle: None,
            ec_timeout: Duration::from_secs(60),
            smt_hints: Vec::new(),
            lockstep_timeout_ms: None,
            quick_close: true,
            leaf_budget: None,
            ec_transcript: EcTranscriptMode::Capped,
            write_granularity: WriteGranularity::Tactic,
            stop: None,
            force: false,
            resume: ResumeMode::Trust,
            announce_stages: false,
            jobs: 1,
            side_inv: None,
            pkg_inv: None,
        }
    }
}

/// The quick close's timeout, at most (`auto => /#.` on every program goal).
const QUICK_CLOSE_TIMEOUT: Duration = Duration::from_secs(2);

/// The lemma names of `ssp.toml`'s `[easycrypt] smt_hints = [...]` (optional).
pub fn read_smt_hints(project_root: &Path) -> Result<Vec<String>, TacticsError> {
    let path = project_root.join("ssp.toml");
    let Ok(text) = std::fs::read_to_string(&path) else {
        return Ok(Vec::new());
    };
    parse_smt_hints(&text)
}

pub(crate) fn parse_smt_hints(text: &str) -> Result<Vec<String>, TacticsError> {
    let value: toml::Value = text
        .parse()
        .map_err(|e: toml::de::Error| TacticsError::Config(e.to_string()))?;
    let Some(hints) = value.get("easycrypt").and_then(|t| t.get("smt_hints")) else {
        return Ok(Vec::new());
    };
    let items = hints.as_array().ok_or_else(|| {
        TacticsError::Config("`[easycrypt] smt_hints` must be a list of lemma names".into())
    })?;
    items
        .iter()
        .map(|item| {
            let name = item.as_str().ok_or_else(|| {
                TacticsError::Config("`[easycrypt] smt_hints` holds non-strings".into())
            })?;
            let valid = !name.is_empty()
                && name
                    .chars()
                    .all(|c| c.is_alphanumeric() || matches!(c, '_' | '.' | '\''));
            if !valid {
                return Err(TacticsError::Config(format!(
                    "`{name}` in `[easycrypt] smt_hints` is not a lemma name"
                )));
            }
            Ok(name.to_string())
        })
        .collect()
}

/// What a job proves (story 69).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum JobKind<'a> {
    /// The oracle lemmas of an equivalence, along joint trees of lockstep execution.
    Equivalence,
    /// The side-invariant lemmas of a composition (its Domino name), along side trees of
    /// one-sided execution.
    SideInvariants(&'a str),
    /// The package lemmas of one variant of a package (its Domino name, story 76): the
    /// package-invariant lemmas along package trees, then the frame lemmas and the start lemma.
    PackageInvariants(&'a str),
}

impl JobKind<'_> {
    /// The composition of a side-invariant job.
    fn composition(self) -> Option<String> {
        match self {
            JobKind::SideInvariants(c) => Some(c.to_string()),
            JobKind::Equivalence | JobKind::PackageInvariants(_) => None,
        }
    }

    /// The package of a package-invariant job.
    fn package(self) -> Option<String> {
        match self {
            JobKind::PackageInvariants(p) => Some(p.to_string()),
            JobKind::Equivalence | JobKind::SideInvariants(_) => None,
        }
    }

    /// Where the lockstep or one-sided execution of `oracle` writes its artifacts.
    fn debug_dir(self, out_dir: &Path, eq: &EquivalenceReport, oracle: &str) -> PathBuf {
        match self {
            JobKind::Equivalence => debug_dir(out_dir, &eq.left_name, &eq.right_name, oracle),
            JobKind::SideInvariants(c) => side_debug_dir(out_dir, c, oracle),
            JobKind::PackageInvariants(p) => pkg_debug_dir(out_dir, p, oracle),
        }
    }

    /// The fingerprint of the tree of `oracle` (ADR 0008).
    fn fingerprint<P: Project>(
        self,
        project: &P,
        theorem: &Theorem<'_>,
        eq: &EquivalenceReport,
        oracle: &str,
    ) -> Result<Fingerprint, crate::debug::driver::DebugError> {
        match self {
            JobKind::Equivalence => Fingerprint::of(project, theorem, eq.proofstep, oracle),
            JobKind::SideInvariants(c) => side_fingerprint(project, &theorem.name, c, oracle),
            JobKind::PackageInvariants(p) => pkg_fingerprint(project, p, oracle),
        }
    }
}

/// What happened to one oracle.
#[derive(Debug, Clone)]
pub struct OracleTactics {
    pub oracle: String,
    /// Set when no tactics could be produced (lockstep failed, no goal): the bullet stays
    /// `admit`.
    pub problem: Option<String>,
    pub stats: OracleStats,
    /// Alignment mismatches (their descriptions): the oracle used the fallback.
    pub alignment_mismatches: Vec<String>,
    pub joint_paths: usize,
    pub nodes: usize,
    pub stuck_points: usize,
    pub lockstep_time: Duration,
    pub easycrypt_time: Duration,
    /// The bullet as written into the file.
    pub script: String,
    /// The outermost closed nodes, for the session record of an interrupted oracle.
    pub closed: Vec<ClosedNode>,
    /// The [`SavedTree::id`] of the joint tree `closed` was proved on, when one was saved.
    pub tree_id: Option<String>,
    /// Not proved by this run: read back from the session record (story 37).
    pub resumed: bool,
    /// Walked again from the session record's closed nodes on the saved joint tree.
    pub resumed_at: Option<ResumedAt>,
    /// The oracle's transcript, `progress/Eq_<L>_<R>/<O>/ec-transcript.jsonl` (story 68); `None`
    /// when this run did not prove it.
    pub transcript: Option<PathBuf>,
}

/// Where an interrupted oracle was resumed, and with what (ADR 0008).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResumedAt {
    /// The in-flight node of the earlier job: `N<k>` or `router`.
    pub node: String,
    /// Closed nodes kept from the session record.
    pub kept: usize,
    /// How they were kept.
    pub mode: ResumeMode,
    /// What changed in the project since the tree was saved (fingerprint parts); empty when
    /// nothing did.
    pub stale: Vec<&'static str>,
}

impl OracleTactics {
    fn empty(oracle: &str, problem: &str) -> OracleTactics {
        OracleTactics {
            oracle: oracle.to_string(),
            problem: Some(problem.to_string()),
            stats: OracleStats::default(),
            alignment_mismatches: vec![],
            joint_paths: 0,
            nodes: 0,
            stuck_points: 0,
            lockstep_time: Duration::ZERO,
            easycrypt_time: Duration::ZERO,
            script: String::new(),
            closed: Vec::new(),
            tree_id: None,
            resumed: false,
            resumed_at: None,
            transcript: None,
        }
    }

    /// The oracle as a session record holds it, or `None` when the record cannot be resumed
    /// from: not done, no script, or a reason or verdict this version does not know.
    fn from_record(record: &OracleRecord) -> Option<OracleTactics> {
        let script = record.script.clone().filter(|_| record.is_resumable())?;
        let admits = record
            .admits
            .iter()
            .map(Admit::from_record)
            .collect::<Option<Vec<_>>>()?;
        let lockstep = record.lockstep.unwrap_or(LockstepRecord {
            joint_paths: 0,
            ms: 0,
        });
        Some(OracleTactics {
            oracle: record.name.clone(),
            problem: None,
            stats: OracleStats {
                admits,
                ..OracleStats::default()
            },
            alignment_mismatches: vec![],
            joint_paths: lockstep.joint_paths,
            nodes: 0,
            stuck_points: 0,
            lockstep_time: Duration::from_millis(lockstep.ms),
            easycrypt_time: Duration::ZERO,
            script,
            closed: Vec::new(),
            tree_id: None,
            resumed: true,
            resumed_at: None,
            transcript: None,
        })
    }

    /// This oracle's entry in the session record.
    fn to_record(&self) -> OracleRecord {
        let interrupted = self
            .stats
            .admits
            .iter()
            .any(|a| a.reason == AdmitReason::Interrupted);
        let status = if interrupted {
            OracleStatus::Interrupted
        } else {
            OracleStatus::Done
        };
        OracleRecord {
            name: self.oracle.clone(),
            status,
            script: (status == OracleStatus::Done).then(|| self.script.clone()),
            admits: self.stats.admits.iter().map(Admit::to_record).collect(),
            lockstep: Some(LockstepRecord {
                joint_paths: self.joint_paths,
                ms: self.lockstep_time.as_millis() as u64,
            }),
            closed: if status == OracleStatus::Interrupted {
                self.closed.clone()
            } else {
                Vec::new()
            },
            tree_id: self
                .tree_id
                .clone()
                .filter(|_| status == OracleStatus::Interrupted),
        }
    }

    /// Admits by reason, in the order of [`AdmitReason::ALL`], nonzero only.
    pub fn admits_by_reason(&self) -> Vec<(AdmitReason, usize)> {
        AdmitReason::ALL
            .iter()
            .map(|&r| {
                (
                    r,
                    self.stats.admits.iter().filter(|a| a.reason == r).count(),
                )
            })
            .filter(|&(_, n)| n > 0)
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct EquivalenceTactics {
    /// The side-invariant job of this composition (story 69), by its Domino name; `None` for
    /// the proof job of an equivalence.
    pub composition: Option<String>,
    /// The package-invariant job of this package (story 76), by its Domino name.
    pub package: Option<String>,
    /// The frame lemmas and the start lemma a package-invariant job checked, in file order.
    pub fixed: Vec<FixedLemma>,
    pub proofstep: usize,
    pub proof_file: String,
    pub left: String,
    pub right: String,
    /// In oracle order, whatever order they finished in.
    pub oracles: Vec<OracleTactics>,
    pub elapsed: Duration,
    /// The written report, relative to the theorem's output directory:
    /// `progress/Eq_<L>_<R>/report.txt`, or with `--oracle O` the oracle's own
    /// `progress/Eq_<L>_<R>/<O>/report.txt`.
    pub report_file: String,
    /// The run was stopped by Ctrl-C while on this equivalence (story 34), or the job ended
    /// early ([`Self::ended_early`]): where.
    pub interrupted: Option<Interrupted>,
    /// Why the job ended before its last oracle although nobody pressed Ctrl-C: EasyCrypt left
    /// more interrupts unanswered than a job respawns it for.
    /// [`Self::interrupted`] says where.
    pub ended_early: Option<String>,
    /// Every interrupt EasyCrypt left unanswered in this job, in order.
    pub unanswered: Vec<Unanswered>,
    /// How many times the oracle files were written, at the last write (story 38).
    pub writes: usize,
}

/// A lemma whose proof a package-invariant job does not walk (story 76): a frame lemma, which
/// translation proves, or the start lemma.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixedLemma {
    /// The lemma file.
    pub file: String,
    /// `None`: EasyCrypt accepted the proof. Otherwise the proof is `admit.`, and this says
    /// why, with the claims the lemma stands for.
    pub admitted: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TheoremTactics {
    pub theorem: String,
    pub equivalences: Vec<EquivalenceTactics>,
    /// The side-invariant jobs (story 69), in the order of the export.
    pub side_invariants: Vec<EquivalenceTactics>,
    /// The package-invariant jobs (story 76), one for each variant, in the order of the export.
    pub package_invariants: Vec<EquivalenceTactics>,
    /// The compositions whose side-invariant files a `--proofstep` job did not find on disk;
    /// their equivalences were not started (story 69 §3.3).
    pub unproved_side_invariants: Vec<String>,
    pub elapsed: Duration,
    /// The warning given when an answer showed EasyCrypt swallowed an interrupt (once per run).
    pub swallowed_interrupt: Option<String>,
}

impl TheoremTactics {
    /// Every oracle of the theorem, in the order of the report: the equivalences', then the
    /// side-invariant jobs', then the package-invariant jobs'.
    pub fn oracles(&self) -> impl Iterator<Item = &OracleTactics> {
        self.jobs().flat_map(|e| e.oracles.iter())
    }

    /// Every job of the run: the equivalences, the side-invariant jobs, then the
    /// package-invariant jobs.
    pub fn jobs(&self) -> impl Iterator<Item = &EquivalenceTactics> {
        self.equivalences
            .iter()
            .chain(&self.side_invariants)
            .chain(&self.package_invariants)
    }

    /// The `admit` count over all translated oracles, and the admitted frame and start lemmas.
    pub fn admit_count(&self) -> usize {
        let fixed = self
            .jobs()
            .flat_map(|e| &e.fixed)
            .filter(|f| f.admitted.is_some())
            .count();
        self.oracles().map(|o| o.stats.admits.len()).sum::<usize>() + fixed
    }

    /// Where Ctrl-C stopped the run, if it did (story 34): the run ended there.
    pub fn interrupted(&self) -> Option<&Interrupted> {
        self.jobs()
            .filter(|e| e.ended_early.is_none())
            .find_map(|e| e.interrupted.as_ref())
    }

    /// Whether a proof job ended before its last oracle without a Ctrl-C
    /// ([`EquivalenceTactics::ended_early`]).
    pub fn ended_early(&self) -> bool {
        self.jobs().any(|e| e.ended_early.is_some())
    }
}

/// The whole of `prove` for one exported theorem, already written to `out_dir`: rewrites
/// the selected `Eq_*.ec` files, writes their reports, and per equivalence its transcript and
/// live page (`progress/Eq_<L>_<R>/`), and returns what it did.
pub fn run_tactics<P, B>(
    theorem: &Theorem<'_>,
    project: &P,
    exported: &ExportedTheorem,
    out_dir: &Path,
    backend: &B,
    options: &TacticsOptions,
) -> Result<TheoremTactics, TacticsError>
where
    P: Project + Sync,
    B: SmtSolverBackend + Sync,
{
    run_tactics_observed(
        theorem,
        project,
        exported,
        out_dir,
        backend,
        options,
        &mut || Box::new(NopExportObserver),
    )
}

/// [`run_tactics`], reporting the `tactics` phase to an observer per oracle (per goal):
/// `progress` is called once for each oracle a worker proves on this thread (`--jobs 1`); with
/// more workers, their oracles report to no observer.
///
/// Each selected equivalence is one **proof job** ([`oracles::prove_equivalence`], story 68): its
/// oracles are proved by up to [`TacticsOptions::jobs`] workers at once, each oracle under its
/// own lock, `progress/Eq_<L>_<R>/<O>.lock`, so jobs on different oracles share nothing they
/// write.
pub fn run_tactics_observed<P, B>(
    theorem: &Theorem<'_>,
    project: &P,
    exported: &ExportedTheorem,
    out_dir: &Path,
    backend: &B,
    options: &TacticsOptions,
    progress: &mut dyn FnMut() -> Box<dyn ExportObserver>,
) -> Result<TheoremTactics, TacticsError>
where
    P: Project + Sync,
    B: SmtSolverBackend + Sync,
{
    std::fs::create_dir_all(out_dir)?;
    let out_dir = std::fs::canonicalize(out_dir).unwrap_or_else(|_| out_dir.to_path_buf());
    let started = Instant::now();
    let (theorem_ec, _aux) = EasyCryptTransform.transform_theorem(theorem)?;
    let swallow = SwallowWatch::default();
    let plan = plan_run(exported, &out_dir, options)?;
    let ctx = RunCtx {
        theorem,
        theorem_ec: &theorem_ec,
        project,
        exported,
        out_dir: &out_dir,
        backend,
        options,
        swallow: &swallow,
        #[cfg(test)]
        fake: tests::TEST_EASYCRYPT.with(|t| t.borrow().clone()),
    };
    let eqs = || {
        plan.equivalences
            .iter()
            .map(|eq| (eq, JobKind::Equivalence))
    };
    // the side-invariant jobs, one after another; on a thread of their own while the
    // equivalences' proof jobs run (story 69 §3.3)
    let sides = || {
        plan.side
            .iter()
            .map(|(eq, c)| (eq, JobKind::SideInvariants(c.as_str())))
    };
    let packages = || {
        plan.packages
            .iter()
            .map(|(eq, p)| (eq, JobKind::PackageInvariants(p.as_str())))
    };
    // `--pkg-inv`: the jobs of the package's variants, and nothing else
    let package_invariants = run_jobs(&ctx, packages(), progress)?;
    let (equivalences, side_invariants) = if !plan.packages.is_empty() {
        (Vec::new(), Vec::new())
    } else if plan.equivalences.is_empty() {
        (Vec::new(), run_jobs(&ctx, sides(), progress)?)
    } else if plan.side.is_empty() {
        (run_jobs(&ctx, eqs(), progress)?, Vec::new())
    } else {
        std::thread::scope(|s| {
            let side = s.spawn(|| run_jobs(&ctx, sides(), &mut || Box::new(NopExportObserver)));
            let equivalences = run_jobs(&ctx, eqs(), progress);
            let side = side.join().expect("the side-invariant jobs do not panic");
            Ok::<_, TacticsError>((equivalences?, side?))
        })?
    };
    Ok(TheoremTactics {
        theorem: theorem.name.clone(),
        equivalences,
        side_invariants,
        package_invariants,
        unproved_side_invariants: plan.unproved,
        elapsed: started.elapsed(),
        swallowed_interrupt: swallow.warning(),
    })
}

/// What a run proves, decided before any job starts (story 69 §3.3).
struct RunPlan {
    /// The equivalences whose proof jobs run, in theorem order.
    equivalences: Vec<EquivalenceReport>,
    /// The side-invariant jobs that run: the job's report (its files are the side-invariant
    /// files of the composition, [`side_job_report`]) and the composition's Domino name.
    side: Vec<(EquivalenceReport, String)>,
    /// The compositions whose side-invariant files a `--proofstep` run did not find.
    unproved: Vec<String>,
    /// The package-invariant jobs that run (`--pkg-inv` only): the job's report
    /// ([`pkg_job_report`]) and the package's Domino name.
    packages: Vec<(EquivalenceReport, String)>,
}

/// - `--pkg-inv P`: the package-invariant job of each variant of `P` only.
/// - `--side-inv C`: the side-invariant job of `C` only.
/// - `--proofstep P`: the proof job of `P`, if the side-invariant files of its compositions are
///   on disk (a file with admits counts); else a warning, and nothing runs.
/// - neither: every equivalence, and the side-invariant job of every composition with side
///   invariants (each job skips what its records say is proved).
fn plan_run(
    exported: &ExportedTheorem,
    out_dir: &Path,
    options: &TacticsOptions,
) -> Result<RunPlan, TacticsError> {
    let side_job = |s: &SideInvReport| (side_job_report(s), s.composition.clone());
    if let Some(package) = &options.pkg_inv {
        let packages: Vec<(EquivalenceReport, String)> = exported
            .package_invariants
            .iter()
            .filter(|p| &p.package == package)
            .map(|p| (pkg_job_report(p), p.package.clone()))
            .collect();
        if packages.is_empty() {
            return Err(TacticsError::NoPackageInvariants {
                package: package.clone(),
            });
        }
        return Ok(RunPlan {
            equivalences: Vec::new(),
            side: Vec::new(),
            unproved: Vec::new(),
            packages,
        });
    }
    if let Some(composition) = &options.side_inv {
        let side = exported
            .side_invariants
            .iter()
            .find(|s| &s.composition == composition)
            .ok_or_else(|| TacticsError::NoSideInvariants {
                composition: composition.clone(),
            })?;
        return Ok(RunPlan {
            equivalences: Vec::new(),
            side: vec![side_job(side)],
            unproved: Vec::new(),
            packages: Vec::new(),
        });
    }
    let Some(proofstep) = options.proofstep else {
        return Ok(RunPlan {
            equivalences: exported.equivalences.clone(),
            side: exported.side_invariants.iter().map(side_job).collect(),
            unproved: Vec::new(),
            packages: Vec::new(),
        });
    };
    let mut plan = RunPlan {
        equivalences: Vec::new(),
        side: Vec::new(),
        unproved: Vec::new(),
        packages: Vec::new(),
    };
    for eq in exported
        .equivalences
        .iter()
        .filter(|e| e.proofstep == proofstep)
    {
        let missing: Vec<&String> = eq
            .side_compositions
            .iter()
            .filter(|c| !side_files_on_disk(exported, out_dir, c))
            .collect();
        for c in &missing {
            eprintln!("{}", unproved_side_invariants_line(c));
            if !plan.unproved.contains(c) {
                plan.unproved.push((*c).clone());
            }
        }
        if missing.is_empty() {
            plan.equivalences.push(eq.clone());
        }
    }
    Ok(plan)
}

/// The warning of a `--proofstep` run whose equivalence needs the side invariants of
/// `composition`, and does not find them on disk (story 69 §3.3).
pub fn unproved_side_invariants_line(composition: &str) -> String {
    format!(
        "warning: side invariants of {composition} are not proved: run prove --side-inv \
         {composition} first"
    )
}

/// Whether `SideInv_<C>.ec` and each `SideInv_<C>_<O>.ec` of `composition` are in `out_dir`.
fn side_files_on_disk(exported: &ExportedTheorem, out_dir: &Path, composition: &str) -> bool {
    exported
        .side_invariants
        .iter()
        .find(|s| s.composition == composition)
        .is_some_and(|s| {
            std::iter::once(&s.join_file)
                .chain(s.oracle_files.iter().map(|(_, f)| f))
                .all(|f| out_dir.join(f).is_file())
        })
}

/// The report the side-invariant job of a composition works from: its "proof file" is
/// `SideInv_<C>.ec`, so its records, trees, locks and pages are under `SideInv_<C>`, and its
/// oracle files are the side-invariant lemma files.
fn side_job_report(side: &SideInvReport) -> EquivalenceReport {
    EquivalenceReport {
        proofstep: 0,
        left_name: side.composition.clone(),
        right_name: String::new(),
        invariants_file: String::new(),
        proof_file: side.join_file.clone(),
        oracle_files: side.oracle_files.clone(),
        oracle_count: side.oracle_files.len(),
        admit_count: side.oracle_files.len(),
        oracle_set_mismatch: None,
        state_relations: Vec::new(),
        helpers: Vec::new(),
        side_compositions: Vec::new(),
    }
}

/// The report the package-invariant job of a package variant works from: its "proof file" is
/// `PkgInv_<V>.ec`, so its records, trees, locks and pages are under `PkgInv_<V>`, and its
/// oracle files are the package-invariant lemma files. The frame and start lemma files are in
/// the export's [`PkgInvReport`].
fn pkg_job_report(pkg: &PkgInvReport) -> EquivalenceReport {
    EquivalenceReport {
        proofstep: 0,
        left_name: pkg.variant.clone(),
        right_name: String::new(),
        invariants_file: String::new(),
        proof_file: pkg.join_file.clone(),
        oracle_files: pkg.oracle_files.clone(),
        oracle_count: pkg.oracle_files.len(),
        admit_count: pkg.oracle_files.len(),
        oracle_set_mismatch: None,
        state_relations: Vec::new(),
        helpers: Vec::new(),
        side_compositions: Vec::new(),
    }
}

/// What every job of one run shares.
struct RunCtx<'a, P, B> {
    theorem: &'a Theorem<'a>,
    theorem_ec: &'a Theorem<'a>,
    project: &'a P,
    exported: &'a ExportedTheorem,
    out_dir: &'a Path,
    backend: &'a B,
    options: &'a TacticsOptions,
    swallow: &'a SwallowWatch,
    /// Read on the thread that started the run: a job may run on another (story 69).
    #[cfg(test)]
    fake: Option<tests::FakeEasyCrypt>,
}

/// Runs the jobs one after another, until one is stopped by Ctrl-C. A job that ended early is
/// not a stop: the next one is a job of its own.
fn run_jobs<'a, P, B>(
    ctx: &RunCtx<'a, P, B>,
    jobs: impl Iterator<Item = (&'a EquivalenceReport, JobKind<'a>)>,
    progress: &mut dyn FnMut() -> Box<dyn ExportObserver>,
) -> Result<Vec<EquivalenceTactics>, TacticsError>
where
    P: Project + Sync,
    B: SmtSolverBackend + Sync,
{
    let mut done = Vec::new();
    for (eq, kind) in jobs {
        let job = oracles::EquivalenceJob {
            theorem: ctx.theorem,
            theorem_ec: ctx.theorem_ec,
            project: ctx.project,
            exported: ctx.exported,
            eq,
            kind,
            out_dir: ctx.out_dir,
            backend: ctx.backend,
            options: ctx.options,
            swallow: ctx.swallow,
            #[cfg(test)]
            fake: ctx.fake.clone(),
        };
        // `None`: skipped, the reason on stderr
        let Some(tactics) = oracles::prove_equivalence(&job, progress)? else {
            continue;
        };
        let interrupted = tactics.interrupted.is_some() && tactics.ended_early.is_none();
        done.push(tactics);
        if interrupted {
            break;
        }
    }
    Ok(done)
}

/// The one line the page shows in place of the export's phases: which translation files were
/// trusted and which this job created.
fn translation_line(exported: &ExportedTheorem, created: &[PathBuf]) -> String {
    let total = exported
        .files
        .keys()
        .filter(|p| !is_oracle_file(exported, p))
        .count();
    if created.is_empty() {
        format!("translation files: all {total} present, trusted as they are")
    } else {
        let names: Vec<String> = created.iter().map(|p| p.display().to_string()).collect();
        format!(
            "translation files: {} of {total} present, trusted as they are; created: {}",
            total - created.len(),
            names.join(", ")
        )
    }
}

/// The stage line of an equivalence that is proved: what this process wrote of the translation
/// (the files it found missing), named when there are fewer than [`NAMED_FILES_LIMIT`] and
/// counted otherwise.
fn translation_files_line(stem: &str, wrote: &[String]) -> String {
    if wrote.is_empty() {
        format!("easycrypt prove: {stem} — translation files already on disk")
    } else if wrote.len() < NAMED_FILES_LIMIT {
        format!(
            "easycrypt prove: {stem} — wrote missing translation files: {}",
            wrote.join(", ")
        )
    } else {
        format!(
            "easycrypt prove: {stem} — wrote {} missing translation files",
            wrote.len()
        )
    }
}

/// A stage line names the files it wrote when fewer than this many.
const NAMED_FILES_LIMIT: usize = 6;

/// What a proof job does with an equivalence.
#[derive(Debug)]
enum JobPlan {
    /// Nothing: the records say it is proved (the reason is on stderr). `record` is the
    /// oracles' records joined: a package-invariant job still checks its frame and start
    /// lemmas from it when their files are not proved yet.
    Skip { record: SessionRecord },
    /// Prove what is not done. `prior` is the oracles' records joined
    /// ([`SessionRecord::join`]): its done oracles are resumed (`None`: from scratch).
    Prove { prior: Option<SessionRecord> },
}

/// Decides what this proof job does for `eq`, whose oracles are `oracles`, from the oracles'
/// session records (story 37 §3.2, story 68), before anything is created or truncated. A record
/// of the whole equivalence, from before story 68, is split first.
///
/// | records | without `--force` | with `--force` |
/// |---|---|---|
/// | none | prove | prove |
/// | all done | skip | from scratch |
/// | some done | resume | from scratch |
///
/// With `--oracle O`: `O` done skips; with `--force`, `O` alone is re-proved (its record is
/// deleted) and every other record is kept.
fn plan_job(
    eq: &EquivalenceReport,
    out_dir: &Path,
    options: &TacticsOptions,
    oracles: &[String],
) -> Result<JobPlan, TacticsError> {
    let file = &eq.proof_file;
    let remove = |path: PathBuf| match std::fs::remove_file(&path) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => Err(e),
        _ => Ok(()),
    };
    if options.force && options.oracle.is_none() {
        // every record goes: the oracles' and the old ones of the whole equivalence
        for oracle in oracles {
            remove(oracle_record_path(out_dir, file, oracle))?;
        }
        remove(equivalence_record_path(out_dir, file))?;
        remove(old_session_record_path(out_dir, file))?;
        return Ok(JobPlan::Prove { prior: None });
    }
    split_equivalence_record(out_dir, file)?;
    let mut records = Vec::new();
    for oracle in oracles {
        records.extend(SessionRecord::read(&oracle_record_path(
            out_dir, file, oracle,
        ))?);
    }
    let Some(mut record) = SessionRecord::join(&records, oracles) else {
        return Ok(JobPlan::Prove { prior: None });
    };
    if options.force {
        let oracle = options.oracle.as_ref().expect("checked above");
        // this oracle alone is proved again: its record goes, the others stay
        remove(oracle_record_path(out_dir, file, oracle))?;
        if let Some(entry) = record.oracles.iter_mut().find(|o| &o.name == oracle) {
            *entry = OracleRecord::new(oracle, OracleStatus::Pending);
        }
        record.complete = false;
        return Ok(JobPlan::Prove {
            prior: Some(record),
        });
    }
    let asked_done = options.oracle.as_ref().map(|o| {
        record
            .oracle(o)
            .is_some_and(|e| e.status == OracleStatus::Done)
    });
    if record.complete && asked_done.unwrap_or(true) {
        eprintln!("{}", record.skip_line(file));
        return Ok(JobPlan::Skip { record });
    }
    if let Some(oracle) = &options.oracle {
        if record
            .oracle(oracle)
            .is_some_and(OracleRecord::is_resumable)
        {
            eprintln!(
                "skipping {oracle} of {}: already proved; --force re-proves it",
                file.trim_end_matches(".ec")
            );
            return Ok(JobPlan::Skip { record });
        }
    }
    if record.done_without_script() > 0 {
        eprintln!("{}", record.version_1_line(file));
    }
    eprintln!("{}", record.resume_line(file));
    Ok(JobPlan::Prove {
        prior: Some(record),
    })
}

/// Closes the front goal with `admit.` outside the walk of an oracle: for `oracle`, or for none.
fn admit_outside(session: &mut Session, oracle: Option<&str>) -> Result<(), SessionError> {
    session.set_context(SentenceCtx {
        oracle: oracle.map(str::to_string),
        node: None,
        role: Role::Admit { part: None },
    })?;
    session.send("admit.", Want::Status).map(|_| ())
}

/// What the EasyCrypt of one oracle is started with.
struct SessionSetup<'a> {
    /// The theorem's output directory: EasyCrypt's working directory and `-I`.
    out_dir: &'a Path,
    transcript_path: &'a Path,
    options: &'a TacticsOptions,
    /// The oracle lemma file, the tag of every transcript record.
    file: &'a str,
    live: &'a LiveHandle,
    swallow: &'a SwallowWatch,
    #[cfg(test)]
    fake: Option<&'a tests::FakeEasyCrypt>,
}

impl SessionSetup<'_> {
    /// A fresh EasyCrypt for the oracle. Its records go to the oracle's transcript (`transcript`;
    /// `None`: none), tagged with the file. Its answers go to the live page and are watched for
    /// a swallowed interrupt. The per-sentence timeout and the stop flag are set.
    fn start(&self, transcript: Option<&File>) -> Result<Session, TacticsError> {
        #[cfg(test)]
        let mut session = spawn_easycrypt(self.out_dir, self.fake)?;
        #[cfg(not(test))]
        let mut session = spawn_easycrypt(self.out_dir)?;
        if let Some(transcript) = transcript {
            session.set_transcript_sink(
                Box::new(transcript.try_clone()?),
                self.transcript_path,
                self.options.ec_transcript,
                self.file,
            );
        }
        let mut page = self.live.session_observer();
        let swallow = self.swallow.clone();
        session.set_observer(Box::new(move |event| {
            if let SessionEvent::Answered { response, .. } = event {
                if let Some(warning) = swallow.see(response) {
                    eprintln_above_bars(&format!("warning: {warning}"));
                }
            }
            page(event);
        }));
        session.set_timeout(self.options.ec_timeout);
        if let Some(stop) = &self.options.stop {
            session.set_stop(stop.clone());
        }
        Ok(session)
    }
}

/// [`Session::start`]; in a test that set [`tests::TEST_EASYCRYPT`] (passed down as `fake`, since
/// workers run on threads of their own), that EasyCrypt with its interrupt timing.
fn spawn_easycrypt(
    dir: &Path,
    #[cfg(test)] fake: Option<&tests::FakeEasyCrypt>,
) -> Result<Session, SessionError> {
    #[cfg(test)]
    if let Some(fake) = fake {
        let mut session = Session::start_with(&fake.binary, dir)?;
        session.set_interrupt_timing(fake.grace, fake.resend);
        return Ok(session);
    }
    Session::start(dir)
}

/// Opens the oracle lemma `file` in a fresh session: every sentence up to `proof.`, after which
/// the oracle's goal is in front. `false`: the run was asked to stop (Ctrl-C) on the way.
fn open_lemma(
    session: &mut Session,
    file: &str,
    source: &str,
    options: &TacticsOptions,
) -> Result<bool, TacticsError> {
    for sentence in sentences_until_proof(file, source)? {
        let response = session.send(&sentence, Want::Full)?;
        if options.stop_requested() {
            return Ok(false);
        }
        ok_or_reject(response, file, &sentence)?;
    }
    Ok(true)
}

/// Where lockstep execution of `oracle` writes its artifacts: beside the export it describes,
/// under the theorem it belongs to (story 19 §4.6). `domino easycrypt debug` writes there too.
pub fn debug_dir(theorem_out: &Path, left: &str, right: &str, oracle: &str) -> PathBuf {
    theorem_out
        .join("!debug!")
        .join(format!("{left}-{right}"))
        .join(oracle)
}

/// One oracle lemma file and its report as a tactics run goes (story 33, story 68): both are
/// rewritten on every write, each atomically, so the file on disk is what has been proved so far
/// and the report next to it describes that file. No `easycrypt compile` (ADR 0005).
struct ProofFile<'a> {
    /// The theorem's name, for the session record.
    theorem: &'a str,
    /// The exported file: `+ proc; inline. admit.`.
    source: &'a str,
    /// The oracle's record this run resumes from.
    prior: Option<&'a SessionRecord>,
    /// `(exported name, EasyCrypt's procedure name)` of the oracle.
    procs: &'a [(String, String)],
    /// The theorem's output directory: the file and the report.
    out_dir: &'a Path,
    /// The oracle's `progress/Eq_<L>_<R>/<O>/`, for the temporary files.
    progress_dir: &'a Path,
    /// The oracle's session record, `session/Eq_<L>_<R>/<O>.record.json`.
    record_path: PathBuf,
    /// When the oracle started: the report's elapsed time.
    started: Instant,
    /// The oracle so far (`proof_file` is the oracle lemma file).
    tactics: EquivalenceTactics,
    /// How many times [`Self::write`] has written (story 38).
    writes: std::cell::Cell<usize>,
}

impl ProofFile<'_> {
    /// Writes the file and its report: the finished oracle, or `in_flight`, the oracle sealed
    /// part way through. Returns what was written.
    fn write(&self, in_flight: Option<&OracleTactics>) -> std::io::Result<EquivalenceTactics> {
        let mut now = self.tactics.clone();
        now.oracles.extend(in_flight.cloned());
        now.elapsed = self.started.elapsed();
        self.writes.set(self.writes.get() + 1);
        now.writes = self.writes.get();
        // the report first: a reader who sees the file finds a report at least as new
        let tmp_dir = self.progress_dir;
        write_atomically(&self.out_dir.join(&now.report_file), tmp_dir, &now.render())?;
        let mut text = self.source.to_string();
        for o in now.oracles.iter().filter(|o| !o.script.is_empty()) {
            let (_, proc_name) = self
                .procs
                .iter()
                .find(|(n, _)| *n == o.oracle)
                .expect("a result names an exported oracle");
            text = with_script(&text, proc_name, &o.script);
        }
        write_atomically(&self.out_dir.join(&now.proof_file), tmp_dir, &text)?;
        // the record last (story 35 §3.4): a crash between the two leaves a record that claims
        // less than the file holds, which costs a re-proof and never claims a missing proof
        let record = self.record(&now);
        if record
            .oracles
            .iter()
            .any(|o| o.status != OracleStatus::Pending)
        {
            write_atomically(&self.record_path, tmp_dir, &record.to_json())?;
        }
        Ok(now)
    }

    /// The session record of `now`. An oracle this run has not got to keeps the entry it had.
    fn record(&self, now: &EquivalenceTactics) -> SessionRecord {
        let oracles = self
            .procs
            .iter()
            .map(
                |(name, _)| match now.oracles.iter().find(|o| &o.oracle == name) {
                    Some(o) => o.to_record(),
                    None => self
                        .prior
                        .and_then(|p| p.oracle(name))
                        .cloned()
                        .unwrap_or_else(|| OracleRecord::new(name, OracleStatus::Pending)),
                },
            )
            .collect();
        SessionRecord::new(self.theorem, &now.left, &now.right, oracles)
    }
}

/// `text`, an exported oracle lemma file, with `script` in place of the oracle's
/// `+ proc; inline. admit.`.
fn with_script(text: &str, proc_name: &str, script: &str) -> String {
    let marker = format!("(* {proc_name} *)\n+ proc; inline. admit.");
    let replacement = format!("(* {proc_name} *)\n{}", script.trim_end());
    text.replacen(&marker, &replacement, 1)
}

/// Writes `text` to `path` through a temporary file in `tmp_dir` (on the same file system) and
/// a rename, so a reader, or a run killed part way, never leaves a half-written file. The
/// temporary file is synced before the rename, so a crash does not leave an empty file either.
/// It is in the job's own `progress/Eq_<L>_<R>/`, a run artifact (story 32), so a leftover one
/// blocks nothing and no other job's temporary file can have the same path.
fn write_atomically(path: &Path, tmp_dir: &Path, text: &str) -> std::io::Result<()> {
    use std::io::Write as _;
    let name = path.file_name().expect("a file path").to_string_lossy();
    let tmp = tmp_dir.join(format!(".{name}.tmp"));
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir)?;
    }
    let mut file = File::create(&tmp)?;
    file.write_all(text.as_bytes())?;
    file.sync_all()?;
    std::fs::rename(&tmp, path)
}

/// How [`tactics_for_oracle`] ended.
enum OracleEnd {
    /// The oracle's bullet is closed, or there was nothing to prove it with (`problem`).
    Done(OracleTactics),
    /// The run was asked to stop (Ctrl-C). `sealed` is the oracle as far as the walk got,
    /// `None` if lockstep execution was stopped before anything was sent.
    Stopped {
        sealed: Option<OracleTactics>,
        at: Interrupted,
    },
    /// EasyCrypt left an interrupt unanswered: the oracle is `sealed` where the walk stood, and
    /// the session cannot be used any more.
    Unanswered {
        sealed: OracleTactics,
        unanswered: Unanswered,
    },
}

/// The joint tree one oracle's walk follows: lockstep execution's, fresh or saved.
struct WalkedTree {
    outcome: LockstepOutcome,
    summary: LockstepSummary,
    /// The SMT names of the state relations of the exported invariant file
    /// (`StateRelation_<name>` is unfolded).
    relations: Vec<String>,
    /// The SMT names of its helper `define-fun`s (`Helper_<name>` is unfolded).
    helpers: Vec<String>,
    /// What lockstep execution took (in the earlier job, for a saved tree).
    lockstep_time: Duration,
    /// Its [`SavedTree::id`]; `None` when it could not be saved.
    id: Option<String>,
}

/// What resuming an interrupted oracle starts from, besides its saved tree.
struct ResumeFrom {
    closed: Vec<ClosedNode>,
    /// The earlier job's in-flight node: `N<k>` or `router`.
    in_flight: String,
    mode: ResumeMode,
    /// What changed since the tree was saved ([`ResumedAt::stale`]).
    stale: Vec<&'static str>,
}

struct Resuming {
    tree: WalkedTree,
    from: ResumeFrom,
}

/// How [`lockstep`] ended.
enum Lockstep {
    /// With a joint tree to walk, saved beside the session record.
    Walk(WalkedTree),
    /// Without: the oracle ends here.
    Ended(OracleEnd),
}

/// The saved joint tree and closed nodes to resume `oracle` from, when the session record holds
/// it as `interrupted` and `--resume` is not `restart` (ADR 0008). `None`, with a warning when
/// the oracle cannot be resumed, means it is proved from scratch.
fn resuming<P: Project>(
    project: &P,
    theorem: &Theorem<'_>,
    eq: &EquivalenceReport,
    kind: JobKind<'_>,
    oracle: &str,
    proof: &ProofFile<'_>,
    options: &TacticsOptions,
) -> Option<Resuming> {
    let prior = proof.prior?;
    let entry = prior
        .oracle(oracle)
        .filter(|e| e.status == OracleStatus::Interrupted)?;
    if options.resume == ResumeMode::Restart {
        return None;
    }
    let restart = |why: &str| {
        eprintln_above_bars(&format!(
            "warning: {why}; {oracle} is proved again from the start"
        ));
    };
    if prior.version < 3 {
        restart(&format!(
            "the session record of {} has no closed nodes (version {})",
            eq.proof_file.trim_end_matches(".ec"),
            prior.version
        ));
        return None;
    }
    let path = path_to_read(
        saved_tree_path(proof.out_dir, &eq.proof_file, oracle),
        old_saved_tree_path(proof.out_dir, &eq.proof_file, oracle),
    );
    let saved = match SavedTree::read(&path) {
        Ok(Some(saved)) if saved.oracle == oracle => saved,
        Ok(Some(saved)) => {
            restart(&format!(
                "{} holds the tree of {}",
                path.display(),
                saved.oracle
            ));
            return None;
        }
        Ok(None) => {
            restart(&format!("{oracle} has no saved joint tree"));
            return None;
        }
        Err(e) => {
            restart(&e.to_string());
            return None;
        }
    };
    // a later lockstep execution (`--resume restart`, or a fallback) rewrites the tree before
    // the record: a job killed in between leaves closed nodes proved on another tree
    if entry.tree_id.as_deref() != Some(saved.id.as_str()) {
        restart(&format!(
            "the saved joint tree of {oracle} is not the one its closed nodes were proved on"
        ));
        return None;
    }
    let stale = match kind.fingerprint(project, theorem, eq, oracle) {
        Ok(now) if now.hex == saved.fingerprint => Vec::new(),
        Ok(now) => {
            let changed = now.changed_from(&saved.fingerprint_parts);
            if changed.is_empty() {
                vec!["the project"]
            } else {
                changed
            }
        }
        Err(_) => vec!["the project"],
    };
    if !stale.is_empty() {
        let what: Vec<&str> = stale.iter().map(|p| describe_part(p)).collect();
        eprintln_above_bars(&format!(
            "warning: the saved joint tree of {oracle} predates changes to {}; the EasyCrypt \
             files may be stale too. Export with --force to start over.",
            what.join(", ")
        ));
    }
    let lockstep_time = Duration::from_millis(entry.lockstep.map_or(0, |l| l.ms));
    Some(Resuming {
        from: ResumeFrom {
            closed: entry.closed.clone(),
            in_flight: entry.in_flight().unwrap_or("router").to_string(),
            mode: options.resume,
            stale,
        },
        tree: WalkedTree {
            outcome: saved.outcome,
            summary: saved.summary,
            relations: saved.relations,
            helpers: saved.helpers,
            lockstep_time,
            id: Some(saved.id),
        },
    })
}

/// Lockstep execution of `oracle`, its joint tree saved beside the session record before the
/// first sentence is sent. Its artifacts are written exactly as `domino easycrypt debug` writes
/// them, so every `S`/`J` of an admit has a page to open.
#[allow(clippy::too_many_arguments)]
fn lockstep<P, B>(
    session: &mut Session,
    project: &P,
    theorem: &Theorem<'_>,
    eq: &EquivalenceReport,
    kind: JobKind<'_>,
    oracle: &str,
    backend: &B,
    options: &TacticsOptions,
    live: &LiveHandle,
    proof: &ProofFile<'_>,
) -> Result<Lockstep, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let lockstep_started = Instant::now();
    live.activity("lockstep execution");
    live.lockstep_started(oracle);
    let mut lockstep_observer = live.lockstep_observer();
    let opts = LockstepDebugOptions::easycrypt(options.lockstep_timeout_ms);
    // next to the export it describes: `<out>/<theorem>/!debug!/<left>-<right>/<oracle>/`, or
    // `!debug!/SideInv_<C>/<oracle>/` for a side tree
    let dir = kind.debug_dir(proof.out_dir, eq, oracle);
    let run = match kind {
        JobKind::Equivalence => run_lockstep_command(
            project,
            &theorem.name,
            eq.proofstep,
            oracle,
            &opts,
            backend,
            Some(dir),
            lockstep_observer.as_mut(),
            options.stop.as_deref(),
        ),
        JobKind::SideInvariants(c) => run_side_command(
            project,
            &theorem.name,
            c,
            oracle,
            &opts,
            backend,
            dir,
            lockstep_observer.as_mut(),
            options.stop.as_deref(),
        ),
        JobKind::PackageInvariants(p) => run_pkg_command(
            project,
            &theorem.name,
            p,
            oracle,
            &opts,
            backend,
            dir,
            lockstep_observer.as_mut(),
            options.stop.as_deref(),
        ),
    };
    // its bars go before the summary line is printed
    drop(lockstep_observer);
    let lockstep_time = lockstep_started.elapsed();
    live.lockstep_finished(
        oracle,
        run.as_ref()
            .ok()
            .map(|r| (r.summary.joint_paths, r.summary.stuck_points)),
        lockstep_time,
        options.stop_requested(),
    );
    live.activity("");
    if options.stop_requested() {
        // lockstep execution was stopped, or has just finished: nothing was sent
        return Ok(Lockstep::Ended(OracleEnd::Stopped {
            sealed: None,
            at: Interrupted::Lockstep {
                oracle: oracle.to_string(),
            },
        }));
    }
    if let Ok(run) = &run {
        live.lockstep_done(Path::new(&run.meta.out_dir));
    }
    let run = match run {
        Ok(run) => run,
        Err(source) => {
            admit_outside(session, Some(oracle))?;
            let mut result =
                OracleTactics::empty(oracle, &format!("lockstep execution failed: {source}"));
            result.lockstep_time = lockstep_time;
            return Ok(Lockstep::Ended(OracleEnd::Done(result)));
        }
    };
    let mut tree = WalkedTree {
        outcome: run.outcome,
        summary: run.summary,
        relations: eq.state_relations.clone(),
        helpers: eq.helpers.clone(),
        lockstep_time,
        id: None,
    };
    tree.id = save_tree(project, theorem, eq, kind, oracle, proof, &tree)?;
    Ok(Lockstep::Walk(tree))
}

/// Writes `session/Eq_<L>_<R>/<oracle>.tree.json`, atomically, replacing any earlier one, and returns
/// its [`SavedTree::id`]. Without a fingerprint there is no tree to trust later: an earlier one
/// is removed, with a warning, and there is no id.
fn save_tree<P: Project>(
    project: &P,
    theorem: &Theorem<'_>,
    eq: &EquivalenceReport,
    kind: JobKind<'_>,
    oracle: &str,
    proof: &ProofFile<'_>,
    tree: &WalkedTree,
) -> std::io::Result<Option<String>> {
    let path = saved_tree_path(proof.out_dir, &eq.proof_file, oracle);
    // lockstep execution has just loaded the invariant files, and warned
    let fingerprint = without_custom_smt_warning(|| kind.fingerprint(project, theorem, eq, oracle));
    let fingerprint = match fingerprint {
        Ok(fingerprint) => fingerprint,
        Err(e) => {
            eprintln_above_bars(&format!(
                "warning: the joint tree of {oracle} is not saved, its fingerprint failed: {e}; \
                 an interrupted {oracle} will be proved again from the start"
            ));
            return match std::fs::remove_file(&path) {
                Err(e) if e.kind() != std::io::ErrorKind::NotFound => Err(e),
                _ => Ok(None),
            };
        }
    };
    // `SavedTree` owns what it holds; the walk keeps its own copy
    let saved = SavedTree {
        version: SavedTree::VERSION,
        oracle: oracle.to_string(),
        id: SavedTree::new_id(),
        domino: env!("CARGO_PKG_VERSION").to_string(),
        fingerprint: fingerprint.hex,
        fingerprint_parts: fingerprint.parts,
        outcome: tree.outcome.clone(),
        summary: tree.summary.clone(),
        relations: tree.relations.clone(),
        helpers: tree.helpers.clone(),
    };
    write_atomically(&path, proof.progress_dir, &saved.to_json())?;
    Ok(Some(saved.id))
}

#[allow(clippy::too_many_arguments)]
fn tactics_for_oracle<P, B>(
    session: &mut Session,
    project: &P,
    theorem: &Theorem<'_>,
    eq: &EquivalenceReport,
    kind: JobKind<'_>,
    setup: &EquivalenceSetup<'_>,
    oracle: &str,
    backend: &B,
    options: &TacticsOptions,
    live: &LiveHandle,
    proof: &mut ProofFile<'_>,
) -> Result<OracleEnd, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    live.oracle_started(oracle);
    // an interrupted oracle of the session record: its saved joint tree, no lockstep execution
    let (walked, resume_from) = match resuming(project, theorem, eq, kind, oracle, proof, options) {
        Some(Resuming { tree, from }) => {
            live.oracle_resumed(&from.in_flight, from.mode.slug());
            let dir = kind.debug_dir(proof.out_dir, eq, oracle);
            if dir.join("index.html").exists() {
                live.lockstep_done(&dir);
            }
            (tree, Some(from))
        }
        None => match lockstep(
            session, project, theorem, eq, kind, oracle, backend, options, live, proof,
        )? {
            Lockstep::Walk(tree) => (tree, None),
            Lockstep::Ended(end) => return Ok(end),
        },
    };
    let lockstep_time = walked.lockstep_time;

    let tree = OracleTree::new(&walked.outcome);
    let resume = resume_from
        .as_ref()
        .map(|from| Resume::new(&tree, from.mode, from.closed.clone(), &from.in_flight));
    let (left, right) = (setup.left_inst, setup.right_inst);
    let (unfold, part_ops, judgement) = match kind {
        JobKind::Equivalence => (
            invariant_ops(project, left, right, &walked.relations, &walked.helpers)
                .map_err(EcExportError::from)?,
            leaf_part_ops(project, left, right, &walked.relations, &walked.helpers)
                .map_err(EcExportError::from)?,
            Judgement::Equiv,
        ),
        // `Comp_<C>.side_inv_<C>` first: the premise unfolded is the one that mentions it
        JobKind::SideInvariants(_) => {
            let ops = side_invariant_ops(project, left.game()).map_err(EcExportError::from)?;
            (ops.clone(), ops, Judgement::Hoare)
        }
        // the templates `PkgInv_<N>_of_<P>`, each standing for its package claim
        JobKind::PackageInvariants(p) => {
            let inst = left
                .game()
                .pkgs
                .iter()
                .find(|i| i.pkg.name == p)
                .expect("the setup's instance has the package");
            let ops = package_invariant_ops(project, inst).map_err(EcExportError::from)?;
            (ops.clone(), ops, Judgement::Package)
        }
    };
    let unfold_ops: Vec<String> = unfold.into_iter().map(|op| op.name).collect();
    // the listings the alignment check compares with: only an equivalence has a router to align
    let listings = match kind {
        JobKind::Equivalence => Some((
            inline_oracle_ec(setup.left_inst, oracle)?,
            inline_oracle_ec(setup.right_inst, oracle)?,
        )),
        JobKind::SideInvariants(_) | JobKind::PackageInvariants(_) => None,
    };
    let began = Instant::now();
    let resumed_at = |kept: usize| {
        resume_from.as_ref().map(|from| ResumedAt {
            node: from.in_flight.clone(),
            kept,
            mode: from.mode,
            stale: from.stale.clone(),
        })
    };
    let result_of = |sealed: Sealed| OracleTactics {
        oracle: oracle.to_string(),
        problem: None,
        stats: sealed.stats,
        alignment_mismatches: sealed.mismatches,
        joint_paths: walked.summary.joint_paths,
        nodes: walked.summary.nodes,
        stuck_points: walked.summary.stuck_points,
        lockstep_time,
        easycrypt_time: began.elapsed(),
        script: sealed.script,
        closed: sealed.closed,
        tree_id: walked.id.clone(),
        resumed: false,
        resumed_at: resumed_at(sealed.kept),
        transcript: None,
    };
    // `--write-granularity node`: seal, write, continue. A failed write stops the writes; the
    // last good one stays on disk and the error ends the run after the oracle.
    let mut write_failed: Option<std::io::Error> = None;
    let mut write_sealed = |sealed: Sealed| {
        if write_failed.is_none() {
            let partial = result_of(sealed);
            if let Err(e) = proof.write(Some(&partial)) {
                write_failed = Some(e);
            }
        }
    };
    let mut prover = Prover {
        session,
        judgement,
        script: Default::default(),
        tree: &tree,
        hints: &options.smt_hints,
        unfold_ops: &unfold_ops,
        part_ops: &part_ops,
        quick_close: options.quick_close,
        oracle,
        leaf_budget: options.leaf_budget,
        deadline: None,
        timeouts: Timeouts {
            general: options.ec_timeout,
            quick_close: QUICK_CLOSE_TIMEOUT.min(options.ec_timeout),
        },
        stats: OracleStats::default(),
        live: Some(live.clone()),
        checkpoint: match options.write_granularity {
            WriteGranularity::Oracle => None,
            WriteGranularity::Node | WriteGranularity::Tactic => Some(&mut write_sealed),
        },
        per_sentence: options.write_granularity == WriteGranularity::Tactic,
        node: None,
        mismatches: Vec::new(),
        stopped: None,
        resume,
        premises: Vec::new(),
        binders: Vec::new(),
        last_smt: None,
        admit_smt: None,
    };
    let proved = prover.oracle(|goal: &Goal| {
        // a side tree or package tree comes from the listing of the lemma's own program
        let Some((left_ir, right_ir)) = &listings else {
            return Vec::new();
        };
        match super::check::align_goal(
            goal,
            (left_ir, &setup.left_flag),
            (right_ir, &setup.right_flag),
        ) {
            None => vec!["`proc; inline.` did not give an equivS goal".to_string()],
            Some(sides) => sides
                .iter()
                .flat_map(|s| s.alignment.mismatches.iter().map(describe_mismatch))
                .collect(),
        }
    });
    let (stopped, unanswered) = match proved {
        Ok(()) => (None, None),
        Err(SessionError::Stopped) => (
            Some(
                prover
                    .stopped
                    .take()
                    .expect("the walk seals the oracle before it stops"),
            ),
            None,
        ),
        // the walk sealed the oracle where it stood (`Prover::session_failed`)
        Err(SessionError::Unresponsive {
            signals, waited, ..
        }) if prover.stopped.is_some() => {
            let sealed = prover.stopped.take().expect("checked by the guard");
            let unanswered = Unanswered {
                oracle: oracle.to_string(),
                node: sealed.node.clone(),
                signals,
                waited,
                ended_job: false,
            };
            (Some(sealed), Some(unanswered))
        }
        Err(e) => return Err(e.into()),
    };
    let stopped_at = stopped.as_ref().map(|sealed| sealed.node.clone());
    // the oracle's bullet is closed and the seal is the script as it is, or the walk sealed it
    // where it stopped
    let sealed = stopped.unwrap_or_else(|| prover.seal());
    drop(prover);
    if let Some(e) = write_failed {
        return Err(e.into());
    }
    let mut result = result_of(sealed);
    // the walk left the oracle's context, which wrote its last `between` record
    result.stats.time = session.take_time_by_role(oracle);
    let Some(node) = stopped_at else {
        return Ok(OracleEnd::Done(result));
    };
    if let Some(unanswered) = unanswered {
        return Ok(OracleEnd::Unanswered {
            sealed: result,
            unanswered,
        });
    }
    let at = Interrupted::Sealed {
        oracle: oracle.to_string(),
        admits: result
            .stats
            .admits
            .iter()
            .filter(|a| a.reason == AdmitReason::Interrupted)
            .count(),
        node,
    };
    Ok(OracleEnd::Stopped {
        sealed: Some(result),
        at,
    })
}

fn secs(d: Duration) -> String {
    format!("{:.1}s", d.as_secs_f32())
}

impl EquivalenceTactics {
    /// The report: `progress/Eq_<L>_<R>/report.txt`, and the same text on stdout.
    pub fn render(&self) -> String {
        let mut out = String::new();
        match (&self.composition, &self.package) {
            (Some(c), _) => {
                let _ = writeln!(
                    out,
                    "tactics for {} (side invariants of {c})",
                    self.proof_file
                );
            }
            (None, Some(p)) => {
                let _ = writeln!(
                    out,
                    "tactics for {} (package invariants of {p})",
                    self.proof_file
                );
            }
            (None, None) => {
                let _ = writeln!(
                    out,
                    "tactics for {} (proofstep {}: {} ~ {})",
                    self.proof_file, self.proofstep, self.left, self.right
                );
            }
        }
        for o in &self.oracles {
            if o.resumed {
                let _ = writeln!(
                    out,
                    "  {}: resumed from session record (lockstep {} joint paths, {} admits)",
                    o.oracle,
                    o.joint_paths,
                    o.stats.admits.len()
                );
                for a in &o.stats.admits {
                    let _ = writeln!(out, "    admit {}", a.fields());
                }
                continue;
            }
            if let Some(problem) = &o.problem {
                let _ = writeln!(out, "  {}: no tactics ({problem})", o.oracle);
                continue;
            }
            if let Some(at) = &o.resumed_at {
                let _ = write!(
                    out,
                    "  {}: resumed at {} ({} closed node{} kept, {})",
                    o.oracle,
                    at.node,
                    at.kept,
                    if at.kept == 1 { "" } else { "s" },
                    at.mode.slug()
                );
                if !at.stale.is_empty() {
                    let _ = write!(out, "; saved joint tree is stale ({})", at.stale.join(", "));
                }
                out.push('\n');
            }
            let _ = writeln!(
                out,
                "  {}: lockstep {} joint paths, {} nodes, {} stuck points ({})",
                o.oracle,
                o.joint_paths,
                o.nodes,
                o.stuck_points,
                secs(o.lockstep_time)
            );
            let by_reason = o.admits_by_reason();
            let admits = if by_reason.is_empty() {
                "no admit".to_string()
            } else {
                let parts: Vec<String> = by_reason
                    .iter()
                    .map(|(r, n)| format!("{} {n}", r.slug()))
                    .collect();
                format!("{} admits ({})", o.stats.admits.len(), parts.join(", "))
            };
            let _ = writeln!(
                out,
                "    goals closed: {}, {admits}, fallbacks: {}, EasyCrypt time {} ({} attempts undone)",
                o.stats.closed,
                o.stats.fallbacks,
                secs(o.easycrypt_time),
                o.stats.attempts_undone
            );
            if !o.stats.time.is_empty() {
                out += &o.stats.time.render(o.easycrypt_time);
            }
            for m in &o.alignment_mismatches {
                let _ = writeln!(out, "    alignment mismatch (fallback used): {m}");
            }
            for a in &o.stats.admits {
                let _ = writeln!(out, "    admit {}", a.fields());
                if a.reason == AdmitReason::DominoVerifiedEcFailed {
                    let goal: String = a.goal.chars().take(4000).collect();
                    let _ = writeln!(out, "      goal: {goal}");
                }
            }
            for u in self.unanswered.iter().filter(|u| u.oracle == o.oracle) {
                let _ = writeln!(out, "    {u}");
            }
        }
        match (&self.interrupted, &self.ended_early) {
            (Some(at), Some(why)) => {
                let _ = writeln!(out, "ended early: {at}: {why}");
            }
            (Some(at), None) => {
                let _ = writeln!(out, "interrupted: {at}");
            }
            (None, _) => {}
        }
        for f in &self.fixed {
            match &f.admitted {
                None => {
                    let _ = writeln!(out, "  {}: proved", f.file);
                }
                Some(why) => {
                    let _ = writeln!(out, "  {}: admitted ({why})", f.file);
                }
            }
        }
        let closed: usize = self.oracles.iter().map(|o| o.stats.closed).sum();
        let admits: usize = self
            .oracles
            .iter()
            .map(|o| o.stats.admits.len())
            .sum::<usize>()
            + self.fixed.iter().filter(|f| f.admitted.is_some()).count();
        let _ = writeln!(
            out,
            "{} oracles, {closed} goals closed, {admits} admits, {}",
            self.oracles.len(),
            secs(self.elapsed)
        );
        out
    }
}

impl TheoremTactics {
    pub fn render(&self) -> String {
        let mut out = format!("tactics for theorem {}\n", self.theorem);
        for job in self.jobs() {
            out.push_str(&job.render());
        }
        for c in &self.unproved_side_invariants {
            let _ = writeln!(out, "{}", unproved_side_invariants_line(c));
        }
        for o in self.oracles() {
            if let Some(transcript) = &o.transcript {
                let _ = writeln!(out, "transcript: {}", transcript.display());
            }
        }
        if let Some(warning) = &self.swallowed_interrupt {
            let _ = writeln!(out, "warning: {warning}");
        }
        let _ = writeln!(out, "elapsed: {}", secs(self.elapsed));
        out
    }
}

#[cfg(test)]
mod tests;
