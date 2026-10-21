// SPDX-License-Identifier: MIT OR Apache-2.0

//! Progress reporting for `domino easycrypt export` (story 21).
//!
//! [`export_theorem_observed`](super::export::export_theorem_observed) and
//! [`write_files_observed`](super::export::write_files_observed) stream
//! [`ExportEvent`]s to an [`ExportObserver`]. Modelled on the debugger's
//! `DebugEvent`/`DebugObserver` (`crate::debug::progress`), deliberately not
//! generalised with it.
//!
//! ## Guarantees
//!
//! - Events are emitted synchronously at points the exporter already passes
//!   through, **before** the item they name is built. So when an export fails,
//!   the last event an observer saw is the item that failed.
//! - Nothing an observer does can change the exported files or stdout: the
//!   exporter never reads anything back from it.
//! - [`ExportEvent`] is `#[non_exhaustive]`; a consumer's `match` ends in `_ => {}`.
//!
//! ## Event order
//!
//! ```text
//! ( TheoremStarted
//!     ( PhaseStarted ItemStarted* PhaseFinished )   // transform, types, packages,
//!                                                   // games, invariants, proofs
//!   TheoremFinished )*
//! PhaseStarted{write} ItemStarted* PhaseFinished    // once, over every theorem's files
//! Finished { files_written }
//! ```
//!
//! `domino easycrypt prove` (story 28) then adds, per theorem, one more phase:
//!
//! ```text
//! PhaseStarted{tactics} ( ItemStarted GoalFinished* )* PhaseFinished
//! ```
//!
//! its items are the oracles (`Eq_A_B PKENC`), and a `GoalFinished` is one node of the joint
//! tree whose goal was closed or admitted.
//!
//! `index` fields are 1-based. Every theorem is exported in memory before any file
//! is written (a failed export must not leave a half-written tree), which is why
//! `write` is one phase after the last theorem and its item names carry the
//! theorem's directory (`Full4WHS/Comp_H5.ec`).

use std::io::Write as _;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use indicatif::{MultiProgress, ProgressBar, ProgressDrawTarget, ProgressStyle};

use crate::debug::driver::Verdict;
use crate::debug::progress::{
    clear_screen, register_screen, BarObserver, DebugEvent, DebugObserver, NopObserver, Tally,
};

/// The phases of one export, in the order they run. `Write` runs once at the end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportPhase {
    Transform,
    Types,
    Packages,
    Games,
    Invariants,
    Proofs,
    Write,
    /// `prove`: one item per oracle (story 28).
    Tactics,
}

impl ExportPhase {
    pub fn name(self) -> &'static str {
        match self {
            Self::Transform => "transform",
            Self::Types => "types",
            Self::Packages => "packages",
            Self::Games => "games",
            Self::Invariants => "invariants",
            Self::Proofs => "proofs",
            Self::Write => "write",
            Self::Tactics => "tactics",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExportEvent<'a> {
    TheoremStarted {
        name: &'a str,
        index: usize,
        total: usize,
    },
    PhaseStarted {
        phase: ExportPhase,
        total_items: usize,
    },
    ItemStarted {
        phase: ExportPhase,
        name: &'a str,
        index: usize,
    },
    PhaseFinished {
        phase: ExportPhase,
    },
    TheoremFinished {
        name: &'a str,
    },
    Finished {
        files_written: usize,
    },
    /// `prove`: the goal of joint node `goal` (`N7`) of `oracle` is done, closed or admitted.
    GoalFinished {
        oracle: &'a str,
        goal: &'a str,
        admitted: bool,
    },
    /// `prove` (story 39): lockstep execution of `oracle` starts. It is the longest silent
    /// stretch of an oracle, so the observer makes room for the debugger's own bar.
    LockstepStarted {
        oracle: &'a str,
    },
    /// `prove`: lockstep execution of `oracle` is over. `found` is `(joint paths, stuck points)`,
    /// `None` when it failed; `stopped` when a Ctrl-C ended it early.
    LockstepFinished {
        oracle: &'a str,
        found: Option<(usize, usize)>,
        elapsed: Duration,
        stopped: bool,
    },
    /// `prove` (story 40): the walk of `oracle` enters joint node `node` (`N7`, or `router` for
    /// the router prelude), of a tree of `total` joint nodes. `N7/23` names a node and says how
    /// big the tree is; it is not a percentage. Also sent again when a subtree is done and the
    /// walk is back in its parent.
    NodeStarted {
        oracle: &'a str,
        node: &'a str,
        total: usize,
    },
    /// `prove` (story 40): the prover is about to send `sentence` to EasyCrypt.
    SentenceSent {
        sentence: &'a str,
    },
}

pub trait ExportObserver {
    fn on_event(&mut self, event: &ExportEvent<'_>);

    /// What watches lockstep execution of one oracle (story 39): what `domino debug` would show
    /// for the same progress mode. Nothing by default.
    fn lockstep_observer(&mut self) -> Box<dyn DebugObserver> {
        Box::new(NopObserver)
    }
}

/// `  PKENC  lockstep: 23 joint paths, 1 stuck point in 41.2s`, the line printed when lockstep
/// execution of an oracle ends (story 39).
pub fn lockstep_summary_line(
    oracle: &str,
    found: Option<(usize, usize)>,
    elapsed: Duration,
    stopped: bool,
) -> String {
    format!("  {oracle}  {}", lockstep_summary(found, elapsed, stopped))
}

/// `lockstep: 23 joint paths, 1 stuck point in 41.2s`: [`lockstep_summary_line`] without the
/// oracle.
fn lockstep_summary(found: Option<(usize, usize)>, elapsed: Duration, stopped: bool) -> String {
    let plural =
        |n: usize, one: &str, many: &str| format!("{n} {}", if n == 1 { one } else { many });
    let what = match found {
        Some((pairs, stuck)) => format!(
            "{}, {}",
            plural(pairs, "joint path", "joint paths"),
            plural(stuck, "stuck point", "stuck points")
        ),
        None => "failed".to_string(),
    };
    let stopped = if stopped { " (stopped)" } else { "" };
    format!("lockstep: {what} in {:.1}s{stopped}", elapsed.as_secs_f64())
}

/// `PKENC  N7/23  smt(dec_enc).`, the proving bar's message (story 40): the oracle, the node, and
/// the first line of the tactic being tried. The bar cuts it to the terminal width.
pub fn proving_message(oracle: &str, node: &str, total: usize, sentence: &str) -> String {
    let tactic = sentence
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("");
    format!("{oracle}  {}  {tactic}", node_label(node, total))
}

/// `N7/23`; the router prelude is just `router`.
fn node_label(node: &str, total: usize) -> String {
    if node == "router" {
        node.to_string()
    } else {
        format!("{node}/{total}")
    }
}

/// `  PKENC N7/23`, the plain line of a node (story 40).
fn node_line(oracle: &str, node: &str, total: usize) -> String {
    format!("  {oracle} {}", node_label(node, total))
}

/// The null observer: "no progress".
pub struct NopExportObserver;

impl ExportObserver for NopExportObserver {
    fn on_event(&mut self, _: &ExportEvent<'_>) {}
}

/// The export phases of each theorem, as they went by: what the live translation page (story 28)
/// shows before the tactics start.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PhaseLog {
    /// `(theorem, [(phase name, items)])`, in order. The `write` phase belongs to no theorem and
    /// is under the name `""`.
    pub theorems: Vec<(String, Vec<(&'static str, usize)>)>,
}

impl PhaseLog {
    /// The phases the export went through for `theorem`, followed by the `write` phase.
    pub fn phases_of(&self, theorem: &str) -> Vec<(&'static str, usize)> {
        let of = |name: &str| {
            self.theorems
                .iter()
                .find(|(t, _)| t == name)
                .map(|(_, p)| p.clone())
                .unwrap_or_default()
        };
        let mut phases = of(theorem);
        phases.extend(of(""));
        phases
    }
}

/// Forwards every event to `inner` and remembers the phases in a [`PhaseLog`].
pub struct LoggingExportObserver<'o> {
    inner: &'o mut dyn ExportObserver,
    log: PhaseLog,
    current: String,
}

impl<'o> LoggingExportObserver<'o> {
    pub fn new(inner: &'o mut dyn ExportObserver) -> Self {
        Self {
            inner,
            log: PhaseLog::default(),
            current: String::new(),
        }
    }

    pub fn into_log(self) -> PhaseLog {
        self.log
    }
}

impl ExportObserver for LoggingExportObserver<'_> {
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        match event {
            ExportEvent::TheoremStarted { name, .. } => {
                self.current = name.to_string();
                self.log.theorems.push((name.to_string(), Vec::new()));
            }
            ExportEvent::TheoremFinished { .. } => self.current.clear(),
            ExportEvent::PhaseStarted { phase, total_items } => {
                if self.current.is_empty()
                    && !self.log.theorems.last().is_some_and(|(t, _)| t.is_empty())
                {
                    self.log.theorems.push((String::new(), Vec::new()));
                }
                if let Some((_, phases)) = self.log.theorems.last_mut() {
                    phases.push((phase.name(), *total_items));
                }
            }
            _ => {}
        }
        self.inner.on_event(event);
    }

    fn lockstep_observer(&mut self) -> Box<dyn DebugObserver> {
        self.inner.lockstep_observer()
    }
}

/// Emits `PhaseStarted`, and hands out `ItemStarted`/`PhaseFinished` with the
/// running index, so the exporter's loops stay one line each.
pub(crate) struct PhaseScope<'o> {
    observer: &'o mut dyn ExportObserver,
    phase: ExportPhase,
    next: usize,
}

impl<'o> PhaseScope<'o> {
    pub(crate) fn start(
        observer: &'o mut dyn ExportObserver,
        phase: ExportPhase,
        total_items: usize,
    ) -> Self {
        observer.on_event(&ExportEvent::PhaseStarted { phase, total_items });
        Self {
            observer,
            phase,
            next: 1,
        }
    }

    pub(crate) fn item(&mut self, name: &str) {
        self.observer.on_event(&ExportEvent::ItemStarted {
            phase: self.phase,
            name,
            index: self.next,
        });
        self.next += 1;
    }

    pub(crate) fn finish(self) {
        self.observer
            .on_event(&ExportEvent::PhaseFinished { phase: self.phase });
    }
}

// ---------------------------------------------------------------------------
// Plain
// ---------------------------------------------------------------------------

/// One line per phase and per item on stderr, e.g. `[Full4WHS 2/2] games 3/7: Comp_H5`.
pub struct PlainExportObserver {
    err: std::io::Stderr,
    theorem: Option<(String, usize, usize)>,
    totals: [usize; 8],
}

impl PlainExportObserver {
    pub fn new() -> Self {
        Self {
            err: std::io::stderr(),
            theorem: None,
            totals: [0; 8],
        }
    }

    fn prefix(&self, phase: ExportPhase) -> String {
        match (&self.theorem, phase) {
            (Some((name, i, n)), p) if p != ExportPhase::Write => format!("[{name} {i}/{n}] "),
            _ => String::new(),
        }
    }
}

impl Default for PlainExportObserver {
    fn default() -> Self {
        Self::new()
    }
}

impl ExportObserver for PlainExportObserver {
    #[allow(unreachable_patterns)]
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        let line = match event {
            ExportEvent::TheoremStarted { name, index, total } => {
                self.theorem = Some((name.to_string(), *index, *total));
                format!("[{name} {index}/{total}] theorem")
            }
            ExportEvent::PhaseStarted { phase, total_items } => {
                self.totals[*phase as usize] = *total_items;
                format!(
                    "{}{}: {total_items} item(s)",
                    self.prefix(*phase),
                    phase.name()
                )
            }
            ExportEvent::ItemStarted { phase, name, index } => format!(
                "{}{} {index}/{}: {name}",
                self.prefix(*phase),
                phase.name(),
                self.totals[*phase as usize]
            ),
            ExportEvent::PhaseFinished { .. } => return,
            ExportEvent::TheoremFinished { name } => {
                let line = format!("[{name}] exported");
                self.theorem = None;
                line
            }
            ExportEvent::Finished { files_written } => {
                format!("done: {files_written} file(s) written")
            }
            ExportEvent::GoalFinished {
                oracle,
                goal,
                admitted,
            } => {
                format!(
                    "  {oracle} {goal}: {}",
                    if *admitted { "admitted" } else { "closed" }
                )
            }
            // no per-path lines: they would flood a log (story 39)
            ExportEvent::LockstepStarted { oracle } => format!("  {oracle}  lockstep: started"),
            ExportEvent::LockstepFinished {
                oracle,
                found,
                elapsed,
                stopped,
            } => lockstep_summary_line(oracle, *found, *elapsed, *stopped),
            ExportEvent::NodeStarted {
                oracle,
                node,
                total,
            } => node_line(oracle, node, *total),
            // sentences are in the transcript (story 40)
            ExportEvent::SentenceSent { .. } => return,
            _ => return,
        };
        let _ = writeln!(self.err, "{line}");
    }
}

// ---------------------------------------------------------------------------
// Bar
// ---------------------------------------------------------------------------

/// One `indicatif` bar per phase on stderr, labelled with the current item.
/// Finished phases stay on screen. Draws nothing when stderr is not a terminal.
pub struct BarExportObserver {
    mp: MultiProgress,
    bar: Option<ProgressBar>,
    theorem: Option<(String, usize, usize)>,
    /// The oracle, node and tree size the proving line names (story 40).
    at: Option<(String, String, usize)>,
}

impl BarExportObserver {
    pub fn new() -> Self {
        Self {
            mp: MultiProgress::new(),
            bar: None,
            theorem: None,
            at: None,
        }
    }
}

impl Default for BarExportObserver {
    fn default() -> Self {
        Self::new()
    }
}

impl ExportObserver for BarExportObserver {
    #[allow(unreachable_patterns)]
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        match event {
            ExportEvent::TheoremStarted { name, index, total } => {
                self.theorem = Some((name.to_string(), *index, *total));
                let _ = self.mp.println(format!("theorem {name} ({index}/{total})"));
            }
            ExportEvent::PhaseStarted { phase, total_items } => {
                let bar = self.mp.add(ProgressBar::new(*total_items as u64));
                // while proving, the message is the whole line: oracle, node, tactic (cut to
                // the terminal's width), and the time spent on the current sentence (story 40)
                let template = if *phase == ExportPhase::Tactics {
                    "{prefix:<9} {bar:12.cyan/blue} {pos}/{len}  {wide_msg} {elapsed}"
                } else {
                    "{prefix:<11} {bar:24.cyan/blue} {pos}/{len}  {msg}"
                };
                bar.set_style(
                    ProgressStyle::with_template(template)
                        .unwrap_or_else(|_| ProgressStyle::default_bar()),
                );
                bar.set_prefix(phase.name());
                self.bar = Some(bar);
            }
            ExportEvent::ItemStarted { name, index, .. } => {
                if let Some(bar) = &self.bar {
                    bar.set_position(index.saturating_sub(1) as u64);
                    bar.set_message(name.to_string());
                }
            }
            ExportEvent::PhaseFinished { .. } => {
                if let Some(bar) = self.bar.take() {
                    bar.finish_with_message("done");
                }
            }
            ExportEvent::TheoremFinished { .. } => self.theorem = None,
            ExportEvent::GoalFinished {
                oracle,
                goal,
                admitted,
            } => {
                if let Some(bar) = &self.bar {
                    bar.set_message(format!(
                        "{oracle} {goal} {}",
                        if *admitted { "admitted" } else { "closed" }
                    ));
                }
            }
            ExportEvent::NodeStarted {
                oracle,
                node,
                total,
            } => {
                self.at = Some((oracle.to_string(), node.to_string(), *total));
                if let Some(bar) = &self.bar {
                    bar.set_message(proving_message(oracle, node, *total, ""));
                    bar.reset_elapsed();
                }
            }
            ExportEvent::SentenceSent { sentence } => {
                if let (Some(bar), Some((oracle, node, total))) = (&self.bar, &self.at) {
                    bar.set_message(proving_message(oracle, node, *total, sentence));
                    bar.reset_elapsed();
                }
            }
            // the debugger's bar has the screen while lockstep execution runs: this one steps
            // aside, so the two never overwrite each other's lines (story 39)
            ExportEvent::LockstepStarted { .. } => {
                if let Some(bar) = &self.bar {
                    self.mp.remove(bar);
                }
            }
            ExportEvent::LockstepFinished {
                oracle,
                found,
                elapsed,
                stopped,
            } => {
                let _ = self
                    .mp
                    .println(lockstep_summary_line(oracle, *found, *elapsed, *stopped));
                if let Some(bar) = self.bar.take() {
                    self.bar = Some(self.mp.add(bar));
                }
            }
            _ => {}
        }
    }

    fn lockstep_observer(&mut self) -> Box<dyn DebugObserver> {
        Box::new(BarObserver::new())
    }
}

// ---------------------------------------------------------------------------
// The progress board (story 82, ADR 0020)
// ---------------------------------------------------------------------------

/// Where the proof jobs of one command run report their progress: one board for each run,
/// shared by every thread that proves (the oracle workers of `--jobs N` and the side-invariant
/// chain). A worker sees only the [`ExportObserver`] of its oracle.
pub trait ProgressBoard: Sync {
    /// A proof job (`stem`: `Eq_H4_H5`) starts, with `oracles` oracles to prove. Its oracle rows
    /// go under it. Dropping the job progress ends the job.
    fn job(&self, stem: &str, oracles: usize) -> Box<dyn JobProgress>;
}

/// The progress of one proof job. It has no status method: it counts the oracle rows it made
/// and the rows that were dropped (ADR 0020 point 2).
pub trait JobProgress: Send + Sync {
    /// An oracle starts on this thread. The observer is used on this thread only; dropping it
    /// ends the oracle's row.
    fn oracle(&self, name: &str) -> Box<dyn ExportObserver>;
}

/// The board of "no progress".
pub struct NopProgressBoard;

impl ProgressBoard for NopProgressBoard {
    fn job(&self, _: &str, _: usize) -> Box<dyn JobProgress> {
        Box::new(NopProgressBoard)
    }
}

impl JobProgress for NopProgressBoard {
    fn oracle(&self, _: &str) -> Box<dyn ExportObserver> {
        Box::new(NopExportObserver)
    }
}

/// `--progress plain`: each oracle writes the oracle lines of [`PlainExportObserver`] with the
/// key `<stem>/<oracle>` at the start (its item line becomes `<stem>/<oracle>  started`; the
/// `tactics` phase lines go), and the job writes `<stem>  oracles <done>/<total> done` when an
/// oracle row is dropped, whatever way the oracle ended. Each line is one write on a locked stderr, so lines of two threads never
/// mix.
pub struct PlainProgressBoard;

impl ProgressBoard for PlainProgressBoard {
    fn job(&self, stem: &str, oracles: usize) -> Box<dyn JobProgress> {
        Box::new(PlainJob(Arc::new(PlainCounts {
            stem: stem.to_string(),
            total: oracles,
            done: AtomicUsize::new(0),
        })))
    }
}

struct PlainJob(Arc<PlainCounts>);

struct PlainCounts {
    stem: String,
    total: usize,
    /// The oracle rows that were dropped.
    done: AtomicUsize,
}

impl JobProgress for PlainJob {
    fn oracle(&self, name: &str) -> Box<dyn ExportObserver> {
        Box::new(PlainRow {
            key: format!("{}/{name}", self.0.stem),
            job: self.0.clone(),
        })
    }
}

struct PlainRow {
    key: String,
    job: Arc<PlainCounts>,
}

fn write_stderr_line(line: &str) {
    let _ = writeln!(std::io::stderr().lock(), "{line}");
}

impl ExportObserver for PlainRow {
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        if let Some(line) = keyed_line(&self.key, event) {
            write_stderr_line(&line);
        }
    }
}

impl Drop for PlainRow {
    fn drop(&mut self) {
        let done = self.job.done.fetch_add(1, Ordering::SeqCst) + 1;
        write_stderr_line(&job_line(&self.job.stem, done, self.job.total));
    }
}

/// `Eq_H4_H5  oracles 3/7 done`, the plain line of a job when one of its oracles ends.
fn job_line(stem: &str, done: usize, total: usize) -> String {
    format!("{stem}  oracles {done}/{total} done")
}

/// The plain line of `event` in the row `key` (`Eq_H4_H5/PKENC`): the key comes from the row,
/// not from the event. `None` for an event plain mode does not show.
fn keyed_line(key: &str, event: &ExportEvent<'_>) -> Option<String> {
    let what = match event {
        // in place of `tactics 3/7: Eq_H4_H5 PKENC`: the key names the oracle, and the job line
        // counts the oracles
        ExportEvent::ItemStarted { .. } => "started".to_string(),
        ExportEvent::GoalFinished { goal, admitted, .. } => {
            format!("{goal}: {}", if *admitted { "admitted" } else { "closed" })
        }
        ExportEvent::LockstepStarted { .. } => "lockstep: started".to_string(),
        ExportEvent::LockstepFinished {
            found,
            elapsed,
            stopped,
            ..
        } => lockstep_summary(*found, *elapsed, *stopped),
        ExportEvent::NodeStarted { node, total, .. } => node_label(node, *total),
        _ => return None,
    };
    Some(format!("{key}  {what}"))
}

/// One observer for the whole job, as before story 82: it sees one `tactics` phase with one item
/// for each oracle, and the phase ends when the job progress is dropped. The rows of the job
/// take turns on it, under a lock.
#[cfg(test)]
pub(crate) struct OneObserverJob(Arc<Mutex<OneObserver>>);

#[cfg(test)]
struct OneObserver {
    inner: Box<dyn ExportObserver + Send>,
    /// The oracles the job proves.
    total: usize,
    phase_started: bool,
    items: usize,
}

#[cfg(test)]
impl OneObserverJob {
    pub(crate) fn new(inner: Box<dyn ExportObserver + Send>, oracles: usize) -> Self {
        Self(Arc::new(Mutex::new(OneObserver {
            inner,
            total: oracles,
            phase_started: false,
            items: 0,
        })))
    }
}

#[cfg(test)]
impl JobProgress for OneObserverJob {
    fn oracle(&self, _: &str) -> Box<dyn ExportObserver> {
        Box::new(OneObserverRow(self.0.clone()))
    }
}

#[cfg(test)]
impl Drop for OneObserverJob {
    fn drop(&mut self) {
        let mut s = self.0.lock().unwrap_or_else(|e| e.into_inner());
        if s.phase_started {
            s.inner.on_event(&ExportEvent::PhaseFinished {
                phase: ExportPhase::Tactics,
            });
        }
    }
}

#[cfg(test)]
struct OneObserverRow(Arc<Mutex<OneObserver>>);

#[cfg(test)]
impl ExportObserver for OneObserverRow {
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        let mut s = self.0.lock().unwrap_or_else(|e| e.into_inner());
        match *event {
            ExportEvent::PhaseStarted { phase, .. } if !s.phase_started => {
                s.phase_started = true;
                let total_items = s.total;
                s.inner
                    .on_event(&ExportEvent::PhaseStarted { phase, total_items });
            }
            ExportEvent::ItemStarted { phase, name, .. } => {
                s.items += 1;
                let index = s.items;
                s.inner
                    .on_event(&ExportEvent::ItemStarted { phase, name, index });
            }
            // the job starts the phase once, and ends it after its last oracle
            ExportEvent::PhaseStarted { .. } | ExportEvent::PhaseFinished { .. } => {}
            _ => s.inner.on_event(event),
        }
    }

    fn lockstep_observer(&mut self) -> Box<dyn DebugObserver> {
        self.0
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .inner
            .lockstep_observer()
    }
}

/// `--progress bar` (story 83, ADR 0020 point 3): one screen for the whole command run, with a
/// header row for each running job and one row for each running oracle under it:
///
/// ```text
/// Eq_H4_H5  tactics ███░░░ 3/7  done 2, running 2
///   PKENC  lockstep  node 40 sync-branch  pairs 23 ✓21 ·0 ✗0 ?2 ✂0      41s
///   DEC  N7/23  smt(dec_enc).                                            12s
/// ```
///
/// The board is the only screen of bars while it lives: making it registers its screen for
/// [`eprintln_above_bars`](crate::debug::progress::eprintln_above_bars) (a debug build fails if
/// another screen is active), dropping it clears the screen. A row leaves when its oracle or job
/// ends; the lines it leaves print above the live rows.
pub struct BarProgressBoard {
    mp: MultiProgress,
}

impl BarProgressBoard {
    /// The board on stderr. Draws nothing when stderr is not a terminal.
    pub fn new() -> Self {
        Self::with_target(ProgressDrawTarget::stderr())
    }

    fn with_target(target: ProgressDrawTarget) -> Self {
        let mp = MultiProgress::with_draw_target(target);
        register_screen(&mp);
        Self { mp }
    }
}

impl Default for BarProgressBoard {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for BarProgressBoard {
    fn drop(&mut self) {
        let _ = self.mp.clear();
        clear_screen();
    }
}

const JOB_ROW: &str = "{prefix} tactics {bar:12.cyan/blue} {pos}/{len}  {msg}";
const ORACLE_ROW: &str = "  {wide_msg} {elapsed:>4}";

fn row_style(template: &str) -> ProgressStyle {
    ProgressStyle::with_template(template).unwrap_or_else(|_| ProgressStyle::default_bar())
}

impl ProgressBoard for BarProgressBoard {
    fn job(&self, stem: &str, oracles: usize) -> Box<dyn JobProgress> {
        let header = self.mp.add(ProgressBar::new(oracles as u64));
        header.set_style(row_style(JOB_ROW));
        header.set_prefix(stem.to_string());
        let job = Arc::new(BarJobState {
            mp: self.mp.clone(),
            header,
            rows: Mutex::new(Vec::new()),
            next: AtomicUsize::new(0),
        });
        job.show_counts();
        Box::new(BarJob(job))
    }
}

/// A job on the bar board. Dropping it takes its header off the screen.
struct BarJob(Arc<BarJobState>);

struct BarJobState {
    mp: MultiProgress,
    header: ProgressBar,
    /// The rows of the running oracles with their numbers, in the order they started.
    rows: Mutex<Vec<(usize, ProgressBar)>>,
    /// The number of the next row.
    next: AtomicUsize,
}

impl BarJobState {
    /// `done <d>, running <r>`: the position of the header is the count of dropped rows.
    fn show_counts(&self) {
        let running = self.rows.lock().unwrap_or_else(|e| e.into_inner()).len();
        let done = self.header.position();
        self.header
            .set_message(format!("done {done}, running {running}"));
    }

    /// A new oracle row and its number, under the header and the rows already there.
    fn add_row(&self) -> (usize, ProgressBar) {
        let mut rows = self.rows.lock().unwrap_or_else(|e| e.into_inner());
        let after = rows.last().map_or(&self.header, |(_, r)| r).clone();
        let row = self.mp.insert_after(&after, ProgressBar::new_spinner());
        row.set_style(row_style(ORACLE_ROW));
        row.enable_steady_tick(Duration::from_secs(1));
        let id = self.next.fetch_add(1, Ordering::SeqCst);
        rows.push((id, row.clone()));
        (id, row)
    }

    /// The oracle of `row` ended: its row leaves, the header counts it as done.
    fn remove_row(&self, id: usize, row: &ProgressBar) {
        row.finish_and_clear();
        self.mp.remove(row);
        self.rows
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .retain(|(i, _)| *i != id);
        self.header.inc(1);
        self.show_counts();
    }
}

impl JobProgress for BarJob {
    fn oracle(&self, name: &str) -> Box<dyn ExportObserver> {
        let (id, bar) = self.0.add_row();
        self.0.show_counts();
        Box::new(BarRow {
            job: self.0.clone(),
            id,
            bar,
            oracle: name.to_string(),
            at: None,
            node_open: false,
            admits: 0,
            lockstep: None,
        })
    }
}

impl Drop for BarJob {
    fn drop(&mut self) {
        self.0.header.finish_and_clear();
        self.0.mp.remove(&self.0.header);
    }
}

/// The row of one running oracle on the bar board.
struct BarRow {
    job: Arc<BarJobState>,
    /// The number of the row in its job.
    id: usize,
    bar: ProgressBar,
    oracle: String,
    /// The node and the tree size of the proving line.
    at: Option<(String, usize)>,
    /// The goal of the current node is not closed or admitted yet.
    node_open: bool,
    admits: usize,
    /// The `lockstep_summary_line` of the oracle; it prints with the oracle's end.
    lockstep: Option<String>,
}

impl BarRow {
    fn show_proving(&self, sentence: &str) {
        if let Some((node, total)) = &self.at {
            self.bar
                .set_message(proving_message(&self.oracle, node, *total, sentence));
            self.bar.reset_elapsed();
        }
    }

    /// `done, 2 admits`, or `interrupted at N7` when the row ends on a node whose goal is open.
    /// The router prelude has no goal of its own, so a row never ends `interrupted at router`.
    fn end_text(&self) -> String {
        match &self.at {
            Some((node, _)) if self.node_open && node != "router" => {
                format!("interrupted at {node}")
            }
            _ if self.admits == 1 => "done, 1 admit".to_string(),
            _ => format!("done, {} admits", self.admits),
        }
    }
}

impl ExportObserver for BarRow {
    #[allow(unreachable_patterns)]
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        match event {
            ExportEvent::LockstepStarted { .. } => {
                self.bar.set_message(format!("{}  lockstep", self.oracle));
                self.bar.reset_elapsed();
            }
            ExportEvent::LockstepFinished {
                oracle,
                found,
                elapsed,
                stopped,
            } => self.lockstep = Some(lockstep_summary_line(oracle, *found, *elapsed, *stopped)),
            ExportEvent::NodeStarted { node, total, .. } => {
                self.at = Some((node.to_string(), *total));
                self.node_open = true;
                self.show_proving("");
            }
            ExportEvent::SentenceSent { sentence } => self.show_proving(sentence),
            ExportEvent::GoalFinished { admitted, .. } => {
                self.node_open = false;
                self.admits += usize::from(*admitted);
            }
            _ => {}
        }
    }

    fn lockstep_observer(&mut self) -> Box<dyn DebugObserver> {
        Box::new(LockstepRow {
            mp: self.job.mp.clone(),
            bar: self.bar.clone(),
            oracle: self.oracle.clone(),
            node: String::new(),
            pairs: 0,
            tally: Tally::default(),
        })
    }
}

impl Drop for BarRow {
    fn drop(&mut self) {
        let line = match self.lockstep.take() {
            Some(lockstep) => format!("{lockstep}; {}", self.end_text()),
            None => format!("  {}  {}", self.oracle, self.end_text()),
        };
        let _ = self.job.mp.println(line);
        self.job.remove_row(self.id, &self.bar);
    }
}

/// Lockstep execution of one oracle, on the oracle's own row: `PKENC  lockstep  node 40
/// sync-branch  pairs 23 ✓21 ·0 ✗0 ?2 ✂0`. Failing goals and stuck points print above the rows,
/// as in [`BarObserver`](crate::debug::progress::BarObserver).
struct LockstepRow {
    mp: MultiProgress,
    bar: ProgressBar,
    oracle: String,
    node: String,
    pairs: usize,
    tally: Tally,
}

impl LockstepRow {
    fn show(&self) {
        self.bar.set_message(format!(
            "{}  lockstep  {}  pairs {} {}",
            self.oracle,
            self.node,
            self.pairs,
            self.tally.render()
        ));
    }
}

impl DebugObserver for LockstepRow {
    #[allow(unreachable_patterns)]
    fn on_event(&mut self, ev: &DebugEvent<'_>) {
        match ev {
            DebugEvent::JointNode { index, kind } => {
                self.node = format!("node {index} {kind}");
                self.show();
            }
            DebugEvent::JointPairChecked { id, claims, .. } => {
                claims.iter().for_each(|c| self.tally.bump(&c.verdict));
                self.pairs += 1;
                self.show();
                if claims
                    .iter()
                    .any(|c| matches!(c.verdict, Verdict::GoalFails { .. }))
                {
                    let _ = self.mp.println(format!("⚠ GOAL FAILS at {id}"));
                }
            }
            DebugEvent::StuckPointFound {
                id,
                side,
                label,
                reason,
            } => {
                let _ = self
                    .mp
                    .println(format!("stuck point {id} ({side} L{label}): {reason}"));
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::debug::driver::ClaimVerdict;

    /// Records every event as one line: a compact, comparable rendering.
    #[derive(Default)]
    pub(crate) struct Recorder(pub Vec<String>);

    impl ExportObserver for Recorder {
        fn on_event(&mut self, ev: &ExportEvent<'_>) {
            self.0.push(match ev {
                ExportEvent::TheoremStarted { name, index, total } => {
                    format!("theorem {name} {index}/{total}")
                }
                ExportEvent::PhaseStarted { phase, total_items } => {
                    format!("phase {} {total_items}", phase.name())
                }
                ExportEvent::ItemStarted { phase, name, index } => {
                    format!("item {} {index} {name}", phase.name())
                }
                ExportEvent::PhaseFinished { phase } => format!("end {}", phase.name()),
                ExportEvent::TheoremFinished { name } => format!("theorem-end {name}"),
                ExportEvent::Finished { files_written } => format!("finished {files_written}"),
                ExportEvent::GoalFinished {
                    oracle,
                    goal,
                    admitted,
                } => {
                    format!("goal {oracle} {goal} {admitted}")
                }
                ExportEvent::NodeStarted {
                    oracle,
                    node,
                    total,
                } => format!("node {oracle} {node}/{total}"),
                ExportEvent::SentenceSent { sentence } => format!("sentence {sentence}"),
                ExportEvent::LockstepStarted { oracle } => format!("lockstep {oracle}"),
                ExportEvent::LockstepFinished { oracle, found, .. } => {
                    format!("lockstep-end {oracle} {found:?}")
                }
            });
        }
    }

    #[test]
    fn logging_observer_remembers_phases_per_theorem_and_the_write_phase() {
        let mut inner = Recorder::default();
        let mut log = LoggingExportObserver::new(&mut inner);
        log.on_event(&ExportEvent::TheoremStarted {
            name: "T",
            index: 1,
            total: 1,
        });
        log.on_event(&ExportEvent::PhaseStarted {
            phase: ExportPhase::Types,
            total_items: 2,
        });
        log.on_event(&ExportEvent::PhaseFinished {
            phase: ExportPhase::Types,
        });
        log.on_event(&ExportEvent::TheoremFinished { name: "T" });
        log.on_event(&ExportEvent::PhaseStarted {
            phase: ExportPhase::Write,
            total_items: 5,
        });
        let log = log.into_log();
        assert_eq!(log.phases_of("T"), [("types", 2), ("write", 5)]);
        assert_eq!(inner.0.len(), 5, "every event is forwarded");
    }

    #[test]
    fn phase_scope_numbers_items_from_one() {
        let mut rec = Recorder::default();
        let mut scope = PhaseScope::start(&mut rec, ExportPhase::Games, 2);
        scope.item("Comp_A");
        scope.item("Comp_B");
        scope.finish();
        assert_eq!(
            rec.0,
            [
                "phase games 2",
                "item games 1 Comp_A",
                "item games 2 Comp_B",
                "end games"
            ]
        );
    }

    #[test]
    fn the_proving_message_names_oracle_node_and_the_first_line_of_the_tactic() {
        assert_eq!(
            proving_message("PKENC", "N7", 23, "smt(dec_enc)."),
            "PKENC  N7/23  smt(dec_enc)."
        );
        assert_eq!(
            proving_message(
                "PKENC",
                "N7",
                23,
                "  seq 2 2 : (a = b /\\\n   c).\n  more\n"
            ),
            "PKENC  N7/23  seq 2 2 : (a = b /\\"
        );
        assert_eq!(
            proving_message("PKENC", "router", 23, "proc; inline."),
            "PKENC  router  proc; inline."
        );
        assert_eq!(proving_message("PKENC", "N1", 3, ""), "PKENC  N1/3  ");
    }

    #[test]
    fn the_plain_observer_has_a_line_per_node_and_none_per_sentence() {
        assert_eq!(node_line("PKENC", "N7", 23), "  PKENC N7/23");
        assert_eq!(node_line("PKENC", "router", 23), "  PKENC router");
        let mut plain = PlainExportObserver::new();
        plain.on_event(&ExportEvent::NodeStarted {
            oracle: "PKENC",
            node: "N7",
            total: 23,
        });
        plain.on_event(&ExportEvent::SentenceSent { sentence: "auto." });
    }

    #[test]
    fn the_bar_observer_follows_node_and_sentence_events() {
        let mut bars = BarExportObserver::new();
        bars.on_event(&ExportEvent::PhaseStarted {
            phase: ExportPhase::Tactics,
            total_items: 1,
        });
        bars.on_event(&ExportEvent::ItemStarted {
            phase: ExportPhase::Tactics,
            name: "Eq O",
            index: 1,
        });
        bars.on_event(&ExportEvent::NodeStarted {
            oracle: "O",
            node: "N7",
            total: 23,
        });
        bars.on_event(&ExportEvent::SentenceSent {
            sentence: "smt(a).\nsecond",
        });
        assert_eq!(bars.bar.as_ref().unwrap().message(), "O  N7/23  smt(a).");
    }

    #[test]
    fn the_lockstep_line_reads_like_the_story() {
        let took = Duration::from_millis(41_240);
        assert_eq!(
            lockstep_summary_line("PKENC", Some((23, 1)), took, false),
            "  PKENC  lockstep: 23 joint paths, 1 stuck point in 41.2s"
        );
        assert_eq!(
            lockstep_summary_line("O", Some((1, 0)), took, false),
            "  O  lockstep: 1 joint path, 0 stuck points in 41.2s"
        );
        assert_eq!(
            lockstep_summary_line("O", None, took, true),
            "  O  lockstep: failed in 41.2s (stopped)"
        );
    }

    #[test]
    fn logging_observer_hands_out_the_inner_observers_lockstep_observer() {
        struct Marks(std::rc::Rc<std::cell::Cell<usize>>);
        impl ExportObserver for Marks {
            fn on_event(&mut self, _: &ExportEvent<'_>) {}
            fn lockstep_observer(&mut self) -> Box<dyn DebugObserver> {
                self.0.set(self.0.get() + 1);
                Box::new(NopObserver)
            }
        }
        let asked = std::rc::Rc::new(std::cell::Cell::new(0));
        let mut inner = Marks(asked.clone());
        let mut log = LoggingExportObserver::new(&mut inner);
        let _ = log.lockstep_observer();
        assert_eq!(asked.get(), 1);
    }

    /// The bar observer steps aside for lockstep execution and is back after it, with its
    /// summary line printed in between (a hidden draw target: nothing is drawn, nothing panics).
    #[test]
    fn the_bar_observer_survives_a_lockstep_interlude() {
        let _lock = screen_lock();
        let mut bars = BarExportObserver::new();
        bars.on_event(&ExportEvent::PhaseStarted {
            phase: ExportPhase::Tactics,
            total_items: 2,
        });
        bars.on_event(&ExportEvent::ItemStarted {
            phase: ExportPhase::Tactics,
            name: "Eq O",
            index: 1,
        });
        for _ in 0..2 {
            bars.on_event(&ExportEvent::LockstepStarted { oracle: "O" });
            drop(bars.lockstep_observer());
            bars.on_event(&ExportEvent::LockstepFinished {
                oracle: "O",
                found: Some((2, 0)),
                elapsed: Duration::from_secs(1),
                stopped: false,
            });
            assert!(bars.bar.is_some(), "the proving bar is back");
        }
    }

    /// Story 82: each plain line of a row starts with `<stem>/<oracle>`, the job's with `<stem>`.
    #[test]
    fn plain_board_lines_start_with_the_key_of_the_row_or_the_job() {
        let key = "Eq_H4_H5/PKENC";
        let line = |e: ExportEvent<'_>| keyed_line(key, &e);
        assert_eq!(
            line(ExportEvent::LockstepStarted { oracle: "other" }).unwrap(),
            "Eq_H4_H5/PKENC  lockstep: started"
        );
        assert_eq!(
            line(ExportEvent::NodeStarted {
                oracle: "PKENC",
                node: "N7",
                total: 23
            })
            .unwrap(),
            "Eq_H4_H5/PKENC  N7/23"
        );
        assert_eq!(
            line(ExportEvent::LockstepFinished {
                oracle: "PKENC",
                found: Some((23, 1)),
                elapsed: Duration::from_millis(41_240),
                stopped: false
            })
            .unwrap(),
            "Eq_H4_H5/PKENC  lockstep: 23 joint paths, 1 stuck point in 41.2s"
        );
        assert_eq!(
            line(ExportEvent::GoalFinished {
                oracle: "PKENC",
                goal: "N7",
                admitted: true
            })
            .unwrap(),
            "Eq_H4_H5/PKENC  N7: admitted"
        );
        assert_eq!(
            line(ExportEvent::ItemStarted {
                phase: ExportPhase::Tactics,
                name: "Eq_H4_H5 PKENC",
                index: 3
            })
            .unwrap(),
            "Eq_H4_H5/PKENC  started"
        );
        assert_eq!(line(ExportEvent::SentenceSent { sentence: "auto." }), None);
        assert_eq!(job_line("Eq_H4_H5", 3, 7), "Eq_H4_H5  oracles 3/7 done");
    }

    /// Story 82: one observer for a whole job sees one `tactics` phase, items numbered across
    /// its oracles, and the end of the phase when the job ends.
    #[test]
    fn one_observer_job_numbers_the_items_of_its_rows_and_ends_the_phase() {
        #[derive(Clone, Default)]
        struct Shared(Arc<Mutex<Recorder>>);
        impl ExportObserver for Shared {
            fn on_event(&mut self, e: &ExportEvent<'_>) {
                self.0.lock().unwrap().on_event(e);
            }
        }
        let seen = Shared::default();
        let job = OneObserverJob::new(Box::new(seen.clone()), 2);
        for name in ["A", "B"] {
            let mut row = job.oracle(name);
            row.on_event(&ExportEvent::PhaseStarted {
                phase: ExportPhase::Tactics,
                total_items: 1,
            });
            row.on_event(&ExportEvent::ItemStarted {
                phase: ExportPhase::Tactics,
                name,
                index: 1,
            });
            row.on_event(&ExportEvent::PhaseFinished {
                phase: ExportPhase::Tactics,
            });
        }
        drop(job);
        assert_eq!(
            seen.0.lock().unwrap().0,
            [
                "phase tactics 2",
                "item tactics 1 A",
                "item tactics 2 B",
                "end tactics"
            ]
        );
    }

    /// The board of story 83 drawn on a terminal in memory, and the terminal.
    fn board_on_screen() -> (BarProgressBoard, indicatif::InMemoryTerm) {
        let term = indicatif::InMemoryTerm::new(20, 100);
        let board = BarProgressBoard::with_target(ProgressDrawTarget::term_like_with_hz(
            Box::new(term.clone()),
            255,
        ));
        (board, term)
    }

    /// The lines of `term` without the timers (`12s` at the end of a row), as `strip_timings`
    /// does for pages.
    fn screen(board: &BarProgressBoard, term: &indicatif::InMemoryTerm) -> Vec<String> {
        // a redraw now, not at the next tick
        board.mp.suspend(|| {});
        term.contents()
            .lines()
            .map(|l| {
                let l = l.trim_end();
                match l.rsplit_once(' ') {
                    Some((head, t))
                        if t.ends_with('s') && t[..t.len() - 1].parse::<u64>().is_ok() =>
                    {
                        head.trim_end().to_string()
                    }
                    _ => l.to_string(),
                }
            })
            .filter(|l| !l.is_empty())
            .collect()
    }

    fn screen_lock() -> std::sync::MutexGuard<'static, ()> {
        crate::debug::progress::SCREEN_TEST_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner())
    }

    fn prove(row: &mut dyn ExportObserver, oracle: &str, node: &str, sentence: &str) {
        row.on_event(&ExportEvent::NodeStarted {
            oracle,
            node,
            total: 23,
        });
        row.on_event(&ExportEvent::SentenceSent { sentence });
    }

    /// Story 83: two oracle rows under one header, each with its node, tactic and timer.
    #[test]
    fn two_oracle_rows_under_one_header() {
        let _lock = screen_lock();
        let (board, term) = board_on_screen();
        let job = board.job("Eq_H4_H5", 7);
        let mut enc = job.oracle("PKENC");
        let mut dec = job.oracle("DEC");
        prove(enc.as_mut(), "PKENC", "N3", "proc; inline.");
        prove(dec.as_mut(), "DEC", "N7", "smt(dec_enc).\nmore");
        let lines = screen(&board, &term);
        assert_eq!(lines.len(), 3, "{lines:#?}");
        assert!(lines[0].starts_with("Eq_H4_H5 tactics"), "{lines:#?}");
        assert!(lines[0].ends_with("0/7  done 0, running 2"), "{lines:#?}");
        assert_eq!(lines[1], "  PKENC  N3/23  proc; inline.");
        assert_eq!(lines[2], "  DEC  N7/23  smt(dec_enc).");
        let raw = term.contents();
        assert!(
            raw.lines().nth(1).unwrap().trim_end().ends_with('s'),
            "a timer: {raw}"
        );
    }

    /// Story 83: the row of an oracle in lockstep shows the node and the pair tally, and the same
    /// row then shows the proving line.
    #[test]
    fn a_row_goes_from_lockstep_to_proving() {
        let _lock = screen_lock();
        let (board, term) = board_on_screen();
        let job = board.job("Eq_A_B", 1);
        let mut row = job.oracle("PKENC");
        row.on_event(&ExportEvent::LockstepStarted { oracle: "PKENC" });
        let mut lockstep = row.lockstep_observer();
        lockstep.on_event(&DebugEvent::JointNode {
            index: 40,
            kind: "sync-branch",
        });
        let claims = [ClaimVerdict {
            claim: "same-output".to_string(),
            verdict: Verdict::Verified,
            model: None,
            parts: Vec::new(),
        }];
        lockstep.on_event(&DebugEvent::JointPairChecked {
            id: "J1",
            claims: &claims,
            elapsed: Duration::from_secs(1),
        });
        assert_eq!(
            screen(&board, &term)[1],
            "  PKENC  lockstep  node 40 sync-branch  pairs 1 ✓1 ·0 ✗0 ?0 ✂0"
        );
        drop(lockstep);
        prove(row.as_mut(), "PKENC", "N7", "auto.");
        assert_eq!(screen(&board, &term)[1], "  PKENC  N7/23  auto.");
    }

    /// Story 83: a finished row leaves, and its lines are above the live rows.
    #[test]
    fn a_finished_row_leaves_and_its_summary_is_above() {
        let _lock = screen_lock();
        let (board, term) = board_on_screen();
        let job = board.job("Eq_A_B", 2);
        let mut enc = job.oracle("PKENC");
        let mut dec = job.oracle("DEC");
        enc.on_event(&ExportEvent::LockstepFinished {
            oracle: "PKENC",
            found: Some((23, 1)),
            elapsed: Duration::from_millis(41_240),
            stopped: false,
        });
        prove(enc.as_mut(), "PKENC", "N1", "auto.");
        enc.on_event(&ExportEvent::GoalFinished {
            oracle: "PKENC",
            goal: "N1",
            admitted: true,
        });
        prove(dec.as_mut(), "DEC", "N7", "auto.");
        drop(enc);
        let lines = screen(&board, &term);
        assert_eq!(
            lines[0],
            "  PKENC  lockstep: 23 joint paths, 1 stuck point in 41.2s; done, 1 admit",
        );
        assert!(lines[1].ends_with("1/2  done 1, running 1"), "{lines:#?}");
        assert_eq!(lines[2], "  DEC  N7/23  auto.");
        assert_eq!(lines.len(), 3, "{lines:#?}");
        drop(dec);
        assert_eq!(screen(&board, &term)[1], "  DEC  interrupted at N7");
    }

    /// Story 83: a line printed while rows are live goes above them; the rows stay whole.
    #[test]
    fn a_line_above_the_rows_tears_no_row() {
        let _lock = screen_lock();
        let (board, term) = board_on_screen();
        let job = board.job("Eq_A_B", 1);
        let mut row = job.oracle("PKENC");
        prove(row.as_mut(), "PKENC", "N7", "auto.");
        let before = screen(&board, &term);
        crate::debug::progress::eprintln_above_bars("warning: something");
        assert_eq!(screen(&board, &term), before);
        drop(board);
        crate::debug::progress::eprintln_above_bars("no screen now");
    }

    /// Story 83: one screen of bars at a time.
    #[test]
    #[cfg(debug_assertions)]
    fn a_second_screen_fails_the_debug_assertion() {
        let _lock = screen_lock();
        let (board, _term) = board_on_screen();
        let second =
            std::panic::catch_unwind(
                || BarProgressBoard::with_target(ProgressDrawTarget::hidden()),
            );
        assert!(second.is_err());
        drop(board);
        let _alone = BarProgressBoard::with_target(ProgressDrawTarget::hidden());
    }
}
