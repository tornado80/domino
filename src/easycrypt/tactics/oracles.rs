// SPDX-License-Identifier: MIT OR Apache-2.0

//! The proof job of one equivalence (story 68, ADR 0013): each oracle is a lemma of its own,
//! `Eq_<L>_<R>_<O>.ec`, proved by a worker in an EasyCrypt process of its own, up to
//! [`TacticsOptions::jobs`] at once.
//!
//! [`prove_equivalence`] reads the oracles' session records (a record of the whole equivalence,
//! from before story 68, is split first), decides what is proved ([`plan_job`]), and hands the
//! oracles to the workers in oracle order. A worker ([`prove_oracle`]) takes the oracle's lock,
//! `progress/Eq_<L>_<R>/<O>.lock`, and skips the oracle with a message when another job holds it.
//! It writes only the oracle's own files: `Eq_<L>_<R>_<O>.ec`, `session/Eq_<L>_<R>/<O>.record.json`
//! and `<O>.tree.json`, and `progress/Eq_<L>_<R>/<O>/` (its page, transcript and report). So two
//! jobs may prove different oracles of one equivalence.
//!
//! The job writes the equivalence's page, `progress/Eq_<L>_<R>/index.html` (one row for each
//! oracle, running ones included), and its report, `progress/Eq_<L>_<R>/report.txt` (the oracles'
//! sections in oracle order, whatever order they finished in), unless it proves one `--oracle`
//! only: then the oracle's own report is the report.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::fmt::Write as _;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Mutex;
use std::time::{Duration, Instant};

use crate::debug::progress::{eprintln_above_bars, DebugObserver};
use crate::project::Project;
use crate::theorem::Theorem;
use crate::util::smtsolver::SmtSolverBackend;
use crate::writers::easycrypt::export::{EquivalenceReport, ExportedTheorem};
use crate::writers::easycrypt::progress::{
    ExportEvent, ExportObserver, ExportPhase, NopExportObserver,
};

use super::super::check::{equivalence_setup, pkg_setup, side_setup, CheckError, EquivalenceSetup};
use super::super::job::{
    create_if_absent, ensure_translation_files, oracle_lock_path, oracle_record_path, progress_dir,
    LiveJob, LockError, OracleStatus, ProofLock, SessionRecord,
};
use super::{
    open_lemma, plan_job, tactics_for_oracle, translation_files_line, translation_line,
    with_script, write_atomically, EquivalenceTactics, Interrupted, JobKind, JobPlan, LiveConfig,
    LiveHandle, OracleEnd, OracleTactics, ProofFile, SessionSetup, SwallowWatch, TacticsError,
    TacticsOptions, Unanswered, MAX_RESPAWNS,
};

/// Everything the proof job of one equivalence works with; shared by its workers.
pub(super) struct EquivalenceJob<'a, P, B> {
    /// The theorem as the project has it (lockstep execution, fingerprints).
    pub theorem: &'a Theorem<'a>,
    /// The theorem after `EasyCryptTransform` (the equivalence setup).
    pub theorem_ec: &'a Theorem<'a>,
    pub project: &'a P,
    pub exported: &'a ExportedTheorem,
    /// The equivalence, or for a side-invariant job its report ([`JobKind::SideInvariants`]).
    pub eq: &'a EquivalenceReport,
    pub kind: JobKind<'a>,
    /// The theorem's output directory.
    pub out_dir: &'a Path,
    pub backend: &'a B,
    pub options: &'a TacticsOptions,
    pub swallow: &'a SwallowWatch,
    #[cfg(test)]
    pub fake: Option<super::tests::FakeEasyCrypt>,
}

impl<P, B> EquivalenceJob<'_, P, B> {
    /// The glue's name without `.ec`: `Eq_<L>_<R>`.
    fn stem(&self) -> &str {
        self.eq.proof_file.trim_end_matches(".ec")
    }

    /// The lemma file of `oracle`.
    fn oracle_file(&self, oracle: &str) -> &str {
        self.eq
            .oracle_files
            .iter()
            .find(|(o, _)| o == oracle)
            .map(|(_, file)| file.as_str())
            .expect("an exported oracle has a lemma file")
    }

    /// The exported text of `oracle`'s lemma file.
    fn oracle_source(&self, oracle: &str) -> Result<&str, CheckError> {
        self.exported_file(self.oracle_file(oracle))
    }

    /// The exported text of `file`.
    pub(super) fn exported_file(&self, file: &str) -> Result<&str, CheckError> {
        self.exported
            .files
            .get(Path::new(file))
            .map(String::as_str)
            .ok_or_else(|| CheckError::MissingFile {
                file: file.to_string(),
            })
    }
}

/// Proves the selected oracles of `job.eq`. `None`: the records say it is proved, and the job
/// skipped it (the reason is on stderr). `progress` is called for each oracle proved on this
/// thread, so only when the job has one worker.
pub(super) fn prove_equivalence<P, B>(
    job: &EquivalenceJob<'_, P, B>,
    progress: &mut dyn FnMut() -> Box<dyn ExportObserver>,
) -> Result<Option<EquivalenceTactics>, TacticsError>
where
    P: Project + Sync,
    B: SmtSolverBackend + Sync,
{
    let started = Instant::now();
    let (eq, options) = (job.eq, job.options);
    let setup = match job.kind {
        JobKind::Equivalence => equivalence_setup(job.theorem_ec, eq)?,
        JobKind::SideInvariants(c) => side_setup(job.theorem_ec, c)?,
        JobKind::PackageInvariants(p) => pkg_setup(job.theorem_ec, p)?,
    };
    if let Some(wanted) = &options.oracle {
        if !setup.oracles.iter().any(|(name, _)| name == wanted) {
            return Err(CheckError::NoSuchOracle {
                oracle: wanted.clone(),
                file: eq.proof_file.clone(),
            }
            .into());
        }
    }
    let names: Vec<String> = setup.oracles.iter().map(|(n, _)| n.clone()).collect();
    // story 35: the records decide before anything is created or truncated
    let prior = match plan_job(eq, job.out_dir, options, &names)? {
        JobPlan::Prove { prior } => prior,
        JobPlan::Skip => return Ok(None),
    };
    let dir = progress_dir(job.out_dir, job.stem());
    std::fs::create_dir_all(&dir)?;
    // what translation owns: created if missing, never read or rewritten (ADR 0006)
    let created = ensure_translation_files(job.exported, job.out_dir)?;
    if options.announce_stages {
        let wrote: Vec<String> = created.iter().map(|p| p.display().to_string()).collect();
        eprintln_above_bars(&translation_files_line(job.stem(), &wrote));
    }
    let selected = |name: &str| options.oracle.as_deref().is_none_or(|w| w == name);
    let mut rows = Vec::new();
    let mut queue = VecDeque::new();
    for (name, proc_name) in &setup.oracles {
        // proved in an earlier job: not walked, not re-sent (ADR 0006)
        let done = prior
            .as_ref()
            .and_then(|p| p.oracle(name))
            .and_then(OracleTactics::from_record);
        if let Some(done) = done {
            restore_oracle_file(job, name, proc_name, &done.script)?;
            rows.push(Row::new(name, RowState::Done(Box::new(done))));
        } else if selected(name) {
            queue.push_back(name.clone());
            rows.push(Row::new(name, RowState::Pending));
        }
    }
    let board = Mutex::new(Board {
        queue,
        rows,
        unanswered: Vec::new(),
        interrupted: None,
        ended_early: None,
        error: None,
        writes: 0,
        fixed: Vec::new(),
        page: options.oracle.is_none().then(|| dir.join("index.html")),
        report: (options.oracle.is_none()).then(|| dir.join("report.txt")),
        started,
        finished: false,
    });
    board.lock().unwrap().write(job, &dir);
    let translation = translation_line(job.exported, &created);
    let workers = options
        .jobs
        .clamp(1, board.lock().unwrap().queue.len().max(1));
    if workers == 1 {
        let shared = Rc::new(RefCell::new(Shared {
            inner: progress(),
            total: board.lock().unwrap().queue.len(),
            phase_started: false,
            items: 0,
        }));
        work(job, &setup, &board, &translation, &dir, &mut || {
            Box::new(SharedProgress(shared.clone()))
        });
        let mut shared = shared.borrow_mut();
        if shared.phase_started {
            shared.inner.on_event(&ExportEvent::PhaseFinished {
                phase: ExportPhase::Tactics,
            });
        }
    } else {
        std::thread::scope(|s| {
            for _ in 0..workers {
                s.spawn(|| {
                    work(job, &setup, &board, &translation, &dir, &mut || {
                        Box::new(NopExportObserver)
                    })
                });
            }
        });
    }
    let mut board = board.into_inner().unwrap();
    if let Some(e) = board.error.take() {
        return Err(e);
    }
    if board.interrupted.is_none() && options.stop_requested() && !board.queue.is_empty() {
        board.interrupted = Some(Interrupted::NoOracleInFlight);
    }
    board.running_done();
    // a package-invariant job: the lemmas no tree is walked for, once every oracle is done
    if let Some(pkg) = job
        .exported
        .package_invariants
        .iter()
        .find(|p| p.join_file == eq.proof_file)
        .filter(|_| matches!(job.kind, JobKind::PackageInvariants(_)))
    {
        if board.interrupted.is_none() {
            board.fixed = super::fixed::prove_fixed_lemmas(job, pkg, &dir)?;
        }
    }
    let tactics = board.tactics(job);
    board.write(job, &dir);
    Ok(Some(tactics))
}

/// Writes `oracle`'s lemma file with `script`, a proof its record holds, when the file is missing
/// (a record split from before story 68, or a file deleted by hand). An existing file is trusted.
fn restore_oracle_file<P, B>(
    job: &EquivalenceJob<'_, P, B>,
    oracle: &str,
    proc_name: &str,
    script: &str,
) -> Result<(), TacticsError> {
    let source = job.oracle_source(oracle)?;
    let path = job.out_dir.join(job.oracle_file(oracle));
    create_if_absent(&path, &with_script(source, proc_name, script))?;
    Ok(())
}

/// One worker: proves the next oracle of the board until there is none.
fn work<P, B>(
    job: &EquivalenceJob<'_, P, B>,
    setup: &EquivalenceSetup<'_>,
    board: &Mutex<Board>,
    translation: &str,
    dir: &Path,
    progress: &mut dyn FnMut() -> Box<dyn ExportObserver>,
) where
    P: Project,
    B: SmtSolverBackend,
{
    loop {
        let next = board.lock().unwrap().next(job, dir);
        let Some(oracle) = next else { return };
        let worked = prove_oracle(job, setup, &oracle, translation, progress());
        board.lock().unwrap().finished(job, dir, &oracle, worked);
    }
}

/// How proving one oracle ended.
enum Worked {
    /// Another job holds the oracle's lock: skipped.
    Held(LiveJob),
    /// Its record says it is proved: another job proved it after this one planned.
    Resumed(OracleTactics),
    /// Proved, or sealed.
    Proved(OracleRun),
}

/// An oracle this job proved (or started to).
struct OracleRun {
    /// `None`: stopped before anything was sent.
    tactics: Option<OracleTactics>,
    interrupted: Option<Interrupted>,
    unanswered: Option<Unanswered>,
    writes: usize,
}

/// Proves `oracle` in a fresh EasyCrypt: takes its lock, reads its record (an interrupted oracle
/// is resumed from it), and writes its lemma file, record, report, page and transcript.
fn prove_oracle<P, B>(
    job: &EquivalenceJob<'_, P, B>,
    setup: &EquivalenceSetup<'_>,
    oracle: &str,
    translation: &str,
    progress: Box<dyn ExportObserver>,
) -> Result<Worked, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let stem = job.stem();
    let lock_path = oracle_lock_path(job.out_dir, stem, oracle);
    let lock = match ProofLock::acquire(&lock_path, &format!("{stem}/{oracle}")) {
        Ok(lock) => lock,
        Err(LockError::Held(other)) => {
            eprintln_above_bars(&format!("skipping {oracle} of {stem}: {other}"));
            return Ok(Worked::Held(other));
        }
        Err(e) => return Err(e.into()),
    };
    // read under the lock: another job may have proved it since the plan
    let record_path = oracle_record_path(job.out_dir, &job.eq.proof_file, oracle);
    let prior = SessionRecord::read(&record_path)?;
    let entry = prior.as_ref().and_then(|r| r.oracle(oracle));
    if let Some(done) = entry.and_then(OracleTactics::from_record) {
        return Ok(Worked::Resumed(done));
    }
    let prior = prior.filter(|r| {
        r.oracle(oracle)
            .is_some_and(|e| e.status != OracleStatus::Pending)
    });
    let dir = progress_dir(job.out_dir, stem).join(oracle);
    std::fs::create_dir_all(&dir)?;
    let file = job.oracle_file(oracle);
    let source = job.oracle_source(oracle)?;
    let proof_path = job.out_dir.join(file);
    if job.options.force && prior.is_none() {
        // restarted from the skeleton
        write_atomically(&proof_path, &dir, source)?;
    } else {
        create_if_absent(&proof_path, source)?;
    }
    let transcript_path = dir.join("ec-transcript.jsonl");
    let live = LiveHandle::new(LiveConfig {
        theorem: job.theorem.name.clone(),
        page: Some(dir.join("index.html")),
        transcript: transcript_path.clone(),
        translation: translation.to_string(),
        progress,
    });
    let procs: Vec<(String, String)> = setup
        .oracles
        .iter()
        .filter(|(n, _)| n == oracle)
        .cloned()
        .collect();
    let report_file = format!("progress/{stem}/{oracle}/report.txt");
    let proof = ProofFile {
        theorem: &job.theorem.name,
        source,
        prior: prior.as_ref(),
        procs: &procs,
        out_dir: job.out_dir,
        progress_dir: &dir,
        record_path,
        started: Instant::now(),
        tactics: EquivalenceTactics {
            composition: job.kind.composition(),
            package: job.kind.package(),
            fixed: Vec::new(),
            proofstep: job.eq.proofstep,
            proof_file: file.to_string(),
            left: job.eq.left_name.clone(),
            right: job.eq.right_name.clone(),
            oracles: Vec::new(),
            elapsed: Duration::ZERO,
            report_file,
            interrupted: None,
            ended_early: None,
            unanswered: Vec::new(),
            writes: 0,
        },
        writes: std::cell::Cell::new(0),
    };
    let result = walk_oracle(job, setup, oracle, proof, &transcript_path, &live);
    // the last write always happens: the page on disk matches the end state
    match &result {
        Ok(run) => match &run.interrupted {
            Some(at) => live.interrupted(&at.to_string()),
            None => live.finish(),
        },
        Err(e) => live.fail(&e.to_string()),
    }
    drop(lock);
    result.map(Worked::Proved)
}

/// The walk of one oracle in its own EasyCrypt: open the lemma, prove it ([`tactics_for_oracle`]),
/// write it.
fn walk_oracle<P, B>(
    job: &EquivalenceJob<'_, P, B>,
    setup: &EquivalenceSetup<'_>,
    oracle: &str,
    mut proof: ProofFile<'_>,
    transcript_path: &Path,
    live: &LiveHandle,
) -> Result<OracleRun, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let options = job.options;
    let file = proof.tactics.proof_file.clone();
    live.equivalence_started(
        &file,
        job.eq.proofstep,
        &job.eq.left_name,
        &job.eq.right_name,
        &[oracle.to_string()],
    );
    let transcript = File::create(transcript_path)?;
    let session_setup = SessionSetup {
        out_dir: job.out_dir,
        transcript_path,
        options,
        file: &file,
        live,
        swallow: job.swallow,
        #[cfg(test)]
        fake: job.fake.as_ref(),
    };
    let mut run = OracleRun {
        tactics: None,
        interrupted: None,
        unanswered: None,
        writes: 0,
    };
    'run: {
        if options.stop_requested() {
            run.interrupted = Some(Interrupted::NoOracleInFlight);
            break 'run;
        }
        live.activity("starting EasyCrypt and opening the oracle lemma");
        let mut session = session_setup.start(Some(&transcript))?;
        if !open_lemma(&mut session, &file, proof.source, options)? {
            run.interrupted = Some(Interrupted::NoOracleInFlight);
            break 'run;
        }
        let end = tactics_for_oracle(
            &mut session,
            job.project,
            job.theorem,
            job.eq,
            job.kind,
            setup,
            oracle,
            job.backend,
            options,
            live,
            &mut proof,
        )?;
        let result = match end {
            OracleEnd::Done(result) => Some(result),
            OracleEnd::Stopped { sealed, at } => {
                run.interrupted = Some(at);
                sealed
            }
            OracleEnd::Unanswered { sealed, unanswered } => {
                // the oracle is sealed; its EasyCrypt is given up (`Drop` kills it)
                live.unanswered(&unanswered);
                proof.tactics.unanswered.push(unanswered.clone());
                run.unanswered = Some(unanswered);
                Some(sealed)
            }
        };
        if let Some(mut result) = result {
            result.transcript = Some(transcript_path.to_path_buf());
            proof.tactics.oracles.push(result);
            proof.write(None)?;
            live.oracle_finished(proof.tactics.oracles.last().expect("just pushed"));
        }
    }
    proof.tactics.interrupted = run.interrupted.clone();
    let tactics = proof.write(None)?;
    live.equivalence_finished(&tactics);
    run.writes = tactics.writes;
    run.tactics = tactics.oracles.into_iter().next();
    Ok(run)
}

/// What the job knows of its oracles while the workers run; behind a lock.
struct Board {
    /// The oracles no worker has taken yet, in oracle order.
    queue: VecDeque<String>,
    /// One for each oracle the job shows, in oracle order.
    rows: Vec<Row>,
    unanswered: Vec<Unanswered>,
    /// The first stop, or where the job ended early.
    interrupted: Option<Interrupted>,
    ended_early: Option<String>,
    /// The first error of a worker: no oracle is started after it, and the job returns it.
    error: Option<TacticsError>,
    writes: usize,
    /// The frame and start lemmas of a package-invariant job, once checked (story 76).
    fixed: Vec<super::FixedLemma>,
    /// The equivalence's page and report; `None` with `--oracle`, whose job writes only the
    /// oracle's own files.
    page: Option<PathBuf>,
    /// `None` with `--oracle`: the oracle's own report is the report.
    report: Option<PathBuf>,
    started: Instant,
    /// The workers are gone: the page has no refresh tag.
    finished: bool,
}

struct Row {
    oracle: String,
    state: RowState,
}

impl Row {
    fn new(oracle: &str, state: RowState) -> Row {
        Row {
            oracle: oracle.to_string(),
            state,
        }
    }
}

enum RowState {
    Pending,
    Running,
    /// Proved or sealed by this job, or read back from its record.
    Done(Box<OracleTactics>),
    /// Another job holds its lock.
    Held(LiveJob),
}

impl Board {
    /// The next oracle to prove, marked running; `None` once the queue is empty, the run is
    /// stopped, the job ended early or a worker failed.
    fn next<P, B>(&mut self, job: &EquivalenceJob<'_, P, B>, dir: &Path) -> Option<String> {
        if self.error.is_some() || self.interrupted.is_some() || job.options.stop_requested() {
            return None;
        }
        let oracle = self.queue.pop_front()?;
        self.set(&oracle, RowState::Running);
        self.write(job, dir);
        Some(oracle)
    }

    fn set(&mut self, oracle: &str, state: RowState) {
        if let Some(row) = self.rows.iter_mut().find(|r| r.oracle == oracle) {
            row.state = state;
        }
    }

    /// Takes in how `oracle` ended. An unanswered interrupt past [`MAX_RESPAWNS`] ends the job.
    fn finished<P, B>(
        &mut self,
        job: &EquivalenceJob<'_, P, B>,
        dir: &Path,
        oracle: &str,
        worked: Result<Worked, TacticsError>,
    ) {
        let state = match worked {
            Err(e) => {
                self.error.get_or_insert(e);
                RowState::Pending
            }
            Ok(Worked::Held(other)) => RowState::Held(other),
            Ok(Worked::Resumed(done)) => RowState::Done(Box::new(done)),
            Ok(Worked::Proved(run)) => {
                self.writes += run.writes;
                if let Some(at) = run.interrupted {
                    self.interrupted.get_or_insert(at);
                }
                if let Some(mut u) = run.unanswered {
                    if self.unanswered.len() == MAX_RESPAWNS {
                        u.ended_job = true;
                        self.ended_early = Some(format!(
                            "EasyCrypt left {} interrupts unanswered, and a proof job respawns it \
                             at most {MAX_RESPAWNS} times",
                            MAX_RESPAWNS + 1
                        ));
                        self.interrupted
                            .get_or_insert(sealed_at(&u, run.tactics.as_ref()));
                    }
                    self.unanswered.push(u);
                }
                match run.tactics {
                    Some(t) => RowState::Done(Box::new(t)),
                    None => RowState::Pending,
                }
            }
        };
        self.set(oracle, state);
        self.write(job, dir);
    }

    /// The workers are gone: rows still running were stopped before they began.
    fn running_done(&mut self) {
        self.finished = true;
        for row in &mut self.rows {
            if matches!(row.state, RowState::Running) {
                row.state = RowState::Pending;
            }
        }
    }

    /// The equivalence as far as it got: its oracles in oracle order.
    fn tactics<P, B>(&self, job: &EquivalenceJob<'_, P, B>) -> EquivalenceTactics {
        let stem = job.stem();
        let report_file = match (&self.report, &job.options.oracle) {
            (None, Some(oracle)) => format!("progress/{stem}/{oracle}/report.txt"),
            _ => format!("progress/{stem}/report.txt"),
        };
        EquivalenceTactics {
            composition: job.kind.composition(),
            package: job.kind.package(),
            fixed: self.fixed.clone(),
            proofstep: job.eq.proofstep,
            proof_file: job.eq.proof_file.clone(),
            left: job.eq.left_name.clone(),
            right: job.eq.right_name.clone(),
            oracles: self
                .rows
                .iter()
                .filter_map(|r| match &r.state {
                    RowState::Done(t) => Some((**t).clone()),
                    _ => None,
                })
                .collect(),
            elapsed: self.started.elapsed(),
            report_file,
            interrupted: self.interrupted.clone(),
            ended_early: self.ended_early.clone(),
            unanswered: self.unanswered.clone(),
            writes: self.writes,
        }
    }

    /// Writes the equivalence's page and report. A failed write is ignored: the oracles' own
    /// files are the results; these join them.
    fn write<P, B>(&self, job: &EquivalenceJob<'_, P, B>, dir: &Path) {
        if let Some(page) = &self.page {
            let _ = write_atomically(page, dir, &self.page_html(job, !self.finished));
        }
        if let Some(report) = &self.report {
            let _ = write_atomically(report, dir, &self.tactics(job).render());
        }
    }

    /// The equivalence's page: one row for each oracle, with a link to its own page.
    fn page_html<P, B>(&self, job: &EquivalenceJob<'_, P, B>, running: bool) -> String {
        let eq = job.eq;
        let mut out = String::from("<!doctype html>\n<html><head><meta charset=\"utf-8\">\n");
        if running {
            out.push_str("<meta http-equiv=\"refresh\" content=\"2\">\n");
        }
        let _ = writeln!(
            out,
            "<title>{stem}</title>\n<style>body{{font-family:sans-serif}}td,th{{padding:2px 12px;text-align:left}}</style>\n</head><body>\n<h1>{stem}</h1>\n<p>proofstep {}: {} ~ {}</p>\n<table>\n<tr><th>oracle</th><th>state</th></tr>",
            eq.proofstep,
            esc(&eq.left_name),
            esc(&eq.right_name),
            stem = esc(job.stem()),
        );
        for row in &self.rows {
            let state = match &row.state {
                RowState::Pending => "pending".to_string(),
                RowState::Running => "running".to_string(),
                RowState::Held(other) => format!("skipped: {other}"),
                RowState::Done(t) if t.resumed => "proved earlier (from its record)".to_string(),
                RowState::Done(t) => match &t.problem {
                    Some(problem) => format!("no tactics: {problem}"),
                    None => format!("done, {} admits", t.stats.admits.len()),
                },
            };
            let name = esc(&row.oracle);
            let _ = writeln!(
                out,
                "<tr><td><a href=\"{name}/index.html\">{name}</a></td><td>{}</td></tr>",
                esc(&state)
            );
        }
        out.push_str("</table>\n");
        if let Some(why) = &self.ended_early {
            let _ = writeln!(out, "<p>ended early: {}</p>", esc(why));
        } else if let Some(at) = &self.interrupted {
            let _ = writeln!(out, "<p>interrupted: {}</p>", esc(&at.to_string()));
        }
        out.push_str("</body></html>\n");
        out
    }
}

/// The progress observer of a job with one worker (`--jobs 1`): the live page of each oracle
/// reports to it, and it reports one `tactics` phase with one item for each oracle, as a job
/// did before story 68.
struct SharedProgress(Rc<RefCell<Shared>>);

struct Shared {
    inner: Box<dyn ExportObserver>,
    /// The oracles the job proves.
    total: usize,
    phase_started: bool,
    items: usize,
}

impl ExportObserver for SharedProgress {
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        let mut s = self.0.borrow_mut();
        match *event {
            ExportEvent::PhaseStarted { phase, .. } => {
                if !s.phase_started {
                    s.phase_started = true;
                    let total_items = s.total;
                    s.inner
                        .on_event(&ExportEvent::PhaseStarted { phase, total_items });
                }
            }
            ExportEvent::ItemStarted { phase, name, .. } => {
                s.items += 1;
                let index = s.items;
                s.inner
                    .on_event(&ExportEvent::ItemStarted { phase, name, index });
            }
            // the job ends the phase, after its last oracle
            ExportEvent::PhaseFinished { .. } => {}
            _ => s.inner.on_event(event),
        }
    }

    fn lockstep_observer(&mut self) -> Box<dyn DebugObserver> {
        self.0.borrow_mut().inner.lockstep_observer()
    }
}

/// Where the job ended on `u`: the sealed oracle and its `interrupted` admits.
fn sealed_at(u: &Unanswered, sealed: Option<&OracleTactics>) -> Interrupted {
    Interrupted::Sealed {
        oracle: u.oracle.clone(),
        admits: sealed.map_or(0, |t| {
            t.stats
                .admits
                .iter()
                .filter(|a| a.reason == super::AdmitReason::Interrupted)
                .count()
        }),
        node: u.node.clone(),
    }
}

fn esc(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}
