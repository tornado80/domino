// SPDX-License-Identifier: MIT OR Apache-2.0

//! Sweeping the debugger over a project (story 19 §4.1, §4.7).
//!
//! `--proof`, `--proofstep`, `--oracle` and `--claim` are all optional: omitted means *all*,
//! given means *only that*, exactly as in `domino prove`. [`plan`] turns the filters into the
//! list of oracles to run; each run turns its outcome into a [`SweepEntry`], which it writes as
//! its result record (`crate::debug::index`).

use std::fmt::Write as _;
use std::path::PathBuf;
use std::time::Duration;

use crate::debug::driver::{
    equivalence_of, ClaimSummary, ClaimVerdict, DebugError, DebugRun, StopReason,
};
use crate::debug::layout::Layout;
use crate::debug::lockstep::PairRecord;
use crate::debug::lockstep_run::LockstepRun;
use crate::debug::report::format_elapsed;
use crate::project::Project;

/// One oracle of one equivalence proofstep: what a debug run is about.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Target {
    pub theorem: String,
    pub proofstep: usize,
    pub left: String,
    pub right: String,
    pub oracle: String,
}

/// A proofstep the sweep passed over because it is not an equivalence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Skipped {
    pub theorem: String,
    pub proofstep: usize,
    pub kind: &'static str,
}

impl Skipped {
    /// The one-line note the sweep prints on stderr.
    pub fn note(&self) -> String {
        format!(
            "debug: skipping {} proofstep {}: a {}, not an equivalence",
            self.theorem, self.proofstep, self.kind
        )
    }
}

#[derive(Debug, Clone, Default)]
pub struct Plan {
    pub targets: Vec<Target>,
    pub skipped: Vec<Skipped>,
}

/// The oracles the filters select, theorems in name order, proofsteps and oracles in
/// declaration order.
///
/// A proofstep that is a reduction or a conjecture is **skipped** while sweeping; naming it
/// with `proofstep` is an error, as it always was.
pub fn plan<P: Project>(
    project: &P,
    proof: Option<&str>,
    proofstep: Option<usize>,
    oracle: Option<&str>,
) -> Result<Plan, DebugError> {
    let theorem_names: Vec<String> = match proof {
        Some(name) => vec![name.to_string()],
        None => {
            let mut names: Vec<String> = project.theorems().map(String::from).collect();
            names.sort();
            names
        }
    };

    let mut plan = Plan::default();
    for name in &theorem_names {
        let theorem = project
            .get_theorem(name)
            .ok_or_else(|| DebugError::TheoremNotFound { name: name.clone() })?;
        let steps: Vec<usize> = match proofstep {
            Some(step) => vec![step],
            None => (0..theorem.game_hops.len()).collect(),
        };
        for step in steps {
            let eq = match equivalence_of(theorem, step) {
                Ok(eq) => eq,
                Err(DebugError::ProofstepNotEquivalence { kind, .. }) if proofstep.is_none() => {
                    plan.skipped.push(Skipped {
                        theorem: name.clone(),
                        proofstep: step,
                        kind,
                    });
                    continue;
                }
                Err(e) => return Err(e),
            };
            let exports: Vec<String> = theorem
                .find_game_instance(eq.left_name())
                .map(|inst| {
                    inst.game()
                        .exports
                        .iter()
                        .map(|export| export.name().to_string())
                        .collect()
                })
                .unwrap_or_default();
            if let Some(wanted) = oracle {
                if !exports.iter().any(|o| o == wanted) && proof.is_some() && proofstep.is_some()
                {
                    return Err(DebugError::OracleNotExported {
                        oracle: wanted.to_string(),
                        game_inst: eq.left_name().to_string(),
                    });
                }
            }
            for exported in exports {
                if oracle.is_some_and(|wanted| wanted != exported) {
                    continue;
                }
                plan.targets.push(Target {
                    theorem: name.clone(),
                    proofstep: step,
                    left: eq.left_name().to_string(),
                    right: eq.right_name().to_string(),
                    oracle: exported,
                });
            }
        }
    }

    if plan.targets.is_empty() {
        if let Some(wanted) = oracle {
            return Err(DebugError::OracleNotExported {
                oracle: wanted.to_string(),
                game_inst: "any selected proofstep".to_string(),
            });
        }
    }
    Ok(plan)
}

/// What one claim said over every pair (or joint path) of a run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ClaimLine {
    pub claim: String,
    pub verified: usize,
    pub unreachable: usize,
    pub goal_fails: usize,
    pub inconclusive: usize,
}

/// One pair (or joint path) a check failed on: a claim, or a part of a claim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failure {
    pub check: String,
    /// The claim this check is a part of (`invariant` for `state-relation rel_ctr`).
    pub part_of: Option<String>,
    pub pair: String,
    pub verdict: &'static str,
}

/// The outcome of one oracle's run, as the sweep's report needs it.
#[derive(Debug, Clone)]
pub struct SweepEntry {
    pub target: Target,
    /// The claim of the run, or `!all-claims!`.
    pub claim: String,
    /// `sequential` or `lockstep`.
    pub strategy: &'static str,
    /// `domino` or `easycrypt`.
    pub listing: &'static str,
    pub out_dir: PathBuf,
    /// The viewer, relative to `out_dir`.
    pub viewer: String,
    /// `pairs` for the sequential strategy, `joint paths` for lockstep.
    pub unit: &'static str,
    pub units: usize,
    pub claims: Vec<ClaimLine>,
    pub failures: Vec<Failure>,
    /// No failing or inconclusive claim, and the run finished.
    pub ok: bool,
    pub stop_reason: StopReason,
    pub elapsed: Duration,
    /// When the run finished, as `YYYY-MM-DDTHH:MM:SSZ`.
    pub finished_at: String,
}

impl SweepEntry {
    pub fn from_sequential(target: Target, run: &DebugRun) -> Self {
        let claims: Vec<ClaimLine> = if run.claim_summaries.is_empty() {
            let s = &run.summary;
            vec![ClaimLine {
                claim: run.claim.clone(),
                verified: s.verified,
                unreachable: s.unreachable,
                goal_fails: s.goal_fails,
                inconclusive: s.inconclusive,
            }]
        } else {
            run.claim_summaries.iter().map(claim_line_of).collect()
        };
        let mut failures = Vec::new();
        for lp in &run.left_paths {
            for rp in &lp.right_paths {
                if rp.claims.is_empty() && rp.verdict.is_failure() {
                    failures.push(Failure {
                        check: run.claim.clone(),
                        part_of: None,
                        pair: format!("#{}", rp.id),
                        verdict: rp.verdict.slug(),
                    });
                }
                failures.extend(claim_failures(&rp.claims, &format!("#{}", rp.id)));
            }
        }
        Self {
            target,
            claim: run.claim.clone(),
            strategy: run.strategy,
            listing: "domino",
            out_dir: PathBuf::from(&run.out_dir),
            viewer: Layout::Strategy(run.strategy).viewer(),
            unit: "pairs",
            units: run.summary.right_paths,
            claims: if run.admitted { Vec::new() } else { claims },
            failures,
            ok: run.is_ok(),
            stop_reason: run.stop_reason,
            elapsed: run.elapsed,
            finished_at: crate::debug::index::now_utc(),
        }
    }

    pub fn from_lockstep(target: Target, run: &LockstepRun) -> Self {
        let claims = run
            .summary
            .claims
            .iter()
            .map(|c| ClaimLine {
                claim: c.claim.clone(),
                verified: c.counts.verified,
                unreachable: c.counts.unreachable,
                goal_fails: c.counts.goal_fails,
                inconclusive: c.counts.inconclusive,
            })
            .collect();
        let mut failures = Vec::new();
        for pair in &run.outcome.pairs {
            failures.extend(failures_of(pair));
        }
        Self {
            target,
            claim: run.meta.claim.clone(),
            strategy: run.meta.mode,
            listing: run.meta.listing,
            out_dir: PathBuf::from(&run.meta.out_dir),
            viewer: run.meta.layout.viewer(),
            unit: "joint paths",
            units: run.summary.joint_paths,
            claims,
            failures,
            ok: run.is_ok(),
            stop_reason: run.outcome.stop_reason,
            elapsed: run.elapsed,
            finished_at: crate::debug::index::now_utc(),
        }
    }

    /// `theorem / proofstep 0 (Left == Right) / oracle`.
    pub(crate) fn label(&self) -> String {
        let t = &self.target;
        format!(
            "{} proofstep {} ({} == {}) {}",
            t.theorem, t.proofstep, t.left, t.right, t.oracle
        )
    }

    /// The claims that failed or could not be decided somewhere, and how often.
    fn failing_claims(&self) -> impl Iterator<Item = &ClaimLine> {
        self.claims
            .iter()
            .filter(|c| c.goal_fails > 0 || c.inconclusive > 0)
    }

    /// The line printed as the run finishes.
    pub fn one_line(&self) -> String {
        let status = if self.ok {
            "ok".to_string()
        } else if self.stop_reason.is_partial() {
            format!("STOPPED EARLY ({})", self.stop_reason.phrase())
        } else {
            let failing: Vec<String> = self
                .failing_claims()
                .map(|c| {
                    format!(
                        "{} ({})",
                        c.claim,
                        [(c.goal_fails, "GOAL FAILS"), (c.inconclusive, "inconclusive")]
                            .iter()
                            .filter(|(n, _)| *n > 0)
                            .map(|(n, w)| format!("{n} {w}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                })
                .collect();
            format!("FAILS: {}", failing.join("; "))
        };
        format!(
            "{}: {} {}, {} [{}]",
            self.label(),
            self.units,
            self.unit,
            status,
            format_elapsed(self.elapsed)
        )
    }
}

fn claim_line_of(c: &ClaimSummary) -> ClaimLine {
    ClaimLine {
        claim: c.claim.clone(),
        verified: c.verified,
        unreachable: c.unreachable_pair + c.unreachable_dependency,
        goal_fails: c.goal_fails,
        inconclusive: c.inconclusive,
    }
}

fn failures_of(pair: &PairRecord) -> Vec<Failure> {
    claim_failures(&pair.claims, &pair.id)
}

/// Each failing claim on `pair`, each followed by its failing parts.
fn claim_failures(claims: &[ClaimVerdict], pair: &str) -> Vec<Failure> {
    let mut failures = Vec::new();
    for c in claims.iter().filter(|c| c.verdict.is_failure()) {
        failures.push(Failure {
            check: c.claim.clone(),
            part_of: None,
            pair: pair.to_string(),
            verdict: c.verdict.slug(),
        });
        for part in c.parts.iter().filter(|p| p.verdict.is_failure()) {
            failures.push(Failure {
                check: part.name.clone(),
                part_of: Some(c.claim.clone()),
                pair: pair.to_string(),
                verdict: part.verdict.slug(),
            });
        }
    }
    failures
}

/// A run that stopped on `Ctrl-C` stops the sweep with it.
pub fn is_interrupted(entry: &SweepEntry) -> bool {
    matches!(entry.stop_reason, StopReason::Interrupted)
}

/// The project-wide table of failures: one row per (oracle, claim) that failed or could not be
/// decided, with the pairs it failed on. Empty when nothing did.
pub fn failure_table(entries: &[SweepEntry]) -> String {
    const SHOWN: usize = 6;
    let mut rows = String::new();
    for entry in entries {
        for c in entry.failing_claims() {
            let pairs: Vec<&str> = entry
                .failures
                .iter()
                .filter(|f| f.check == c.claim)
                .map(|f| f.pair.as_str())
                .collect();
            let more = pairs.len().saturating_sub(SHOWN);
            let _ = writeln!(
                rows,
                "  {}  {}: {} GOAL FAILS, {} inconclusive on {}{}{}",
                entry.label(),
                c.claim,
                c.goal_fails,
                c.inconclusive,
                entry.unit,
                if pairs.is_empty() {
                    String::new()
                } else {
                    format!(" ({}", pairs.iter().take(SHOWN).copied().collect::<Vec<_>>().join(", "))
                },
                if pairs.is_empty() {
                    String::new()
                } else if more > 0 {
                    format!(", … and {more} more)")
                } else {
                    ")".to_string()
                },
            );
        }
    }
    if rows.is_empty() {
        return rows;
    }
    format!("failures\n{rows}")
}

/// Percent-encode what a relative `href` cannot hold: `!` and spaces appear in run names
/// (`!all-claims!`) and stay legal, but `#` and `?` would cut the path short.
pub(crate) fn href_attr(path: &str) -> String {
    path.replace('#', "%23").replace('?', "%3F").replace(' ', "%20")
}

pub(crate) fn esc(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;").replace('"', "&quot;")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(ok: bool, claims: Vec<ClaimLine>, failures: Vec<Failure>) -> SweepEntry {
        SweepEntry {
            target: Target {
                theorem: "T".into(),
                proofstep: 0,
                left: "L".into(),
                right: "R".into(),
                oracle: "O".into(),
            },
            claim: "!all-claims!".into(),
            strategy: "sequential",
            listing: "domino",
            out_dir: PathBuf::from("/r/T/L-R/O/!all-claims!"),
            viewer: "sequential_viewer.html".into(),
            unit: "pairs",
            units: 4,
            claims,
            failures,
            ok,
            stop_reason: StopReason::Completed,
            elapsed: Duration::from_millis(1200),
            finished_at: "2026-10-07T12:00:00Z".into(),
        }
    }

    fn line(claim: &str, goal_fails: usize) -> ClaimLine {
        ClaimLine {
            claim: claim.into(),
            verified: 3,
            goal_fails,
            ..ClaimLine::default()
        }
    }

    #[test]
    fn a_clean_sweep_has_no_failure_table() {
        assert_eq!(failure_table(&[entry(true, vec![line("same-output", 0)], vec![])]), "");
    }

    #[test]
    fn the_failure_table_names_the_claim_and_the_pairs() {
        let e = entry(
            false,
            vec![line("same-output", 0), line("invariant", 2)],
            vec![
                Failure { check: "invariant".into(), part_of: None, pair: "#1.2".into(), verdict: "goal-fails" },
                Failure { check: "invariant".into(), part_of: None, pair: "#3.1".into(), verdict: "goal-fails" },
            ],
        );
        let table = failure_table(&[e]);
        assert!(table.starts_with("failures\n"), "{table}");
        assert!(table.contains("invariant: 2 GOAL FAILS"), "{table}");
        assert!(table.contains("#1.2, #3.1"), "{table}");
        assert!(!table.contains("same-output"), "{table}");
    }
}
