// SPDX-License-Identifier: MIT OR Apache-2.0

//! The claims of an oracle, checked at a terminal pair (story 19).
//!
//! An **all-claim run** explores an oracle once and asks every claim of its obligation set
//! about each terminal pair. The pair's path conditions and what every claim shares are on the
//! solver stack already; a claim adds only its **own declared dependencies** (`no-abort`,
//! project lemmas, …) and its negated goal, in one `push` / `check-sat` / `pop`.
//!
//! Verdicts are meant to be comparable to `domino prove`'s, which grants each claim its own
//! dependencies, so the claim's dependencies are never dropped. What moving them from the base
//! frame to the terminal pair adds is *scope* for [`Verdict::Unreachable`]: the pair may be
//! infeasible ([`Unreachability::PairInfeasible`]), or feasible with this claim's premise
//! false on it ([`Unreachability::DependencyFalse`]).

use std::path::Path;

use serde_derive::Serialize;

use crate::debug::driver::{
    write_model, ClaimVerdict, DebugError, PartVerdict, Unreachability, Verdict,
};
use crate::debug::layout::Layout;
use crate::gamehops::equivalence::Equivalence;
use crate::theorem::{Claim, ClaimType};
use crate::util::smtsolver::{SmtSolver, SmtSolverResponse};
use crate::writers::smt::contexts::EquivalenceContext;
use crate::writers::smt::exprs::SmtExpr;

/// A claim of the oracle's obligation set, ready to be checked at a terminal pair.
pub struct ClaimQuery {
    pub name: String,
    /// The claim's own declared dependencies, by name, with the assertion each one is —
    /// what a single-claim run has in its base frame.
    pub dependencies: Vec<(String, SmtExpr)>,
    /// `(assert (not <goal>))`.
    pub negated: SmtExpr,
    /// The named parts of the goal, each negated; empty for every claim but `invariant`.
    /// [`check_claim`] checks them only where the claim is not verified.
    pub parts: Vec<(String, SmtExpr)>,
}

/// The name of the check that one state relation is on the Domino listing.
pub fn state_relation_part(relation: &str) -> String {
    format!("state-relation {relation}")
}

/// A claim of `ty` called `name` with no dependencies: its goal is the goal of that claim
/// alone.
pub(crate) fn no_dependency_claim(name: &str, ty: ClaimType) -> Claim {
    Claim {
        name: name.to_string(),
        ty,
        dependencies: Vec::new(),
        admitted: false,
    }
}

/// The negated goal of each state relation except `invariant` on the new states, each named
/// by `name_of`: the parts of the `invariant` claim.
pub(crate) fn state_relation_parts(
    eqctx: &EquivalenceContext<'_>,
    oracle: &str,
    name_of: impl Fn(&str) -> String,
) -> Vec<(String, SmtExpr)> {
    eqctx
        .state_relation_names()
        .into_iter()
        .filter(|name| name != "invariant")
        .map(|name| {
            let negated = eqctx
                .emit_claim_goal_negated(&no_dependency_claim(&name, ClaimType::Invariant), oracle);
            (name_of(&name), negated)
        })
        .collect()
}

/// One check as the solver gets it at a terminal pair, rendered: the claim's dependencies, its
/// negated goal, then its parts. Both pages render the `Claim assertion` and `Verdicts`
/// sections from this.
#[derive(Debug, Clone, Serialize)]
pub struct ClaimGoalView {
    pub claim: String,
    /// The claim's own dependencies, as the assertions made at the terminal pair.
    pub dependencies: Vec<String>,
    pub smt: String,
    pub parts: Vec<PartGoalView>,
}

#[derive(Debug, Clone, Serialize)]
pub struct PartGoalView {
    pub name: String,
    pub smt: String,
}

impl ClaimQuery {
    pub fn of(eqctx: &EquivalenceContext<'_>, claim: &Claim, oracle: &str) -> Self {
        let assumptions = eqctx.emit_claim_own_assumptions(claim, oracle);
        debug_assert_eq!(assumptions.len(), claim.dependencies().len());
        Self {
            name: claim.name().to_string(),
            dependencies: claim
                .dependencies()
                .iter()
                .cloned()
                .zip(assumptions)
                .collect(),
            negated: eqctx.emit_claim_goal_negated(claim, oracle),
            parts: if claim.name() == "invariant" {
                state_relation_parts(eqctx, oracle, state_relation_part)
            } else {
                Vec::new()
            },
        }
    }

    /// The check rendered for the pages.
    pub fn view(&self) -> ClaimGoalView {
        ClaimGoalView {
            claim: self.name.clone(),
            dependencies: self.dependencies.iter().map(|(_, a)| a.to_string()).collect(),
            smt: self.negated.to_string(),
            parts: self
                .parts
                .iter()
                .map(|(name, negated)| PartGoalView {
                    name: name.clone(),
                    smt: negated.to_string(),
                })
                .collect(),
        }
    }

    /// A claim with no dependencies and an explicit negated goal (the EasyCrypt listing's
    /// `equal-output`, which is a grouping of two claims).
    pub fn without_dependencies(name: &str, negated: SmtExpr) -> Self {
        Self {
            name: name.to_string(),
            dependencies: Vec::new(),
            negated,
            parts: Vec::new(),
        }
    }
}

/// The full obligation set of `oracle`: what `domino prove` discharges. `equal-aborts`,
/// `same-output` and `invariant` come first, then the rest of the proof tree in declaration
/// order, then the generated package/game invariant claims — so a report reads like `prove`'s.
pub(crate) fn obligations(
    eqctx: &EquivalenceContext<'_>,
    eq: &Equivalence,
    oracle: &str,
) -> Vec<Claim> {
    const FIRST: [&str; 3] = ["equal-aborts", "same-output", "invariant"];
    let mut ranked: Vec<(usize, Claim)> = eq
        .proof_tree_by_oracle_name(oracle)
        .into_iter()
        .map(|claim| {
            let rank = FIRST
                .iter()
                .position(|name| *name == claim.name())
                .unwrap_or(FIRST.len());
            (rank, claim)
        })
        .collect();
    ranked.extend(
        eqctx
            .generate_game_or_package_invariant_claims()
            .into_iter()
            .map(|claim| (FIRST.len() + 1, claim)),
    );
    ranked.sort_by_key(|(rank, _)| *rank);
    ranked.into_iter().map(|(_, claim)| claim).collect()
}

/// Which side(s) of a terminal pair abort. The driver knows this syntactically.
#[derive(Debug, Clone, Copy)]
pub struct PairAborts {
    pub left: bool,
    pub right: bool,
}

/// Is the dependency `name` false on a pair with these aborts — decided **without the solver**?
/// `build_no_abort` is `left_no_abort ∧ right_no_abort` over the two return values' abort
/// constructors, so for the dependencies every default and generated claim uses the answer is
/// read off the terminals. `None`: not one of these, only the solver can tell.
fn false_by_terminals(name: &str, aborts: PairAborts) -> Option<bool> {
    match name {
        "no-abort" => Some(aborts.left || aborts.right),
        "left-no-abort" => Some(aborts.left),
        "right-no-abort" => Some(aborts.right),
        "equal-aborts" => Some(aborts.left != aborts.right),
        _ => None,
    }
}

/// Check `claim` on the pair whose path conditions are on the solver stack (and found
/// satisfiable by the pair's vacuity check). The stack is as it was on return.
///
/// 1. A dependency false on the terminals settles it: `Unreachable { DependencyFalse }`, no
///    solver call.
/// 2. Otherwise `push`, assert the claim's dependencies, `push`, assert the negated goal,
///    `check-sat`. `sat` fails the claim, `unknown` is inconclusive.
/// 3. `unsat` verifies the claim *unless the dependencies alone are unsatisfiable here*: a
///    dependency that is a project lemma or a user relation may be false on a pair whose
///    terminals do not say so. That is one more `check-sat`, asked only after an `unsat`
///    (a `sat` goal check already proves the dependencies satisfiable), and only for a claim
///    with such a dependency.
///
/// 4. Where the claim fails or is inconclusive, each of its parts is checked inside the same
///    dependency frame ([`check_parts`]).
///
/// `model_id` names the model file of a failing check under `models/`; `queries` counts the
/// `check-sat` calls made.
pub(crate) fn check_claim<S: SmtSolver>(
    solver: &mut S,
    claim: &ClaimQuery,
    aborts: PairAborts,
    out_dir: &Path,
    layout: Layout,
    model_id: &str,
    queries: &mut usize,
) -> Result<ClaimVerdict, DebugError> {
    if let Some((name, _)) = claim
        .dependencies
        .iter()
        .find(|(name, _)| false_by_terminals(name, aborts) == Some(true))
    {
        return Ok(ClaimVerdict::of(&claim.name, dependency_false(name.clone())));
    }

    let has_dependencies = !claim.dependencies.is_empty();
    if has_dependencies {
        solver.push()?;
        for (_, assertion) in &claim.dependencies {
            solver.write_smt(assertion.clone())?;
        }
    }
    let (verdict, model) = check_negated(solver, &claim.negated, out_dir, layout, model_id, queries)?;
    let parts = if verdict.is_failure() {
        check_parts(solver, &claim.parts, out_dir, layout, model_id, queries)?
    } else {
        Vec::new()
    };
    let checked = ClaimVerdict {
        claim: claim.name.clone(),
        verdict,
        model,
        parts,
    };
    if !has_dependencies {
        return Ok(checked);
    }

    let by_solver: Vec<&(String, SmtExpr)> = claim
        .dependencies
        .iter()
        .filter(|(name, _)| false_by_terminals(name, aborts).is_none())
        .collect();
    let dependencies_unsat = matches!(checked.verdict, Verdict::Verified)
        && !by_solver.is_empty()
        && {
            *queries += 1;
            matches!(solver.check_sat()?, SmtSolverResponse::Unsat)
        };
    solver.pop()?;
    if dependencies_unsat {
        let dependency = dependency_false_here(solver, &by_solver, queries)?;
        return Ok(ClaimVerdict::of(&claim.name, dependency_false(dependency)));
    }
    Ok(checked)
}

fn dependency_false(dependency: String) -> Verdict {
    Verdict::Unreachable {
        reason: Unreachability::DependencyFalse { dependency },
    }
}

/// `push`, assert `negated`, `check-sat`, `pop`, and classify the answer: `unsat` verifies,
/// `sat` fails, `unknown` is inconclusive. The model of a failing check goes to
/// `models/<model_id>.smt2`; its text comes back with the verdict.
fn check_negated<S: SmtSolver>(
    solver: &mut S,
    negated: &SmtExpr,
    out_dir: &Path,
    layout: Layout,
    model_id: &str,
    queries: &mut usize,
) -> Result<(Verdict, Option<String>), DebugError> {
    solver.push()?;
    solver.write_smt(negated.clone())?;
    *queries += 1;
    let outcome = match solver.check_sat()? {
        SmtSolverResponse::Unsat => (Verdict::Verified, None),
        SmtSolverResponse::Sat => {
            let (rel, text) = write_model(solver, out_dir, layout, model_id)?;
            (Verdict::GoalFails { model: rel }, Some(text))
        }
        SmtSolverResponse::Unknown => match write_model(solver, out_dir, layout, model_id) {
            Ok((rel, text)) => (Verdict::Inconclusive { model: Some(rel) }, Some(text)),
            Err(_) => (Verdict::Inconclusive { model: None }, None),
        },
    };
    solver.pop()?;
    Ok(outcome)
}

/// Each part of a claim on its own, on the stack as [`check_claim`] left it: the pair and the
/// claim's dependencies. The model of a failing part goes to
/// `models/<model_id>.<part>.smt2`, with each space of the part's name as `-`.
fn check_parts<S: SmtSolver>(
    solver: &mut S,
    parts: &[(String, SmtExpr)],
    out_dir: &Path,
    layout: Layout,
    model_id: &str,
    queries: &mut usize,
) -> Result<Vec<PartVerdict>, DebugError> {
    parts
        .iter()
        .map(|(name, negated)| {
            // a model file name has no space
            let part_id = format!("{model_id}.{}", name.replace(' ', "-"));
            let (verdict, model) = check_negated(solver, negated, out_dir, layout, &part_id, queries)?;
            Ok(PartVerdict {
                name: name.clone(),
                verdict,
                model,
            })
        })
        .collect()
}

/// Which dependency is false on the pair: the first of `dependencies` unsatisfiable on its own,
/// or all of them, joined, when only their conjunction is. On entry the solver holds the pair,
/// and nothing of the claim.
fn dependency_false_here<S: SmtSolver>(
    solver: &mut S,
    dependencies: &[&(String, SmtExpr)],
    queries: &mut usize,
) -> Result<String, DebugError> {
    for (name, assertion) in dependencies {
        solver.push()?;
        solver.write_smt(assertion.clone())?;
        *queries += 1;
        let unsat = matches!(solver.check_sat()?, SmtSolverResponse::Unsat);
        solver.pop()?;
        if unsat {
            return Ok(name.clone());
        }
    }
    Ok(dependencies
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<Vec<_>>()
        .join(", "))
}

/// Check every claim of `claims` on the pair, in order. `skip` says a claim is not checked on
/// this pair (`--first-failure-per-claim`, once the claim has failed), and then its parts are
/// not checked either.
pub(crate) fn check_claims<S: SmtSolver>(
    solver: &mut S,
    claims: &[ClaimQuery],
    aborts: PairAborts,
    out_dir: &Path,
    layout: Layout,
    pair_id: &str,
    queries: &mut usize,
    mut skip: impl FnMut(&str) -> bool,
) -> Result<Vec<ClaimVerdict>, DebugError> {
    let mut verdicts = Vec::with_capacity(claims.len());
    for claim in claims {
        if skip(&claim.name) {
            continue;
        }
        let model_id = format!("{pair_id}.{}", claim.name);
        verdicts.push(check_claim(solver, claim, aborts, out_dir, layout, &model_id, queries)?);
    }
    Ok(verdicts)
}

/// The one verdict that stands for a pair the claims were checked on: a failure if any claim
/// failed (`goal-fails` before `inconclusive`), otherwise `verified` if any claim verified,
/// otherwise every claim was unreachable and the first one's reason stands. The model text is
/// the standing failure's.
pub(crate) fn aggregate(checked: &[ClaimVerdict]) -> (Verdict, Option<String>) {
    let pick = |wanted: fn(&Verdict) -> bool| checked.iter().find(|c| wanted(&c.verdict));
    if let Some(c) = pick(|v| matches!(v, Verdict::GoalFails { .. })) {
        return (c.verdict.clone(), c.model.clone());
    }
    if let Some(c) = pick(|v| matches!(v, Verdict::Inconclusive { .. })) {
        return (c.verdict.clone(), c.model.clone());
    }
    if checked.iter().any(|c| matches!(c.verdict, Verdict::Verified)) {
        return (Verdict::Verified, None);
    }
    match checked.first() {
        Some(c) => (c.verdict.clone(), None),
        // every claim admitted, or skipped: nothing was asked, so nothing can fail
        None => (Verdict::Verified, None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn aborts(left: bool, right: bool) -> PairAborts {
        PairAborts { left, right }
    }

    #[test]
    fn the_four_dependencies_the_defaults_use_are_read_off_the_terminals() {
        assert_eq!(false_by_terminals("no-abort", aborts(false, false)), Some(false));
        assert_eq!(false_by_terminals("no-abort", aborts(true, false)), Some(true));
        assert_eq!(false_by_terminals("no-abort", aborts(false, true)), Some(true));
        assert_eq!(false_by_terminals("left-no-abort", aborts(true, false)), Some(true));
        assert_eq!(false_by_terminals("left-no-abort", aborts(false, true)), Some(false));
        assert_eq!(false_by_terminals("right-no-abort", aborts(true, false)), Some(false));
        assert_eq!(false_by_terminals("right-no-abort", aborts(false, true)), Some(true));
        assert_eq!(false_by_terminals("equal-aborts", aborts(true, true)), Some(false));
        assert_eq!(false_by_terminals("equal-aborts", aborts(true, false)), Some(true));
        assert_eq!(false_by_terminals("my-lemma", aborts(true, true)), None);
    }

    fn claim(name: &str, verdict: Verdict) -> ClaimVerdict {
        ClaimVerdict::of(name, verdict)
    }

    fn dependency_false(name: &str) -> Verdict {
        Verdict::Unreachable {
            reason: Unreachability::DependencyFalse {
                dependency: name.to_string(),
            },
        }
    }

    #[test]
    fn a_failing_claim_stands_for_the_pair() {
        let checked = [
            claim("a", Verdict::Verified),
            claim("b", Verdict::Inconclusive { model: None }),
            claim("c", Verdict::GoalFails { model: "m".into() }),
        ];
        assert!(matches!(aggregate(&checked).0, Verdict::GoalFails { .. }));
    }

    #[test]
    fn a_verified_claim_outranks_an_unreachable_one() {
        let checked = [claim("a", dependency_false("no-abort")), claim("b", Verdict::Verified)];
        assert!(matches!(aggregate(&checked).0, Verdict::Verified));
    }

    #[test]
    fn a_pair_where_every_claim_is_unreachable_keeps_the_reason() {
        let checked = [claim("a", dependency_false("no-abort"))];
        assert!(matches!(
            aggregate(&checked).0,
            Verdict::Unreachable {
                reason: Unreachability::DependencyFalse { .. }
            }
        ));
    }

    /// The claim checker on a live solver.
    #[cfg(feature = "cvc5-lib")]
    mod on_a_solver {
        use super::*;
        use crate::util::smtsolver::cvc5lib::Cvc5LibBackend;
        use crate::util::smtsolver::SmtSolverBackend;

        fn smt(text: &str) -> SmtExpr {
            SmtExpr::Atom(text.to_string())
        }

        /// `invariant` on the lemma `x > 5`, with the parts `x > 3` and `x > 100`.
        fn invariant_on_a_lemma() -> ClaimQuery {
            ClaimQuery {
                name: "invariant".into(),
                dependencies: vec![("my-lemma".into(), smt("(assert (> x 5))"))],
                negated: smt("(assert (not (and (> x 3) (> x 100))))"),
                parts: vec![
                    (state_relation_part("a"), smt("(assert (not (> x 3)))")),
                    (state_relation_part("b"), smt("(assert (not (> x 100)))")),
                ],
            }
        }

        fn checked_on_a_pair(claim: &ClaimQuery) -> (ClaimVerdict, usize, tempfile::TempDir) {
            let dir = tempfile::tempdir().unwrap();
            std::fs::create_dir_all(Layout::Plain.path(dir.path(), "models")).unwrap();
            let mut solver = Cvc5LibBackend::new(true, None).new_smtsolver().unwrap();
            solver.write_smt(smt("(set-logic ALL)")).unwrap();
        solver.write_smt(smt("(declare-const x Int)")).unwrap();
            let mut queries = 0;
            let checked = check_claim(
                &mut solver,
                claim,
                aborts(false, false),
                dir.path(),
                Layout::Plain,
                "1.1.invariant",
                &mut queries,
            )
            .unwrap();
            (checked, queries, dir)
        }

        /// The old lockstep loop checked each state relation after the claim's dependencies were
        /// popped, so `a` failed where the lemma is false.
        #[test]
        fn the_parts_are_checked_under_the_claims_dependencies() {
            let (checked, queries, dir) = checked_on_a_pair(&invariant_on_a_lemma());
            assert!(matches!(checked.verdict, Verdict::GoalFails { .. }));
            assert!(checked.model.is_some());
            let parts: Vec<(&str, &str)> = checked
                .parts
                .iter()
                .map(|p| (p.name.as_str(), p.verdict.slug()))
                .collect();
            assert_eq!(
                parts,
                [("state-relation a", "verified"), ("state-relation b", "goal-fails")]
            );
            assert!(checked.parts[1].model.is_some());
            assert_eq!(queries, 3);
            let model = Layout::Plain.path(dir.path(), "models/1.1.invariant.state-relation-b.smt2");
            assert!(model.exists(), "{}", model.display());
        }

        #[test]
        fn a_verified_claim_checks_no_part() {
            let claim = ClaimQuery {
                negated: smt("(assert (not (> x 3)))"),
                ..invariant_on_a_lemma()
            };
            let (checked, queries, _dir) = checked_on_a_pair(&claim);
            assert!(matches!(checked.verdict, Verdict::Verified));
            assert!(checked.parts.is_empty());
            // the goal, then the dependencies alone
            assert_eq!(queries, 2);
        }
    }
}
