// SPDX-License-Identifier: MIT OR Apache-2.0

//! One-sided execution (`docs/stories/symbolic-execution/25-one-sided-execution.md`, ADR 0014):
//! the **side tree** of one oracle of one composition.
//!
//! It is the one-sided part of lockstep execution ([`crate::debug::lockstep`]). The side
//! consumes its straight-line code up to its next decision point, and then:
//!
//! 1. **Branch**: with `A` the base frame and `pc` the path condition, a condition `c` with
//!    `A ∧ pc ∧ ¬c` or `A ∧ pc ∧ c` unsatisfiable is **determined** ([`NodeKind::Determined`]):
//!    the side takes the one possible child. If both are unsatisfiable, the node is
//!    [`NodeKind::Unreachable`]. Otherwise both arms are explored ([`NodeKind::Split`]). Only
//!    `unsat` prunes. An exit guard is marked on the node's view, as in lockstep execution.
//! 2. **Sampling**: a draw with no pairing ([`NodeKind::SamplingIndependent`]), one child.
//! 3. **Terminal** ([`NodeKind::TerminalPair`], with no right side): after the vacuity check,
//!    each claim is checked with [`check_claim`]. Every claim depends on `left-no-abort`, so a
//!    terminal that aborts has nothing to check: each claim is `unreachable` there, and no
//!    solver call is made.
//!
//! The output is a [`LockstepOutcome`], so the side tree has the JSON shape of the joint tree:
//! each node's `right` is [`SideView::absent`] and each terminal's `right` is
//! [`PairSide::absent`]. The joint-tree viewer shows it with one column. Terminals are numbered
//! `J<n>` in depth-first order (then before else), as joint paths are.

use std::ops::ControlFlow;
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::debug::claims::{check_claim, ClaimQuery, PairAborts};
use crate::debug::driver::{ClaimVerdict, DebugError, StopReason, Verdict};
use crate::debug::exec::Side;
use crate::debug::exec::{Head, SideExec, SidePos, Terminal};
use crate::debug::layout::Layout;
use crate::debug::lockstep::{
    pair_side, side_view_at, Answer, ChildOutcome, JointChild, JointNode, JointTree,
    LockstepOutcome, LockstepSide, NodeKind, PairRecord, PairSide, SideStep, SideView,
    SolverAnswer,
};
use crate::util::smtsolver::{SmtSolver, SmtSolverResponse};
use crate::writers::smt::exprs::{SmtAssert, SmtExpr, SmtNot};

pub struct SideOptions<'a> {
    /// Stop after this many terminals.
    pub max_paths: Option<usize>,
    /// `Ctrl-C`: checked at every node.
    pub stop: Option<&'a AtomicBool>,
    /// Where models of failing checks go (`models/<J>.<claim>.smt2`).
    pub out_dir: &'a Path,
    pub layout: Layout,
}

/// Run one-sided execution of `side`, checking `claims` at each terminal.
///
/// `solver` must already hold the base frame at level 0 (declarations, definitions, the
/// side's invariants on the old state). It is returned to that state, whatever the outcome.
pub fn run_side<S: SmtSolver>(
    solver: &mut S,
    side: LockstepSide<'_>,
    claims: &[ClaimQuery],
    opts: &SideOptions<'_>,
) -> Result<LockstepOutcome, DebugError> {
    let mut exec = SideExec::new(side.inlined, side.game_inst, side.sample_info, Side::Left)?;
    let (pos, head) = exec.start();
    let mut walk = Walk {
        solver,
        claims,
        opts,
        exec,
        inlined: side.inlined,
        out: LockstepOutcome {
            tree: JointTree::default(),
            pairs: Vec::new(),
            stuck: Vec::new(),
            stop_reason: StopReason::Completed,
        },
    };
    let _ = walk.explore(pos, head)?;
    Ok(walk.out)
}

/// A child a node planned: the step into it and the state it starts from.
struct Planned<'a> {
    step: SideStep,
    pos: SidePos<'a>,
    head: Head<'a>,
}

struct Walk<'r, 'a, S: SmtSolver> {
    solver: &'r mut S,
    claims: &'r [ClaimQuery],
    opts: &'r SideOptions<'r>,
    exec: SideExec<'a>,
    inlined: &'a crate::debug::ir::InlinedOracle,
    out: LockstepOutcome,
}

impl<'a, S: SmtSolver> Walk<'_, 'a, S> {
    /// Explore the node at `pos`/`head` in a solver scope of its own.
    fn explore(&mut self, pos: SidePos<'a>, head: Head<'a>) -> Result<ControlFlow<()>, DebugError> {
        if self.opts.stop.is_some_and(|s| s.load(Ordering::Relaxed)) {
            self.out.stop_reason = StopReason::Interrupted;
            return Ok(ControlFlow::Break(()));
        }
        self.solver.push()?;
        let result = self.explore_scoped(pos, head);
        let popped = self.solver.pop();
        let flow = result?;
        popped?;
        Ok(flow)
    }

    fn explore_scoped(
        &mut self,
        mut pos: SidePos<'a>,
        head: Head<'a>,
    ) -> Result<ControlFlow<()>, DebugError> {
        let (decls, constraints) = pos.pending();
        for e in decls.iter().chain(constraints) {
            self.solver.write_smt(e.clone())?;
        }
        pos.mark_reported();
        let view = side_view_at(&mut pos, &head);
        let index = self.out.tree.nodes.len();
        let mut answers = Vec::new();

        let (kind, children) = match &head {
            Head::Terminal(terminal) => {
                if let Some(limit) = self.opts.max_paths {
                    if self.out.pairs.len() >= limit {
                        self.out.stop_reason = StopReason::MaxPaths { limit };
                        return Ok(ControlFlow::Break(()));
                    }
                }
                let record = self.terminal(&pos, terminal, index)?;
                self.push_node(index, NodeKind::TerminalPair, view, answers, &[]);
                self.out.tree.nodes[index].pair = Some(record.id.clone());
                self.out.pairs.push(record);
                return Ok(ControlFlow::Continue(()));
            }
            Head::Sample(sample) => {
                let mut child_pos = pos.clone();
                let child_head = self.exec.take_sample(&mut child_pos, sample);
                let step = SideStep {
                    label: sample.label,
                    decision: "draw".to_string(),
                };
                (
                    NodeKind::SamplingIndependent,
                    vec![Planned {
                        step,
                        pos: child_pos,
                        head: child_head,
                    }],
                )
            }
            Head::Branch(branch) => {
                let (first, second) = branch.decisions();
                let mut possible = Vec::new();
                for (decision, cond) in [
                    (first, branch.cond.clone()),
                    (second, SmtNot(branch.cond.clone()).into()),
                ] {
                    let query = format!("{}-possible", decision.as_str());
                    if self.ask(&mut answers, query, cond)? != Answer::Unsat {
                        possible.push(decision);
                    }
                }
                let kind = match possible.len() {
                    0 => NodeKind::Unreachable,
                    1 => NodeKind::Determined,
                    _ => NodeKind::Split,
                };
                let children = possible
                    .into_iter()
                    .map(|decision| {
                        let mut child_pos = pos.clone();
                        let child_head = self.exec.take_branch(&mut child_pos, branch, decision);
                        Planned {
                            step: SideStep {
                                label: branch.label,
                                decision: decision.as_str().to_string(),
                            },
                            pos: child_pos,
                            head: child_head,
                        }
                    })
                    .collect();
                (kind, children)
            }
        };

        let steps: Vec<SideStep> = children.iter().map(|c| c.step.clone()).collect();
        self.push_node(index, kind, view, answers, &steps);
        for (i, child) in children.into_iter().enumerate() {
            let child_node = self.out.tree.nodes.len();
            self.out.tree.nodes[index].children[i].outcome =
                ChildOutcome::Explored { node: child_node };
            let flow = self.explore(child.pos, child.head)?;
            if self.out.tree.nodes.len() == child_node {
                self.out.tree.nodes[index].children[i].outcome = ChildOutcome::NotExplored;
            }
            if flow.is_break() {
                return Ok(ControlFlow::Break(()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }

    fn push_node(
        &mut self,
        index: usize,
        kind: NodeKind,
        view: SideView,
        answers: Vec<SolverAnswer>,
        steps: &[SideStep],
    ) {
        self.out.tree.nodes.push(JointNode {
            index,
            kind,
            left: view,
            right: SideView::absent(),
            answers,
            children: steps
                .iter()
                .map(|step| JointChild {
                    left: Some(step.clone()),
                    right: None,
                    outcome: ChildOutcome::NotExplored,
                })
                .collect(),
            pair: None,
            stuck: None,
        });
    }

    /// Is `A ∧ pc ∧ extra` satisfiable? The answer is recorded.
    fn ask(
        &mut self,
        answers: &mut Vec<SolverAnswer>,
        query: String,
        extra: SmtExpr,
    ) -> Result<Answer, DebugError> {
        self.solver.push()?;
        let response = self
            .solver
            .write_smt(SmtAssert(extra))
            .and_then(|()| self.solver.check_sat());
        self.solver.pop()?;
        let answer = Answer::from(response?);
        answers.push(SolverAnswer { query, answer });
        Ok(answer)
    }

    /// The vacuity check, then each claim, at the terminal node `node`.
    fn terminal(
        &mut self,
        pos: &SidePos<'a>,
        terminal: &Terminal,
        node: usize,
    ) -> Result<PairRecord, DebugError> {
        let path = self.exec.terminal_path(pos, terminal);
        let id = format!("J{}", self.out.pairs.len() + 1);
        self.solver.push()?;
        let claims = self.check(&id, &path);
        self.solver.pop()?;
        Ok(PairRecord {
            id,
            node,
            left: pair_side(self.inlined, &path),
            right: PairSide::absent(),
            claims: claims?,
        })
    }

    fn check(
        &mut self,
        id: &str,
        path: &crate::debug::exec::TerminalPath,
    ) -> Result<Vec<ClaimVerdict>, DebugError> {
        for e in path.decls[path.reported_decls..]
            .iter()
            .chain(&path.constraints[path.reported_constraints..])
        {
            self.solver.write_smt(e.clone())?;
        }
        self.solver.write_smt(path.return_constraint.clone())?;
        if matches!(self.solver.check_sat()?, SmtSolverResponse::Unsat) {
            return Ok(self
                .claims
                .iter()
                .map(|claim| ClaimVerdict::of(&claim.name, Verdict::pair_infeasible()))
                .collect());
        }
        let aborts = PairAborts {
            left: path.terminal.is_abort(),
            right: false,
        };
        let mut queries = 0;
        self.claims
            .iter()
            .map(|claim| {
                check_claim(
                    &mut *self.solver,
                    claim,
                    aborts,
                    self.opts.out_dir,
                    self.opts.layout,
                    &format!("{id}.{}", claim.name),
                    &mut queries,
                )
            })
            .collect()
    }
}
