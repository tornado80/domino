// SPDX-License-Identifier: MIT OR Apache-2.0

//! The prover: walks the lockstep joint tree of one oracle depth first, alongside a live
//! EasyCrypt session, and writes down the sentences EasyCrypt accepts (story 27 §3.2-§3.6).
//!
//! **Invariant of the walk.** Every routine that handles "the front goal" leaves the session in
//! the state "that goal is closed and every other goal is as it was": what a tactic produces is
//! handled front to back, each subgoal in its own bullet. A subgoal EasyCrypt could not be
//! made to close is closed with a labelled `admit`. Every attempt runs under `undo`: the
//! session is always "all accepted sentences so far", so the script replays.
//!
//! **Tactics take positions from EasyCrypt** (ADR 0002): the joint tree supplies decisions
//! only. Counts for `sp k l` and the names of sampled variables are read from the JSON of the
//! goal in front, and subgoals are told apart by kind, never by position in a list.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::time::Duration;

use crate::debug::driver::Verdict;
use crate::debug::lockstep::{
    ChildOutcome, HeadKind, JointChild, JointNode, LockstepOutcome, NodeKind, PairRecord,
    EQUAL_OUTPUT,
};
use crate::debug::progress::eprintln_above_bars;
use crate::easycrypt::json::{Goal, GoalKind, Status};
use crate::easycrypt::session::{Session, SessionError, Want};
use crate::easycrypt::time_by_role::TimeByRole;
use crate::easycrypt::transcript::{Role, SentenceCtx};

use super::goals;
use super::live::{Closing, LiveHandle};
use super::script::{Mark, Script};
use super::ResumeMode;
use crate::easycrypt::job::{AdmitRecord, ClosedNode};
use crate::writers::easycrypt::invariant::{state_relation_op_name, InvariantOp};

type R<T> = Result<T, SessionError>;

/// Why an `admit` is there (story 27 §3.7). The slugs are what the report counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdmitReason {
    /// The lockstep engine could not decide a sampling.
    Stuck,
    /// A claim fails in Domino, so EasyCrypt was not asked.
    DominoFails,
    /// Domino could not decide, and EasyCrypt could not either.
    DominoInconclusive,
    /// Domino verified the claim and EasyCrypt could not close it: where better heuristics pay
    /// off, and story 29's input.
    DominoVerifiedEcFailed,
    /// EasyCrypt's program did not match what the lowering said, and the fallback found nothing.
    ProgramMismatch,
    /// A sampling that `seq` could not be given a safe postcondition for.
    SeqPost,
    /// A goal of the router prelude (the condition, or both sides already aborted).
    Router,
    /// A goal still open when the oracle was sealed (story 33): the walk had not got to it
    /// when the file was written.
    Interrupted,
}

impl AdmitReason {
    pub const ALL: [AdmitReason; 8] = [
        AdmitReason::Stuck,
        AdmitReason::DominoFails,
        AdmitReason::DominoInconclusive,
        AdmitReason::DominoVerifiedEcFailed,
        AdmitReason::ProgramMismatch,
        AdmitReason::SeqPost,
        AdmitReason::Router,
        AdmitReason::Interrupted,
    ];

    pub fn slug(self) -> &'static str {
        match self {
            AdmitReason::Stuck => "stuck",
            AdmitReason::DominoFails => "domino-fails",
            AdmitReason::DominoInconclusive => "domino-inconclusive",
            AdmitReason::DominoVerifiedEcFailed => "domino-verified-ec-failed",
            AdmitReason::ProgramMismatch => "program-mismatch",
            AdmitReason::SeqPost => "seq-post",
            AdmitReason::Router => "router",
            AdmitReason::Interrupted => "interrupted",
        }
    }

    /// The reason a slug names (a session record's).
    pub fn from_slug(slug: &str) -> Option<AdmitReason> {
        AdmitReason::ALL.into_iter().find(|r| r.slug() == slug)
    }

    /// Whether the admit comment needs `Domino: <view>`: only for a reason that does not say
    /// what Domino concluded.
    fn needs_domino_view(self) -> bool {
        matches!(
            self,
            AdmitReason::Router
                | AdmitReason::Stuck
                | AdmitReason::SeqPost
                | AdmitReason::ProgramMismatch
        )
    }
}

/// What Domino itself concluded about the claim an admit stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DominoView {
    Verified,
    Fails,
    Inconclusive,
    /// Domino has no verdict for it (the router prelude).
    NotApplicable,
}

impl DominoView {
    pub fn slug(self) -> &'static str {
        match self {
            DominoView::Verified => "verified",
            DominoView::Fails => "fails",
            DominoView::Inconclusive => "inconclusive",
            DominoView::NotApplicable => "n/a",
        }
    }

    /// The view a slug names (a session record's).
    pub fn from_slug(slug: &str) -> Option<DominoView> {
        [
            DominoView::Verified,
            DominoView::Fails,
            DominoView::Inconclusive,
            DominoView::NotApplicable,
        ]
        .into_iter()
        .find(|v| v.slug() == slug)
    }

    fn worst(self, other: DominoView) -> DominoView {
        use DominoView::*;
        match (self, other) {
            (Fails, _) | (_, Fails) => Fails,
            (Inconclusive, _) | (_, Inconclusive) => Inconclusive,
            _ => self,
        }
    }
}

/// One `admit` in the script.
#[derive(Debug, Clone)]
pub struct Admit {
    pub reason: AdmitReason,
    /// `J<n>` (a joint path), `S<n>` (a stuck point), `N<n>` (a node of the joint tree) or
    /// `router`.
    pub id: String,
    /// `equal-output`, `invariant`, `invariant/StateRelation_<rel>`, `side-goal`, …
    pub claim: String,
    pub domino: DominoView,
    /// The goal as EasyCrypt prints it on one line.
    pub goal: String,
    /// How the last part fallback ended (story 65), or `None` when no fallback ran. The
    /// session record does not hold it.
    pub smt: Option<SmtOutcome>,
}

/// How the last part fallback before an admit ended (story 65).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtOutcome {
    /// A prover call timed out: the goal is too large, or the time too short.
    Timeout,
    /// The provers stopped without a proof: a lemma is missing, or the claim does not hold in
    /// EasyCrypt's model.
    Unknown,
    /// EasyCrypt refused the sentence with no prover call that timed out or gave up.
    Error,
}

impl SmtOutcome {
    pub fn slug(self) -> &'static str {
        match self {
            SmtOutcome::Timeout => "timeout",
            SmtOutcome::Unknown => "unknown",
            SmtOutcome::Error => "error",
        }
    }

    /// The outcome of an answer: `timeout` if a prover call timed out, else `unknown` if one
    /// gave up, else `error` if EasyCrypt refused the sentence, else `None`.
    pub fn of_answer(response: &crate::easycrypt::json::Response) -> Option<SmtOutcome> {
        match response.timing.as_ref().and_then(|t| t.smt) {
            Some(s) if s.timeout > 0 => Some(SmtOutcome::Timeout),
            Some(s) if s.unknown > 0 => Some(SmtOutcome::Unknown),
            _ if response.status != Status::Ok => Some(SmtOutcome::Error),
            _ => None,
        }
    }
}

impl Admit {
    /// The comment after the `admit.`: `(* domino: <fields> *)`, see [`Self::fields`].
    pub fn label(&self) -> String {
        format!("(* domino: {} *)", self.fields())
    }

    /// `J7 StateRelation_rel; domino-verified-ec-failed; smt: timeout`: the node id, the claim
    /// (an invariant claim by its operator's name, nothing for the whole leaf), the reason,
    /// `Domino: <view>` only when the reason does not say it, and the last fallback's outcome
    /// when a fallback ran. The report's admit line has the same fields.
    pub fn fields(&self) -> String {
        let claim = self.claim.strip_prefix("invariant/").unwrap_or(&self.claim);
        let claim = claim
            .strip_prefix("equal-output+invariant")
            .unwrap_or(claim)
            .trim();
        let mut out = self.id.clone();
        if !claim.is_empty() {
            out = format!("{out} {claim}");
        }
        out = format!("{out}; {}", self.reason.slug());
        if self.reason.needs_domino_view() {
            out = format!("{out}; Domino: {}", self.domino.slug());
        }
        if let Some(smt) = self.smt {
            out = format!("{out}; smt: {}", smt.slug());
        }
        out
    }

    /// The admit as the session record holds it, without the goal.
    pub fn to_record(&self) -> AdmitRecord {
        AdmitRecord {
            node: self.id.clone(),
            reason: self.reason.slug().to_string(),
            claim: self.claim.clone(),
            domino: self.domino.slug().to_string(),
        }
    }

    /// An admit of the session record, or `None` for a reason or a verdict this version does
    /// not know.
    pub fn from_record(record: &AdmitRecord) -> Option<Admit> {
        Some(Admit {
            reason: AdmitReason::from_slug(&record.reason)?,
            id: record.node.clone(),
            claim: record.claim.clone(),
            domino: if record.domino.is_empty() {
                DominoView::NotApplicable
            } else {
                DominoView::from_slug(&record.domino)?
            },
            goal: String::new(),
            smt: None,
        })
    }
}

/// What happened while proving one oracle.
#[derive(Debug, Clone, Default)]
pub struct OracleStats {
    /// Goals closed by a tactic other than `admit`.
    pub closed: usize,
    pub admits: Vec<Admit>,
    /// Nodes that used the fallback trial procedure (§3.4).
    pub fallbacks: usize,
    /// Sentences EasyCrypt refused or that were undone.
    pub attempts_undone: usize,
    /// Where the EasyCrypt time went (story 57). Empty until the oracle is done: the session
    /// holds the sums while the walk runs.
    pub time: TimeByRole,
}

/// The open call at the head of a package procedure's program ([`Prover::open_calls`]).
pub(super) const OPEN_CALL: &str = "seq 1 : (#pre); 1: by call (_: true); auto.";

/// What the walked lemma is a judgement about (story 69).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Judgement {
    /// An oracle lemma, `equiv[…]`, walked along the joint tree of lockstep execution.
    Equiv,
    /// A side-invariant lemma, `hoare[…]`, walked along the side tree of one-sided execution
    /// (symbolic-execution story 25). Its tactics name no side, and its leaf has one memory.
    Hoare,
    /// A package-invariant lemma (story 76), `hoare[…]` about one oracle of a package over any
    /// imports, walked along the package tree (symbolic-execution story 29). As [`Self::Hoare`],
    /// but its program has no router, and each import call is an open call (ADR 0017).
    Package,
}

impl Judgement {
    /// The side selector of a one-sided tactic on side `side`: `{1}`, `{2}`, or nothing in a
    /// `hoare` judgement, which has one program.
    fn side(self, side: u8) -> String {
        match self {
            Judgement::Equiv => format!("{{{side}}}"),
            Judgement::Hoare | Judgement::Package => String::new(),
        }
    }

    /// Whether the judgement is about one program: a `hoare` judgement.
    fn one_program(self) -> bool {
        self != Judgement::Equiv
    }
}

/// The joint tree of an oracle with what the walk needs to know about each node's subtree.
pub(super) struct OracleTree<'a> {
    pub outcome: &'a LockstepOutcome,
    /// Indices into `outcome.pairs` of the pairs at or below each node.
    subtree: Vec<Vec<usize>>,
    pair_of_node: HashMap<usize, usize>,
}

impl<'a> OracleTree<'a> {
    pub(super) fn new(outcome: &'a LockstepOutcome) -> OracleTree<'a> {
        let nodes = &outcome.tree.nodes;
        let mut pair_of_node = HashMap::new();
        for (i, pair) in outcome.pairs.iter().enumerate() {
            pair_of_node.insert(pair.node, i);
        }
        // pre-order arena: a child always has a larger index than its parent
        let mut subtree: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
        for idx in (0..nodes.len()).rev() {
            let mut below = Vec::new();
            if let Some(&p) = pair_of_node.get(&idx) {
                below.push(p);
            }
            for child in &nodes[idx].children {
                if let ChildOutcome::Explored { node } = child.outcome {
                    below.extend(subtree[node].iter().copied());
                }
            }
            below.sort_unstable();
            subtree[idx] = below;
        }
        OracleTree {
            outcome,
            subtree,
            pair_of_node,
        }
    }

    fn node(&self, idx: usize) -> &'a JointNode {
        &self.outcome.tree.nodes[idx]
    }

    /// The nodes above `idx`, its parent first.
    fn ancestors(&self, idx: usize) -> Vec<usize> {
        let nodes = &self.outcome.tree.nodes;
        let parent = |child: usize| {
            // pre-order arena: a parent always has a smaller index than its child
            (0..child).rev().find(|&p| {
                nodes[p]
                    .children
                    .iter()
                    .any(|c| matches!(c.outcome, ChildOutcome::Explored { node } if node == child))
            })
        };
        std::iter::successors(parent(idx), |&p| parent(p)).collect()
    }

    fn pairs_below(&self, idx: usize) -> impl Iterator<Item = &'a PairRecord> + '_ {
        self.subtree
            .get(idx)
            .into_iter()
            .flatten()
            .map(|&i| &self.outcome.pairs[i])
    }
}

/// Which claim a part of a goal stands for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Part {
    /// A whole goal, or one whose meaning has not been told apart yet.
    Whole,
    EqualOutput,
    Invariant,
    /// A state relation, by the name of its `define-state-relation`.
    Relation(String),
    /// A side invariant of a side-invariant lemma (story 73): a `PkgInv_<N>_of_<Inst>_in_<C>`
    /// wrapper or a `GameInv_<N>_of_<C>`, by its EasyCrypt name, with the one Domino claim it
    /// stands for.
    SideInvariant {
        op: String,
        claim: String,
    },
}

impl Part {
    pub(super) fn claim_label(&self) -> String {
        match self {
            Part::Whole => "equal-output+invariant".into(),
            Part::EqualOutput => "equal-output".into(),
            Part::Invariant => "invariant".into(),
            Part::Relation(name) => format!("invariant/{}", state_relation_op_name(name)),
            Part::SideInvariant { op, .. } => {
                format!(
                    "invariant/{}",
                    op.rsplit_once('.').map_or(op.as_str(), |(_, n)| n)
                )
            }
        }
    }
}

/// One step of [`Prover::open_part`] on an ambient goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Step {
    /// The binders of a `forall`.
    Intro(String),
    /// The premise of an implication, named.
    Premise(String),
    Unfold(String),
    /// Nothing above applies: `do split`, and the goal is a leaf part if it gives one goal.
    Split,
}

/// The next step on `goal`, and the part it belongs to. `inv` starts [`Part::Invariant`]; an
/// operator of `part_ops` is unfolded and starts the part of [`part_of_op`], or stays in
/// `part`; anything else is split, in `part`.
pub(super) fn ambient_step(goal: &Goal, part: &Part, part_ops: &[InvariantOp]) -> (Step, Part) {
    let concl = &goal.concl;
    if let Some((names, _)) = goals::as_forall(concl) {
        return (Step::Intro(names.join(" ")), part.clone());
    }
    if goals::as_implication(concl).is_some() {
        return (Step::Premise(goals::fresh_name(goal, "hpre")), part.clone());
    }
    match goals::app_op_leaf(concl) {
        Some("inv") => (Step::Unfold("inv".into()), Part::Invariant),
        Some(op) => match part_ops.iter().find(|o| op_leaf(&o.name) == op) {
            Some(listed) => (
                Step::Unfold(listed.name.clone()),
                part_of_op(listed).unwrap_or_else(|| part.clone()),
            ),
            None => (Step::Split, part.clone()),
        },
        None => (Step::Split, part.clone()),
    }
}

/// The last path component of an operator name: `side_inv_C` for `Comp_C.side_inv_C`.
fn op_leaf(name: &str) -> &str {
    name.rsplit_once('.').map_or(name, |(_, n)| n)
}

/// The two decisions on an exit-path `if` whose condition reads `cond`, the one Domino predicts
/// first (story 64 §3.1): `rcondf` on a done-flag guard (`!ec_done`), which comes after the
/// side's terminal; on the router's tail `if (ec_result = None)`, `rcondt` when the side's
/// terminal is an abort (`aborts`), else `rcondf`; on any other `if`, or with no terminal
/// known, `rcondf` first.
pub(super) fn exit_decisions(cond: &str, aborts: Option<bool>) -> [&'static str; 2] {
    let cond = cond.trim().trim_start_matches('(').trim_start();
    let router_tail = cond.starts_with("ec_result = None");
    if router_tail && aborts == Some(true) {
        ["rcondt", "rcondf"]
    } else {
        ["rcondf", "rcondt"]
    }
}

/// The part that an application of `op` starts, or `None` when `op` stays inside the part
/// that contains it.
pub(super) fn part_of_op(op: &InvariantOp) -> Option<Part> {
    if let Some(relation) = &op.relation {
        return Some(Part::Relation(relation.clone()));
    }
    op.claim.as_ref().map(|claim| Part::SideInvariant {
        op: op.name.clone(),
        claim: claim.clone(),
    })
}

fn view_of_verdict(verdict: &Verdict) -> DominoView {
    match verdict {
        Verdict::Verified | Verdict::Unreachable { .. } => DominoView::Verified,
        Verdict::GoalFails { .. } => DominoView::Fails,
        Verdict::Inconclusive { .. } => DominoView::Inconclusive,
    }
}

fn pair_aborts(pair: &PairRecord) -> bool {
    pair.left.terminal.is_abort || pair.right.terminal.is_abort
}

/// What Domino says about `part` on one pair. On a pair where a side aborts, an invariant
/// failure is not held against EasyCrypt (story 23's note: Domino's verdict is stricter there
/// than EasyCrypt's `inv`), so it counts as inconclusive.
pub(super) fn pair_view(pair: &PairRecord, part: &Part) -> DominoView {
    if pair.verdict_of(EQUAL_OUTPUT).is_none() {
        return side_pair_view(pair, part);
    }
    let invariant = |v: &Verdict| {
        let view = view_of_verdict(v);
        if view == DominoView::Fails && pair_aborts(pair) {
            DominoView::Inconclusive
        } else {
            view
        }
    };
    // the EasyCrypt claim set: `equal-output` and `invariant`, neither with a dependency
    let claim = |name: &str| {
        pair.verdict_of(name)
            .expect("a lockstep run on the EasyCrypt listing checks equal-output and invariant")
    };
    match part {
        Part::EqualOutput => view_of_verdict(claim(EQUAL_OUTPUT)),
        Part::Invariant => invariant(claim("invariant")),
        Part::Relation(name) if name == "invariant" => invariant(claim("invariant")),
        Part::Relation(name) => part_view(
            pair,
            &state_relation_op_name(name),
            claim("invariant"),
            invariant,
        ),
        Part::SideInvariant { op, .. } => part_view(pair, op, claim("invariant"), invariant),
        Part::Whole => view_of_verdict(claim(EQUAL_OUTPUT)).worst(invariant(claim("invariant"))),
    }
}

/// What Domino says about `part` on a terminal of a side tree (story 69), whose claims are the
/// package and game invariants of the composition: a side invariant part has the view of its
/// own claim (`Inconclusive` when the side tree has no verdict for it), and every
/// other part the worst view of all the claims. One-sided execution checks no claim at a terminal that
/// aborts (its verdicts are `unreachable`).
fn side_pair_view(pair: &PairRecord, part: &Part) -> DominoView {
    match part {
        Part::SideInvariant { claim, .. } => pair
            .verdict_of(claim)
            .map_or(DominoView::Inconclusive, view_of_verdict),
        _ => pair
            .claims
            .iter()
            .map(|c| view_of_verdict(&c.verdict))
            .fold(DominoView::Verified, DominoView::worst),
    }
}

/// What Domino says about the part of `invariant` called `name` (its EasyCrypt operator) on
/// `pair`. A verified or unreachable `invariant` stands for every part: its goal holds them
/// all. Else the part has the view of its own verdict through `view`, and is `Inconclusive`
/// when it has none (a tree saved before symbolic-execution story 21). It never takes the
/// `invariant` verdict when `invariant` failed.
fn part_view(
    pair: &PairRecord,
    name: &str,
    invariant: &Verdict,
    view: impl Fn(&Verdict) -> DominoView,
) -> DominoView {
    if matches!(invariant, Verdict::Verified | Verdict::Unreachable { .. }) {
        return view_of_verdict(invariant);
    }
    pair.parts()
        .iter()
        .find(|p| p.name == name)
        .map_or(DominoView::Inconclusive, |p| view(&p.verdict))
}

/// The lemmas every `smt(…)` of the last fallbacks is given (§3.5 step 5); the project's own come
/// from `ssp.toml`.
pub(super) const BASE_SMT_LEMMAS: [&str; 5] = ["get_setE", "mem_set", "remE", "mem_rem", "emptyE"];

/// The length of the fallback sequence: the crush `move=> /> <binders> *; smt().` (story 86),
/// then `smt()` and `smt(hints)`, each also with the premise unfolded.
const FALLBACKS: usize = 5;

/// The length of the part fallback sequence ([`Prover::atom`]); the fourth is the key case
/// split.
const PART_FALLBACKS: usize = 4;

/// Timeouts of the prover.
#[derive(Debug, Clone, Copy)]
pub struct Timeouts {
    /// Every sentence but the quick close.
    pub general: Duration,
    /// The quick close (`auto => /#.` on every program goal): short.
    pub quick_close: Duration,
}

/// An oracle's proof as it stands, sealed (story 33): the script with every goal still open
/// closed by an `admit` labelled `interrupted`, the stats counting those admits, and the
/// alignment's mismatches so far.
pub(super) struct Sealed {
    pub script: String,
    pub stats: OracleStats,
    pub mismatches: Vec<String>,
    /// The joint node the walk was in, as the `interrupted` admits name it: `N<k>` or `router`.
    pub node: String,
    /// The outermost closed nodes (the session record's `closed`).
    pub closed: Vec<ClosedNode>,
    /// Resuming: how many closed nodes of the session record were kept so far.
    pub kept: usize,
}

/// Resuming an interrupted oracle on its saved joint tree (ADR 0008): which nodes the earlier
/// job closed, and where it stood.
pub(super) struct Resume {
    /// `trust` or `replay` (`restart` does not resume).
    pub mode: ResumeMode,
    /// The session record's closed nodes, by node index.
    pub closed: BTreeMap<usize, ClosedNode>,
    /// The ancestors of the in-flight node: the earlier job got past their quick close.
    pub skip_quick_close: HashSet<usize>,
    /// The closed nodes the walk has kept or proved again so far, in order; an undone attempt
    /// takes back what it reached. A closed node not reached is kept by a seal.
    pub reached: Vec<usize>,
    /// How many closed nodes were kept.
    pub kept: usize,
    /// While a closed node's script is replayed: the goals open before it. The replayed
    /// sentences are not in the script, so a seal in the middle seals this many goals.
    pub replaying: Option<usize>,
}

impl Resume {
    /// `closed` and `in_flight` (`N<k>` or `router`) as the session record names them.
    ///
    /// Panics on a node id that is not in the tree: the record and the tree were written by the
    /// same job.
    pub(super) fn new(
        tree: &OracleTree<'_>,
        mode: ResumeMode,
        closed: Vec<ClosedNode>,
        in_flight: &str,
    ) -> Resume {
        let total = tree.outcome.tree.nodes.len();
        let index = |id: &str| {
            id.strip_prefix('N')
                .and_then(|k| k.parse::<usize>().ok())
                .filter(|&k| k < total)
                .unwrap_or_else(|| {
                    panic!("node {id} of the session record is not in the saved tree")
                })
        };
        let skip_quick_close = if in_flight == "router" {
            HashSet::new()
        } else {
            tree.ancestors(index(in_flight)).into_iter().collect()
        };
        Resume {
            mode,
            closed: closed.into_iter().map(|c| (index(&c.id), c)).collect(),
            skip_quick_close,
            reached: Vec::new(),
            kept: 0,
            replaying: None,
        }
    }
}

/// A point to return to: the session's state and the script's.
struct Snap {
    state: u64,
    script: Mark,
    closed: usize,
    /// How many closed nodes of the session record had been reached ([`Resume::reached`]), and
    /// how many of them kept.
    reached: usize,
    kept: usize,
}

pub(super) struct Prover<'a> {
    pub session: &'a mut Session,
    /// An oracle lemma or a side-invariant lemma.
    pub judgement: Judgement,
    pub script: Script,
    pub tree: &'a OracleTree<'a>,
    pub hints: &'a [String],
    /// The operators unfolded in a premise, in the order `rewrite /… in` unfolds them, the one
    /// whose premise is unfolded first: those of the invariant file ([`invariant_ops`], `inv`
    /// first) for an oracle lemma, the composition's side invariant operators
    /// ([`side_invariant_ops`], `side_inv_<C>` first) for a side-invariant lemma.
    ///
    /// [`invariant_ops`]: crate::writers::easycrypt::invariant::invariant_ops
    /// [`side_invariant_ops`]: crate::writers::easycrypt::invariant::side_invariant_ops
    pub unfold_ops: &'a [String],
    /// The operators unfolded inside a leaf part ([`leaf_part_ops`] for an oracle lemma, the
    /// side invariant operators for a side-invariant lemma), matched by the last component of
    /// their name: a `StateRelation_` operator starts a [`Part::Relation`], an operator with a
    /// claim (a wrapper or a `GameInv_<N>_of_<C>`) a [`Part::SideInvariant`]; any other is unfolded in
    /// the part it is in, and is never a part of its own.
    ///
    /// [`leaf_part_ops`]: crate::writers::easycrypt::invariant::leaf_part_ops
    pub part_ops: &'a [InvariantOp],
    pub timeouts: Timeouts,
    /// The quick close (`auto => /#.` on every program goal) is on unless a test turns it off to
    /// exercise the walk.
    pub quick_close: bool,
    /// The exported oracle, for the transcript's notes.
    pub oracle: &'a str,
    /// The most time splitting one leaf by meaning may take (`--leaf-budget`), or `None` for
    /// no limit: each sentence is still bounded by its timeout, so a leaf always ends.
    pub leaf_budget: Option<Duration>,
    /// When the current leaf's budget runs out.
    pub deadline: Option<std::time::Instant>,
    pub stats: OracleStats,
    /// The live translation page (story 28), told which node and closing attempt the walk is at.
    pub live: Option<LiveHandle>,
    /// Called with the sealed oracle after every joint node (`--write-granularity node`).
    pub checkpoint: Option<&'a mut dyn FnMut(Sealed)>,
    /// Also call the checkpoint after every accepted sentence (`--write-granularity tactic`),
    /// which makes the write after each node redundant.
    pub per_sentence: bool,
    /// The joint node being proved, innermost (`None` in the router prelude).
    pub node: Option<usize>,
    /// The descriptions of the alignment's mismatches: with any, the oracle is proved by the
    /// fallback.
    pub mismatches: Vec<String>,
    /// The oracle sealed where the walk stood when it saw that the run was asked to stop
    /// (Ctrl-C, story 34), or when EasyCrypt left an interrupt unanswered; the walk then unwinds
    /// with [`SessionError::Stopped`] or [`SessionError::Unresponsive`].
    pub stopped: Option<Sealed>,
    /// Set when the oracle is resumed from the session record's closed nodes.
    pub resume: Option<Resume>,
    /// The premises the leaf procedure introduced on the way to the front goal, in the order of
    /// introduction (story 65): part fallback 3 moves them back into the goal.
    pub premises: Vec<String>,
    /// The binders the leaf procedure introduced on the way to the front goal (story 66): the
    /// key case split splits on them.
    pub binders: Vec<String>,
    /// The outcome of the last sentence sent ([`SmtOutcome::of_answer`]).
    pub last_smt: Option<SmtOutcome>,
    /// The outcome of the last part fallback, for the next admit's comment; the admit takes it.
    pub admit_smt: Option<SmtOutcome>,
}

impl Prover<'_> {
    // ------------------------------------------------------------------
    // Session primitives
    // ------------------------------------------------------------------

    pub(super) fn count(&self) -> usize {
        self.session.count()
    }

    // ------------------------------------------------------------------
    // The seal (story 33)
    // ------------------------------------------------------------------

    /// The oracle sealed where the walk stands: every goal it still has open is admitted, with
    /// the reason `interrupted` and the joint node the walk is in. Sends nothing to EasyCrypt,
    /// and the walk goes on from the unsealed script. Between two sentences is any time.
    pub(super) fn seal(&self) -> Sealed {
        self.seal_with(self.count())
    }

    /// [`Self::seal`], with `open` goals open in the session.
    fn seal_with(&self, open: usize) -> Sealed {
        let admit = Admit {
            reason: AdmitReason::Interrupted,
            id: self
                .node
                .map_or_else(|| "router".to_string(), |n| format!("N{n}")),
            claim: "open-goal".into(),
            domino: DominoView::NotApplicable,
            goal: String::new(),
            smt: None,
        };
        let (script, admits) = self.script.sealed(open, &admit.label());
        let node = admit.id.clone();
        let mut stats = self.stats.clone();
        stats.admits.extend(std::iter::repeat_n(admit, admits));
        let mut closed = script.closed_nodes();
        // closed nodes of the earlier job the resumed walk has not reached yet stay closed
        if let Some(resume) = &self.resume {
            closed.extend(
                resume
                    .closed
                    .iter()
                    .filter(|(idx, _)| !resume.reached.contains(idx))
                    .map(|(_, c)| c.clone()),
            );
        }
        Sealed {
            closed,
            kept: self.resume.as_ref().map_or(0, |r| r.kept),
            script: script.render(),
            stats,
            mismatches: self.mismatches.clone(),
            node,
        }
    }

    // ------------------------------------------------------------------
    // Ctrl-C (story 34)
    // ------------------------------------------------------------------

    /// Where the walk stops if the run was asked to stop: the oracle is sealed as it stands
    /// ([`Self::stopped`]) and [`SessionError::Stopped`] unwinds the walk, fallback sequences and leaf
    /// splits included. Called before every sentence the walk sends, so after an interrupted
    /// sentence has been rolled back like any failed attempt. The seal reads only the script and
    /// the goal count, which agree between any two sentences.
    fn stop_point(&mut self) -> R<()> {
        if !self.session.stop_requested() {
            return Ok(());
        }
        Err(self.stop_with(self.count()))
    }

    /// Seals the oracle with `open` goals open, unless it is sealed already, and returns
    /// [`SessionError::Stopped`].
    fn stop_with(&mut self, open: usize) -> SessionError {
        let open = self
            .resume
            .as_ref()
            .and_then(|r| r.replaying)
            .unwrap_or(open);
        if self.stopped.is_none() {
            self.stopped = Some(self.seal_with(open));
        }
        SessionError::Stopped
    }

    /// `e`, unless EasyCrypt left an interrupt unanswered ([`SessionError::Unresponsive`]).
    /// When the run was asked to stop, that is a stop like any other, with what has been proved
    /// so far. Otherwise the oracle is sealed where the walk stands ([`Self::stopped`]), as a
    /// stop would seal it, and `e` unwinds the walk: the caller respawns EasyCrypt. The seal is
    /// consistent: the goals are those of the last answer, and the script holds only accepted
    /// sentences.
    fn session_failed(&mut self, e: SessionError) -> SessionError {
        if !matches!(e, SessionError::Unresponsive { .. }) {
            return e;
        }
        if self.session.stop_requested() {
            return self.stop_point().expect_err("a stop was requested");
        }
        let _ = self.stop_with(self.count());
        e
    }

    /// Seals the oracle and hands it to the checkpoint, if there is one.
    fn checkpoint(&mut self) {
        if self.checkpoint.is_none() {
            return;
        }
        let sealed = self.seal();
        if let Some(checkpoint) = self.checkpoint.as_mut() {
            checkpoint(sealed);
        }
    }

    fn front(&self) -> Option<&Goal> {
        self.session.front()
    }

    /// Makes [`Self::front`] the front goal in full: after sentences that asked for
    /// [`Want::Head`], it is cut at depth 4 ([`Session::ensure_front`]).
    fn full_front(&mut self) -> R<()> {
        self.session
            .ensure_front(Want::Full)
            .map_err(|e| self.session_failed(e))
    }

    fn is_if_split(&self) -> bool {
        goals::is_if_split(self.front(), |i| self.session.kind(i))
    }

    fn state(&self) -> u64 {
        self.session.last().map_or(0, |r| r.state)
    }

    fn snap(&self) -> Snap {
        Snap {
            state: self.state(),
            script: self.script.mark(),
            closed: self.stats.closed,
            reached: self.resume.as_ref().map_or(0, |r| r.reached.len()),
            kept: self.resume.as_ref().map_or(0, |r| r.kept),
        }
    }

    fn rollback(&mut self, snap: Snap) -> R<()> {
        if self.state() != snap.state {
            if let Err(e) = self.session.undo_to(snap.state) {
                return Err(self.session_failed(e));
            }
        }
        self.script.rollback(snap.script);
        self.stats.closed = snap.closed;
        if let Some(resume) = self.resume.as_mut() {
            resume.reached.truncate(snap.reached);
            resume.kept = snap.kept;
        }
        self.stats.attempts_undone += 1;
        Ok(())
    }

    /// Sends one sentence, its answer carrying what `want` asks for (ADR 0012: what the caller
    /// reads next); an accepted one goes into the script. `Ok(false)` if EasyCrypt refused it (or
    /// it was interrupted): the session is then where it was, front goal included.
    pub(super) fn send(&mut self, sentence: &str, want: Want) -> R<bool> {
        self.stop_point()?;
        if let Some(live) = &self.live {
            live.sentence_sent(sentence);
        }
        let before = self.count();
        let ok = match self.session.send(sentence, want) {
            // the sentence a stop interrupted lost its goals: stop as if it had not been sent
            Ok(response) if response.goals_lost() => return Err(self.stop_with(before)),
            Ok(response) => {
                self.last_smt = SmtOutcome::of_answer(response);
                response.status == Status::Ok
            }
            Err(e) => return Err(self.session_failed(e)),
        };
        if ok {
            self.script.push(sentence, None);
            let after = self.count();
            if after < before {
                self.stats.closed += before - after;
            }
            if self.per_sentence {
                self.checkpoint();
            }
        }
        Ok(ok)
    }

    /// Sends `sentence` without writing it into the script, the live line showing `shown`:
    /// whether EasyCrypt accepted it. A stop and an unanswered interrupt seal and unwind as in
    /// [`Self::send`].
    fn send_unscripted(&mut self, sentence: &str, shown: &str, want: Want) -> R<bool> {
        self.stop_point()?;
        if let Some(live) = &self.live {
            live.sentence_sent(shown);
        }
        let before = self.count();
        match self.session.send(sentence, want) {
            Ok(response) if response.goals_lost() => Err(self.stop_with(before)),
            Ok(response) => Ok(response.status == Status::Ok),
            Err(e) => Err(self.session_failed(e)),
        }
    }

    /// Sends the sentences in order, each asking for `want`, and keeps them if all are accepted
    /// and `holds` at the end; otherwise everything is undone.
    fn attempt(
        &mut self,
        sentences: &[&str],
        want: Want,
        holds: impl Fn(&Self) -> bool,
    ) -> R<bool> {
        let snap = self.snap();
        for sentence in sentences {
            if !self.send(sentence, want)? {
                self.rollback(snap)?;
                return Ok(false);
            }
        }
        if !holds(self) {
            self.rollback(snap)?;
            return Ok(false);
        }
        Ok(true)
    }

    /// An attempt that must close the front goal. Its answers carry no goal ([`Want::Status`]):
    /// it is read only from the count of open goals.
    fn try_close(&mut self, sentences: &[&str]) -> R<bool> {
        let before = self.count();
        self.attempt(sentences, Want::Status, |p| p.count() + 1 == before)
    }

    fn with_timeout<T>(&mut self, timeout: Duration, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = self.session.timeout();
        self.session.set_timeout(timeout);
        let result = f(self);
        self.session.set_timeout(saved);
        result
    }

    /// Runs `f` with its sentences sent for `role` (the transcript's `ctx`, story 56), at the
    /// same oracle and node; the role before is back afterwards, also on an error.
    fn as_role<T>(&mut self, role: Role, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let context = self.session.context().with_role(role);
        self.in_context(context, f)
    }

    /// Runs `f` in `context`; the context before is back afterwards.
    fn in_context<T>(&mut self, context: SentenceCtx, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = self.session.context().clone();
        self.session.set_context(context)?;
        let result = f(self);
        let restored = self.session.set_context(saved);
        let value = result?;
        restored.map(|()| value)
    }

    /// The context of joint node `idx`: its structure, until a closing attempt says otherwise.
    fn node_context(&self, idx: usize) -> SentenceCtx {
        SentenceCtx {
            oracle: Some(self.oracle.to_string()),
            node: Some((idx, self.tree.node(idx).kind.as_str().to_string())),
            role: Role::Structure,
        }
    }

    /// Runs `f` as the block of the next subgoal: its first sentence gets the bullet.
    fn bullet<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        self.script.enter_bullet(self.count());
        let result = f(self);
        self.script.leave_bullet();
        result
    }

    // ------------------------------------------------------------------
    // Admits
    // ------------------------------------------------------------------

    /// Closes the front goal with a labelled `admit`.
    fn admit(&mut self, reason: AdmitReason, id: &str, claim: &str, domino: DominoView) -> R<()> {
        self.admit_of_part(&Part::Whole, reason, id, claim, domino)
    }

    /// [`Self::admit`] of `part` of a leaf's claims (the whole claim is no part).
    fn admit_of_part(
        &mut self,
        part: &Part,
        reason: AdmitReason,
        id: &str,
        claim: &str,
        domino: DominoView,
    ) -> R<()> {
        let role = Role::Admit {
            part: (*part != Part::Whole).then(|| part.claim_label()),
        };
        self.as_role(role, |p| p.send_admit(reason, id, claim, domino))
    }

    fn send_admit(
        &mut self,
        reason: AdmitReason,
        id: &str,
        claim: &str,
        domino: DominoView,
    ) -> R<()> {
        let goal_pp = self
            .front()
            .map(|g| g.concl.pp.replace('\n', " "))
            .unwrap_or_default();
        let smt = self.admit_smt.take();
        let admit = Admit {
            reason,
            id: id.to_string(),
            claim: claim.to_string(),
            domino,
            goal: goal_pp,
            smt,
        };
        let label = admit.label();
        self.stop_point()?;
        let before = self.count();
        let response = match self.session.send("admit.", Want::Status) {
            Ok(response) if response.goals_lost() => return Err(self.stop_with(before)),
            Ok(response) => response,
            Err(e) => return Err(self.session_failed(e)),
        };
        if response.status != Status::Ok {
            let msg = response
                .error
                .as_ref()
                .map_or_else(|| format!("{:?}", response.status), |e| e.msg.clone());
            // interrupted by a stop request
            self.stop_point()?;
            // `admit.` closes any goal: a refusal means there is none, and the walk is lost
            return Err(SessionError::Refused {
                sentence: "admit.".into(),
                msg,
            });
        }
        self.script.push("admit.", Some(label));
        if let Some(live) = &self.live {
            live.admitted(&admit);
        }
        self.stats.admits.push(admit);
        if self.per_sentence {
            self.checkpoint();
        }
        Ok(())
    }

    /// The first pair below `node` for which `part` has the given view, else its first pair.
    fn id_below(&self, node: usize, part: &Part, view: DominoView) -> String {
        let tree = self.tree;
        let pick = tree
            .pairs_below(node)
            .find(|p| pair_view(p, part) == view)
            .or_else(|| tree.pairs_below(node).next());
        match pick {
            Some(pair) => pair.id.clone(),
            None => format!("N{node}"),
        }
    }

    /// Admits after EasyCrypt failed on `part` of the subtree at `node`: the reason is what
    /// Domino itself concluded (§3.6).
    fn admit_ec_failed(&mut self, node: usize, part: &Part, claim: &str) -> R<()> {
        let tree = self.tree;
        let view = if tree.subtree.get(node).is_none_or(|below| below.is_empty()) {
            DominoView::Inconclusive
        } else {
            tree.pairs_below(node)
                .map(|p| pair_view(p, part))
                .fold(DominoView::Verified, DominoView::worst)
        };
        let reason = match view {
            DominoView::Fails => AdmitReason::DominoFails,
            DominoView::Inconclusive | DominoView::NotApplicable => AdmitReason::DominoInconclusive,
            DominoView::Verified => AdmitReason::DominoVerifiedEcFailed,
        };
        let id = self.id_below(node, part, view);
        self.admit_of_part(part, reason, &id, claim, view)
    }

    // ------------------------------------------------------------------
    // Closing ambient goals: side goals, the fallback sequence
    // ------------------------------------------------------------------

    /// Brings the front goal to a plain formula: introduces the memory of a quantified program
    /// judgement (`forall &m0, hoare[…]`, what `rcondt` leaves as its side goal) and reduces a
    /// program judgement with nothing left to do (`<skip>`) by `auto.`
    fn reduce_to_ambient(&mut self) -> R<()> {
        for _ in 0..4 {
            let step = {
                let Some(goal) = self.front() else {
                    return Ok(());
                };
                let c = &goal.concl;
                if goals::wraps_program(c) {
                    goals::as_forall(c).map(|(names, _)| format!("move => {}.", names.join(" ")))
                } else if !goals::is_ambient(goal) {
                    Some("auto.".to_string())
                } else {
                    None
                }
            };
            let Some(sentence) = step else { return Ok(()) };
            let before = self.count();
            if !self.attempt(&[&sentence], Want::Head, |p| p.count() == before)? {
                return Ok(());
            }
        }
        Ok(())
    }

    /// Unfolds the invariant's operators in the hypothesis `name` (`rewrite /inv /params_inv
    /// /StateRelation_… /Helper_… in name.`), so a solver sees through them; only if the
    /// hypothesis may mention `inv` ([`goals::may_mention_op`]: a premise read at `head` is cut
    /// at depth 4, and `inv` can be deeper). `Ok(false)` if there was nothing to unfold, if
    /// EasyCrypt refused, or if it warned `unused unfold` for each operator (story 86).
    pub(super) fn unfold_premise(&mut self, name: &str) -> R<bool> {
        // `inv` for an oracle lemma, `Comp_<C>.side_inv_<C>` for a side-invariant lemma
        let Some(head) = self.unfold_ops.first().cloned() else {
            return Ok(false);
        };
        let may_mention = self.front().is_some_and(|g| {
            g.hyps.iter().any(|h| {
                h.name == name
                    && h.form
                        .as_ref()
                        .is_some_and(|f| goals::may_mention_op(f, op_leaf(&head)))
            })
        });
        if !may_mention {
            return Ok(false);
        }
        let all: Vec<&str> = self.unfold_ops.iter().map(String::as_str).collect();
        let only_head = [head.as_str()];
        let tries: &[&[&str]] = if all.len() > 1 {
            &[&all, &only_head]
        } else {
            &[&only_head]
        };
        for &ops in tries {
            let list: String = ops.iter().map(|o| format!(" /{o}")).collect();
            if self.send(&format!("rewrite{list} in {name}."), Want::Head)? {
                return Ok(!self.all_unfolds_unused(ops));
            }
        }
        Ok(false)
    }

    /// Whether the last answer warns `unused unfold: /<op>` for each of `ops`: the rewrite
    /// changed nothing.
    fn all_unfolds_unused(&self, ops: &[&str]) -> bool {
        let Some(answer) = self.session.last() else {
            return false;
        };
        ops.iter().all(|op| {
            let warning = format!("unused unfold: /{op}");
            answer.messages.iter().any(|m| m.text.contains(&warning))
        })
    }

    /// The binders of an ambient goal `forall <binders>, A => B`, as `move =>` names them; `None`
    /// if the front goal has no such premise.
    fn premise_binders(&self) -> Option<String> {
        let goal = self.front()?;
        match goals::as_forall(&goal.concl) {
            Some((names, body)) if goals::as_implication(body).is_some() => Some(names.join(" ")),
            _ => None,
        }
    }

    /// The crush of a side goal (story 86): `move=> /> <binders> *; smt().` `/>` substitutes the
    /// equalities of the premise, destructs its conjunctions and existentials, and the solver
    /// sees only the facts left. `Ok(false)`, with nothing sent, on a goal without a premise.
    fn try_crush(&mut self) -> R<bool> {
        let Some(names) = self.premise_binders() else {
            return Ok(false);
        };
        self.try_close(&[&format!("move=> /> {names} *; smt().")])
    }

    /// `move => <binders> hpre.`, the invariant unfolded in `hpre`, then `tail`.
    fn try_with_premise(&mut self, tail: &str) -> R<bool> {
        let Some(names) = self.premise_binders() else {
            return Ok(false);
        };
        let Some(premise) = self.front().map(|g| goals::fresh_name(g, "hpre")) else {
            return Ok(false);
        };
        let before = self.count();
        let snap = self.snap();
        if self.send(&format!("move => {names} {premise}."), Want::Head)? {
            self.unfold_premise(&premise)?;
            if self.send(tail, Want::Status)? && self.count() + 1 == before {
                return Ok(true);
            }
        }
        self.rollback(snap)?;
        Ok(false)
    }

    /// The fallback sequence (§3.5): the crush (story 86), then `smt()`, then the same with the
    /// premise introduced and the invariant unfolded in it, then the hint list likewise.
    fn fallbacks(&mut self) -> R<bool> {
        self.as_role(Role::Reduce, Self::reduce_to_ambient)?;
        let crush = Closing::Fallback {
            k: 1,
            of: FALLBACKS,
        };
        let closed = self.as_role(Role::SideGoalFallback(1), |p| {
            p.closing_attempt(crush, "move=> /> <binders> *; smt()", Self::try_crush)
        })?;
        if closed {
            return Ok(true);
        }
        let hints = self.hint_sentence();
        for (i, tail) in ["smt().", hints.as_str()].into_iter().enumerate() {
            let k = 2 * i + 2;
            let shown = tail.trim_end_matches('.');
            let plain = Closing::Fallback { k, of: FALLBACKS };
            let closed = self.as_role(Role::SideGoalFallback(k), |p| {
                p.closing_attempt(plain, shown, |p| p.try_close(&[tail]))
            })?;
            if closed {
                return Ok(true);
            }
            let unfolded = Closing::Fallback {
                k: k + 1,
                of: FALLBACKS,
            };
            let shown = format!("{shown} (premise unfolded)");
            let closed = self.as_role(Role::SideGoalFallback(k + 1), |p| {
                p.closing_attempt(unfolded, &shown, |p| p.try_with_premise(tail))
            })?;
            if closed {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Runs `f`, a closing attempt, and tells the live page what it was and how it ended.
    fn closing_attempt(
        &mut self,
        closing: Closing,
        shown: &str,
        f: impl FnOnce(&mut Self) -> R<bool>,
    ) -> R<bool> {
        if let Some(live) = &self.live {
            live.attempt(closing, shown, self.session.timeout());
        }
        let closed = f(self)?;
        if let Some(live) = &self.live {
            live.attempt_ended(closed);
        }
        Ok(closed)
    }

    /// `auto => /#.` as a closing attempt.
    fn try_quick_close(&mut self) -> R<bool> {
        self.as_role(Role::QuickClose, |p| {
            p.closing_attempt(Closing::QuickClose, "auto => /#", |p| {
                p.try_close(&["auto => /#."])
            })
        })
    }

    /// The quick close of a program goal (§3.3), under its short timeout; `Ok(false)` without
    /// sending anything when it is off.
    fn quick_close_program(&mut self) -> R<bool> {
        if !self.quick_close {
            return Ok(false);
        }
        let timeout = self.timeouts.quick_close;
        self.with_timeout(timeout, Self::try_quick_close)
    }

    /// The claim of a whole leaf: what the oracle lemma's postcondition says, or the side
    /// invariant of a side-invariant lemma.
    fn whole_claim(&self) -> &'static str {
        match self.judgement {
            Judgement::Equiv => "equal-output+invariant",
            Judgement::Hoare => "side-invariant",
            Judgement::Package => "package-invariant",
        }
    }

    fn hint_sentence(&self) -> String {
        let mut names: Vec<&str> = BASE_SMT_LEMMAS.to_vec();
        names.extend(self.hints.iter().map(String::as_str));
        format!("smt({}).", names.join(" "))
    }

    /// A side goal (a condition, the side goal of `rcondt`): the quick close, then the fallbacks,
    /// else an admit whose reason is `Router` for the router prelude and otherwise
    /// `domino-verified-ec-failed`: Domino decided this branch under its assumptions.
    pub(super) fn close_side_goal(&mut self, node: usize, claim: &str, router: bool) -> R<()> {
        if self.try_quick_close()? || self.fallbacks()? {
            return Ok(());
        }
        if router {
            return self.admit(
                AdmitReason::Router,
                "router",
                claim,
                DominoView::NotApplicable,
            );
        }
        let id = self.id_below(node, &Part::Whole, DominoView::Verified);
        self.admit(
            AdmitReason::DominoVerifiedEcFailed,
            &id,
            claim,
            DominoView::Verified,
        )
    }

    // ------------------------------------------------------------------
    // The walk
    // ------------------------------------------------------------------

    /// Proves the front goal, which is the program goal of joint node `idx`.
    pub(super) fn prove_node(&mut self, idx: usize) -> R<()> {
        if let Some(live) = &self.live {
            let node = self.tree.node(idx);
            let mut ids: Vec<String> = self.tree.pairs_below(idx).map(|p| p.id.clone()).collect();
            ids.extend(node.stuck.clone());
            live.node_entered(&format!("N{idx}"), node.kind.as_str(), ids, Some(idx));
            live.node_started(&format!("N{idx}"), self.tree.outcome.tree.nodes.len());
        }
        let parent = self.node.replace(idx);
        let start = self.script.node_start(idx);
        let admits_before = self.stats.admits.len();
        let context = self.node_context(idx);
        let result = self.in_context(context, |p| match p.keep_node(idx) {
            Ok(true) => Ok(()),
            Ok(false) => p.prove_node_inner(idx),
            Err(e) => Err(e),
        });
        self.node = parent;
        if result.is_ok() {
            let admits = self.stats.admits[admits_before..]
                .iter()
                .map(Admit::to_record)
                .collect();
            self.script.close_node(start, admits);
        }
        if result.is_ok() && !self.per_sentence {
            self.checkpoint();
        }
        if let Some(live) = &self.live {
            live.node_left();
            // back in the parent, whose sentences the bar shows next
            let parent = parent.map_or_else(|| "router".to_string(), |p| format!("N{p}"));
            live.node_started(&parent, self.tree.outcome.tree.nodes.len());
        }
        result
    }

    /// A node the session record holds as closed (resuming): its goal is closed without being
    /// proved again, by `admit.` (`trust`) or by sending its recorded script again (`replay`), and
    /// the recorded script goes into the file. `false`: the node is not closed in the record, or
    /// a replayed sentence was rejected and everything was undone; it is proved live.
    fn keep_node(&mut self, idx: usize) -> R<bool> {
        let Some(resume) = self.resume.as_ref() else {
            return Ok(false);
        };
        let Some(closed) = resume.closed.get(&idx).cloned() else {
            return Ok(false);
        };
        let mode = resume.mode;
        let reached = |p: &mut Self| {
            if let Some(resume) = p.resume.as_mut() {
                resume.reached.push(idx);
            }
        };
        let Some(admits) = closed
            .admits
            .iter()
            .map(Admit::from_record)
            .collect::<Option<Vec<_>>>()
        else {
            eprintln_above_bars(&format!(
                "warning: N{idx} of {} has an admit this Domino does not know; it is proved again",
                self.oracle
            ));
            reached(self);
            return Ok(false);
        };
        // a stop before the node is kept or proved again leaves it closed, for the seal
        let kept = self.as_role(Role::Resume, |p| match mode {
            ResumeMode::Replay => p.replay(idx, &closed),
            ResumeMode::Trust => {
                if !p.send_unscripted("admit.", "kept", Want::Status)? {
                    // interrupted by a stop request
                    p.stop_point()?;
                    // `admit.` closes any goal: a refusal means there is none, and the walk is lost
                    return Err(SessionError::Refused {
                        sentence: "admit.".into(),
                        msg: format!("no goal for kept node N{idx}"),
                    });
                }
                Ok(true)
            }
            ResumeMode::Restart => unreachable!("restart does not resume"),
        })?;
        reached(self);
        if !kept {
            return Ok(false);
        }
        self.script.push_closed(idx, &closed);
        self.stats.admits.extend(admits);
        if let Some(resume) = self.resume.as_mut() {
            resume.kept += 1;
        }
        if let Some(live) = &self.live {
            live.node_kept();
        }
        if self.per_sentence {
            self.checkpoint();
        }
        Ok(true)
    }

    /// Sends node `idx`'s recorded script again: whether EasyCrypt accepted every sentence and
    /// the node's goal is closed. Otherwise it is all undone.
    fn replay(&mut self, idx: usize, closed: &ClosedNode) -> R<bool> {
        let before = self.count();
        if let Some(resume) = self.resume.as_mut() {
            resume.replaying = Some(before);
        }
        let replayed = self.replay_sentences(idx, closed, before);
        if let Some(resume) = self.resume.as_mut() {
            resume.replaying = None;
        }
        replayed
    }

    fn replay_sentences(&mut self, idx: usize, closed: &ClosedNode, before: usize) -> R<bool> {
        let state = self.state();
        for line in &closed.script {
            if self.send_unscripted(&line.sentence, &line.sentence, Want::Full)? {
                continue;
            }
            // interrupted by a stop request, not rejected
            self.stop_point()?;
            eprintln_above_bars(&format!(
                "warning: replaying N{idx} of {}: EasyCrypt rejected `{}`; N{idx} is proved again",
                self.oracle, line.sentence
            ));
            return self.undo_replay(state);
        }
        if self.count() + 1 != before {
            eprintln_above_bars(&format!(
                "warning: replaying N{idx} of {}: its script did not close its goal; N{idx} is \
                 proved again",
                self.oracle
            ));
            return self.undo_replay(state);
        }
        Ok(true)
    }

    fn undo_replay(&mut self, state: u64) -> R<bool> {
        if self.state() != state {
            if let Err(e) = self.session.undo_to(state) {
                return Err(self.session_failed(e));
            }
        }
        self.stats.attempts_undone += 1;
        Ok(false)
    }

    fn prove_node_inner(&mut self, idx: usize) -> R<()> {
        let tree = self.tree;
        let node = tree.node(idx);

        // §3.6: a claim that fails in Domino is not worth EasyCrypt's time
        if let Some(pair) = tree.pairs_below(idx).next() {
            let all_fail = tree.pairs_below(idx).all(|p| match self.judgement {
                Judgement::Equiv => {
                    pair_view(p, &Part::EqualOutput) == DominoView::Fails
                        && pair_view(p, &Part::Invariant) == DominoView::Fails
                }
                // a side tree's terminal: every package and game invariant claim fails
                Judgement::Hoare | Judgement::Package => {
                    !p.claims.is_empty()
                        && p.claims
                            .iter()
                            .all(|c| view_of_verdict(&c.verdict) == DominoView::Fails)
                }
            });
            if all_fail {
                let id = pair.id.clone();
                let claim = self.whole_claim();
                return self.admit(AdmitReason::DominoFails, &id, claim, DominoView::Fails);
            }
        }

        // the quick close (§3.3): most abort branches close in one step. Resuming, the in-flight node's
        // ancestors skip it: the earlier job got past it into a child.
        let resumed_past = self
            .resume
            .as_ref()
            .is_some_and(|r| r.skip_quick_close.contains(&idx));
        if self.judgement == Judgement::Package {
            self.open_calls()?;
        }
        if node.kind != NodeKind::TerminalPair && !resumed_past && self.quick_close_program()? {
            return Ok(());
        }

        match node.kind {
            NodeKind::TerminalPair => self.leaf(idx),
            NodeKind::Stuck => {
                let stuck = node
                    .stuck
                    .as_deref()
                    .and_then(|id| tree.outcome.stuck.iter().find(|s| s.id == id));
                let (id, claim) = stuck.map_or_else(
                    || (format!("N{idx}"), "stuck".to_string()),
                    |s| (s.id.clone(), format!("stuck/{}", s.reason.as_str())),
                );
                let view = tree
                    .pairs_below(idx)
                    .map(|p| pair_view(p, &Part::Whole))
                    .fold(DominoView::Verified, DominoView::worst);
                self.admit(AdmitReason::Stuck, &id, &claim, view)
            }
            NodeKind::Unreachable => {
                if self.try_close(&["exfalso; smt()."])? {
                    return Ok(());
                }
                self.admit(
                    AdmitReason::DominoVerifiedEcFailed,
                    &format!("N{idx}"),
                    "unreachable",
                    DominoView::Verified,
                )
            }
            _ => {
                let snap = self.snap();
                if self.step_node(idx)? {
                    return Ok(());
                }
                self.rollback(snap)?;
                self.stats.fallbacks += 1;
                self.prove_blind(idx, 64)
            }
        }
    }

    /// `sp k l.` for the assignments at the head of the front goal's programs, `k`/`l` counted
    /// from EasyCrypt's JSON. `false` if the front goal is not a program goal or `sp` failed.
    fn sp_front(&mut self) -> R<bool> {
        if self.judgement.one_program() {
            let Some(k) = self
                .front()
                .and_then(goals::program)
                .map(|p| goals::leading_assignments(&p.stmt))
            else {
                return Ok(false);
            };
            // with its count: a bare `sp` also goes through the `if`s that follow
            return if k == 0 {
                Ok(true)
            } else {
                self.send(&format!("sp {k}."), Want::Full)
            };
        }
        let Some((k, l)) = self.front().and_then(goals::sp_counts) else {
            return Ok(false);
        };
        if k + l == 0 {
            return Ok(true);
        }
        self.send(&format!("sp {k} {l}."), Want::Full)
    }

    /// The tactic of a non-terminal, non-stuck node and its children. `Ok(false)` if the
    /// tactic did not apply (nothing of the children has been handled then).
    ///
    /// `sp` runs only before a two-sided step (`if.`, `if{1}.`, `seq`), which needs both
    /// programs' heads at the same place. A determined node sends `rcondt{i} ^if` without it:
    /// the side goal reasons about the code before the `if` itself, and each `sp` adds
    /// existentials to the precondition. The straight-line code that stays is taken by the
    /// next two-sided step's `sp` or by the leaf.
    fn step_node(&mut self, idx: usize) -> R<bool> {
        let kind = self.tree.node(idx).kind;
        if kind == NodeKind::Determined {
            return if self.front().is_some_and(goals::is_program) {
                self.determined(idx)
            } else {
                Ok(false)
            };
        }
        if !self.sp_front()? {
            return Ok(false);
        }
        if self.judgement.one_program() {
            return match kind {
                NodeKind::Split => self.split_hoare(idx),
                NodeKind::SamplingIndependent => self.sampling_hoare(idx),
                _ => Ok(false),
            };
        }
        match kind {
            NodeKind::Synchronized => self.synchronized(idx),
            NodeKind::Split => self.split(idx),
            NodeKind::SamplingSynchronized => self.sampling(idx, true),
            NodeKind::SamplingIndependent => self.sampling(idx, false),
            _ => Ok(false),
        }
    }

    /// The route of a joint child into the tree.
    fn handle_child(&mut self, parent: usize, child: &JointChild) -> R<()> {
        match &child.outcome {
            ChildOutcome::Explored { node } => self.prove_node(*node),
            ChildOutcome::Pruned { .. } => {
                if self.try_close(&["exfalso; smt()."])? || self.try_close(&["auto => /#."])? {
                    return Ok(());
                }
                self.admit(
                    AdmitReason::DominoVerifiedEcFailed,
                    &format!("N{parent}"),
                    "pruned-combination",
                    DominoView::Verified,
                )
            }
            ChildOutcome::NotExplored => self.admit(
                AdmitReason::DominoInconclusive,
                &format!("N{parent}"),
                "not-explored",
                DominoView::Inconclusive,
            ),
        }
    }

    fn determined(&mut self, idx: usize) -> R<bool> {
        let tree = self.tree;
        let node = tree.node(idx);
        let [child] = node.children.as_slice() else {
            return Ok(false);
        };
        // (side number, decision) of every side that moved alone
        let steps: Vec<(u8, &str)> = [(1u8, &child.left), (2u8, &child.right)]
            .into_iter()
            .filter_map(|(side, step)| step.as_ref().map(|s| (side, s.decision.as_str())))
            .collect();
        if steps.is_empty() {
            return Ok(false);
        }
        for &(side, decision) in &steps {
            let tactic = match decision {
                "then" => "rcondt",
                "else" => "rcondf",
                _ => return Ok(false),
            };
            let before = self.count();
            let at = self.judgement.side(side);
            let closing = format!("{tactic}{at} ^if; 1: auto => /#.");
            if self.send(&closing, Want::Status)? {
                // the side goal closed in the same sentence: the main goal is in front
                if self.count() != before {
                    return Ok(false);
                }
                continue;
            }
            // the side goal did not close in one step: take it on its own
            let plain = format!("{tactic}{at} ^if.");
            if !self.send(&plain, Want::Full)? || self.count() != before + 1 {
                return Ok(false);
            }
            // a `hoare` side goal is a program judgement; `close_side_goal` reduces it
            if self.judgement == Judgement::Equiv
                && !self
                    .front()
                    .is_some_and(|g| goals::is_ambient(g) || goals::is_skip_pair(g))
            {
                return Ok(false);
            }
            self.bullet(|p| p.close_side_goal(idx, "side-goal", false))?;
        }
        self.handle_child(idx, child)?;
        Ok(true)
    }

    fn synchronized(&mut self, idx: usize) -> R<bool> {
        let node = self.tree.node(idx);
        if node.children.len() != 2 {
            return Ok(false);
        }
        let before = self.count();
        if !self.send("if.", Want::Full)? {
            return Ok(false);
        }
        // the condition, then the two arms: told apart by kind
        let shape_ok = self.count() == before + 2 && self.is_if_split();
        if !shape_ok {
            return Ok(false);
        }
        self.bullet(|p| p.close_side_goal(idx, "branch-condition", false))?;
        for child in &node.children {
            self.bullet(|p| p.handle_child(idx, child))?;
        }
        Ok(true)
    }

    fn split(&mut self, idx: usize) -> R<bool> {
        let tree = self.tree;
        let node = tree.node(idx);
        let both =
            node.left.head.kind == HeadKind::Branch && node.right.head.kind == HeadKind::Branch;
        let before = self.count();
        if both {
            if node.children.len() != 4 {
                return Ok(false);
            }
            if !self.send("if{1}.", Want::Full)? || !self.two_programs_in_front(before) {
                return Ok(false);
            }
            for a in 0..2 {
                self.bullet(|p| {
                    let here = p.count();
                    if !p.send("if{2}.", Want::Full)? || !p.two_programs_in_front(here) {
                        // an arm EasyCrypt would not split further
                        return p.admit_ec_failed(idx, &Part::Whole, "split");
                    }
                    for b in 0..2 {
                        p.bullet(|p| p.handle_child(idx, &node.children[a * 2 + b]))?;
                    }
                    Ok(())
                })?;
            }
            return Ok(true);
        }
        // one side splits, the other waits
        if node.children.len() != 2 {
            return Ok(false);
        }
        let side = match &node.children[0] {
            c if c.left.is_some() => 1,
            c if c.right.is_some() => 2,
            _ => return Ok(false),
        };
        if !self.send(&format!("if{{{side}}}."), Want::Full)? || !self.two_programs_in_front(before)
        {
            return Ok(false);
        }
        for child in &node.children {
            self.bullet(|p| p.handle_child(idx, child))?;
        }
        Ok(true)
    }

    /// A branch of a side tree with both arms: `if.` leaves the two arms, `then` in front, and
    /// each is a bullet. EasyCrypt's answer tells only the front goal of a `hoare` judgement
    /// apart (the kinds of the others are `formula`), so only that one is checked.
    fn split_hoare(&mut self, idx: usize) -> R<bool> {
        let node = self.tree.node(idx);
        if node.children.len() != 2 {
            return Ok(false);
        }
        let before = self.count();
        if !self.send("if.", Want::Full)?
            || self.count() != before + 1
            || !self.front().is_some_and(goals::is_program)
        {
            return Ok(false);
        }
        for child in &node.children {
            self.bullet(|p| p.handle_child(idx, child))?;
        }
        Ok(true)
    }

    /// A sampling of a side tree, at the head of the program after `sp`: `seq 1 : (#pre)`, its
    /// first goal closed by `auto`. The side invariants do not name the sampled variable.
    fn sampling_hoare(&mut self, idx: usize) -> R<bool> {
        let node = self.tree.node(idx);
        let [child] = node.children.as_slice() else {
            return Ok(false);
        };
        let is_rnd_head = self
            .front()
            .and_then(goals::program)
            .map(|p| goals::head_after_assignments(&p.stmt))
            .is_some_and(|(k, head)| k == 0 && head.is_some_and(|i| i.kind == "rnd"));
        if !is_rnd_head {
            return Ok(false);
        }
        let before = self.count();
        for close in ["auto => />", "auto => /#", "auto"] {
            let sentence = format!("seq 1 : (#pre); 1: {close}.");
            if self.attempt(&[&sentence], Want::Full, |p| {
                p.count() == before && p.front().is_some_and(goals::is_program)
            })? {
                self.handle_child(idx, child)?;
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// The import calls at the head of a package procedure's program, each after the
    /// assignments before it: open calls (ADR 0017). Each is `sp k.` and then
    /// `seq 1 : (#pre); 1: by call (_: true); auto.`: nothing is known about the import, so the
    /// call keeps the precondition (the import cannot write the package's state) and tells
    /// nothing about its result, which the guard after it splits on. Stops at the first head that
    /// is not a call, or when EasyCrypt refuses; the node's step then fails as it would.
    fn open_calls(&mut self) -> R<()> {
        loop {
            let Some((k, call)) = self.front().and_then(goals::program).map(|p| {
                let (k, head) = goals::head_after_assignments(&p.stmt);
                (k, head.is_some_and(|i| i.kind == "call"))
            }) else {
                return Ok(());
            };
            if !call || (k > 0 && !self.send(&format!("sp {k}."), Want::Full)?) {
                return Ok(());
            }
            if !self.send(OPEN_CALL, Want::Full)? {
                return Ok(());
            }
        }
    }

    /// After a tactic that turned one goal (count `before`) into two program goals.
    fn two_programs_in_front(&self, before: usize) -> bool {
        self.count() == before + 1
            && (0..2).all(|i| self.session.kind(i) == Some(GoalKind::Program))
    }

    fn sampling(&mut self, idx: usize, synchronized: bool) -> R<bool> {
        let tree = self.tree;
        let node = tree.node(idx);
        let [child] = node.children.as_slice() else {
            return Ok(false);
        };
        let Some((left, right)) = self.front().and_then(goals::sides) else {
            return Ok(false);
        };
        let (kl, hl) = goals::head_after_assignments(&left.stmt);
        let (kr, hr) = goals::head_after_assignments(&right.stmt);
        let rnd = |h: Option<&crate::easycrypt::json::Instr>| {
            h.filter(|i| i.kind == "rnd")
                .and_then(|i| i.lvalue.as_ref())
                .map(|l| l.pp.clone())
        };
        let (x, y) = (rnd(hl), rnd(hr));
        let before = self.count();
        let sentences: Vec<String> = if synchronized {
            let (Some(x), Some(y)) = (x, y) else {
                return Ok(false);
            };
            if kl + kr > 0 {
                // `sp` left assignments before the sampling: `seq` would swallow them
                return self.seq_post_admit(idx).map(|()| true);
            }
            let post = format!("(#pre /\\ {x}{{1}} = {y}{{2}})");
            ["auto => />", "auto => /#", "auto"]
                .iter()
                .map(|close| format!("seq 1 1 : {post}; 1: {close}."))
                .collect()
        } else {
            let (n, m) = match (child.left.is_some(), child.right.is_some(), x, y) {
                (true, false, Some(_), _) => (1, 0),
                (false, true, _, Some(_)) => (0, 1),
                _ => return Ok(false),
            };
            ["auto => />", "auto => /#", "auto"]
                .iter()
                .map(|close| format!("seq {n} {m} : (#pre); 1: {close}."))
                .collect()
        };
        let mut applied = false;
        for sentence in &sentences {
            if self.attempt(&[sentence], Want::Full, |p| {
                p.count() == before && p.front().is_some_and(goals::is_program)
            })? {
                applied = true;
                break;
            }
        }
        if !applied {
            return Ok(false);
        }
        self.handle_child(idx, child)?;
        Ok(true)
    }

    fn seq_post_admit(&mut self, idx: usize) -> R<()> {
        let id = self.id_below(idx, &Part::Whole, DominoView::Verified);
        self.admit(AdmitReason::SeqPost, &id, "sampling", DominoView::Verified)
    }

    // ------------------------------------------------------------------
    // Leaves (§3.5)
    // ------------------------------------------------------------------

    fn leaf(&mut self, idx: usize) -> R<()> {
        let tree = self.tree;
        let pair = tree.pair_of_node.get(&idx).map(|&i| &tree.outcome.pairs[i]);
        self.leaf_of(idx, pair)
    }

    /// The leaf procedure (story 64): decide the exit path, reduce the programs to a formula
    /// with `auto`, then open that formula into its leaf parts. A leaf whose programs do not
    /// reduce to a formula is admitted whole. The leaf budget runs from the formula on.
    fn leaf_of(&mut self, node: usize, pair: Option<&PairRecord>) -> R<()> {
        self.as_role(Role::ExitPath, |p| p.decide_exit_path(pair))?;
        let before = self.count();
        if !self.as_role(Role::Reduce, |p| p.reduce_leaf("hpre"))? {
            let claim = self.whole_claim();
            return self.admit_ec_failed(node, &Part::Whole, claim);
        }
        if self.count() < before {
            return Ok(());
        }
        self.premises = vec!["hpre".to_string()];
        self.binders.clear();
        self.deadline = leaf_deadline(self.leaf_budget, std::time::Instant::now());
        let result = self.as_role(Role::Split, |p| p.open_part(node, pair, Part::Whole));
        self.deadline = None;
        result?;
        // the opening read goals at `head` depth: the walk after the leaf reads programs in full
        self.full_front()?;
        Ok(())
    }

    /// The side (1 or 2) of the first `if` left in the front goal's programs, side 1 first,
    /// and that `if`'s condition.
    fn first_exit_if(&self) -> Option<(u8, String)> {
        let first = |side: &crate::easycrypt::json::Side| {
            side.stmt
                .iter()
                .find(|i| i.kind == "if")
                .map(|i| match &i.cond {
                    Some(c) if !c.pp.is_empty() => c.pp.clone(),
                    _ => i.pp.trim_start_matches("if").to_string(),
                })
        };
        (1u8..)
            .zip(self.programs())
            .find_map(|(side, program)| first(program).map(|c| (side, c)))
    }

    /// The programs of the front goal: both sides of an `equiv`, side 1 first, or the one
    /// program of a `hoare`. Empty when the front goal is not a program goal.
    fn programs(&self) -> Vec<&crate::easycrypt::json::Side> {
        let Some(goal) = self.front() else {
            return Vec::new();
        };
        match (goals::program(goal), goals::sides(goal)) {
            (Some(p), _) => vec![p],
            (None, Some((l, r))) => vec![l, r],
            (None, None) => Vec::new(),
        }
    }

    /// Decides the `if`s left in the front goal's programs, one at a time: the first `if` of
    /// side 1, else of side 2, by `rcondt{i} ^if; 1: by auto.` or `rcondf`, the decision of
    /// [`exit_decisions`] first. Stops at the first `if` that neither decision takes (`auto`'s
    /// wp then takes it into the formula), and after as many decisions as the goal had `if`s.
    fn decide_exit_path(&mut self, pair: Option<&PairRecord>) -> R<()> {
        let bound: usize = self
            .programs()
            .iter()
            .map(|p| p.stmt.iter().filter(|i| i.kind == "if").count())
            .sum();
        for _ in 0..bound {
            let Some((side, cond)) = self.first_exit_if() else {
                return Ok(());
            };
            let aborts = pair.map(|p| match side {
                1 => p.left.terminal.is_abort,
                _ => p.right.terminal.is_abort,
            });
            if !self.decide_if(side, &cond, aborts)? {
                return Ok(());
            }
        }
        Ok(())
    }

    /// The first `if` of `side`, decided by the predicted decision, else by the other one:
    /// whether either was accepted with its side goal closed.
    fn decide_if(&mut self, side: u8, cond: &str, aborts: Option<bool>) -> R<bool> {
        for tactic in exit_decisions(cond, aborts) {
            let before = self.count();
            let sentence = format!("{tactic}{} ^if; 1: by auto.", self.judgement.side(side));
            if self.attempt(&[&sentence], Want::Status, |p| {
                p.count() == before && p.front().is_some_and(goals::is_program)
            })? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// `auto => &1 &2 <premise>.` on the leaf's program goal (`auto => &hr <premise> /=.` in a
    /// `hoare` judgement, whose `let`s would hide `side_inv_<C>`), then the invariant unfolded in
    /// the premise. Whether it gave a formula or closed the goal; `false` (with nothing kept)
    /// if `auto` failed or left a program goal.
    fn reduce_leaf(&mut self, premise: &str) -> R<bool> {
        let before = self.count();
        let sentence = match self.judgement {
            Judgement::Equiv => format!("auto => &1 &2 {premise}."),
            Judgement::Hoare | Judgement::Package => format!("auto => &hr {premise} /=."),
        };
        let reduced = self.attempt(&[&sentence], Want::Head, |p| {
            p.count() < before || (p.count() == before && p.front().is_some_and(goals::is_ambient))
        })?;
        if reduced && self.count() == before {
            self.unfold_premise(premise)?;
        }
        Ok(reduced)
    }

    /// Opens the front ambient goal, which belongs to `part`, until it is leaf parts: binders
    /// and premises are introduced (`/=` removes the `let`s and record projections), `inv` and
    /// the [`Self::part_ops`] unfolded (a claim operator makes the goal that claim's, and a
    /// claim that fails in Domino is admitted at once), and anything else is `do split` into
    /// bullets. A goal that nothing opens is a leaf part, which goes to [`Self::atom`].
    fn open_part(&mut self, node: usize, pair: Option<&PairRecord>, part: Part) -> R<()> {
        let mut part = part;
        for _ in 0..64 {
            if self
                .deadline
                .is_some_and(|d| std::time::Instant::now() >= d)
            {
                return self.admit_part(node, pair, &part, " (leaf time budget spent)");
            }
            let Some((step, now)) = self
                .front()
                .map(|goal| ambient_step(goal, &part, self.part_ops))
            else {
                return Ok(());
            };
            part = now;

            // §3.6: a part that fails in Domino is admitted without spending EasyCrypt time
            if let Some(p) = pair {
                if !matches!(part, Part::Whole) && pair_view(p, &part) == DominoView::Fails {
                    return self.admit_of_part(
                        &part,
                        AdmitReason::DominoFails,
                        &p.id,
                        &part.claim_label(),
                        DominoView::Fails,
                    );
                }
            }

            if step == Step::Split {
                return self.split_part(node, pair, &part);
            }
            if !self.open_step(step)? {
                return self.atom(node, pair, &part);
            }
        }
        self.atom(node, pair, &part)
    }

    /// One step of [`Self::open_part`] that keeps one goal: whether EasyCrypt accepted it.
    fn open_step(&mut self, step: Step) -> R<bool> {
        match step {
            Step::Intro(names) => {
                let sent = self.send(&format!("move => {names} /=."), Want::Head)?;
                if sent {
                    self.binders
                        .extend(names.split_whitespace().map(String::from));
                }
                Ok(sent)
            }
            Step::Premise(name) => {
                let sent = self.send(&format!("move => {name} /=."), Want::Head)?;
                if sent {
                    self.premises.push(name.clone());
                    // let the solver see through the invariant in the premise just introduced
                    self.unfold_premise(&name)?;
                }
                Ok(sent)
            }
            Step::Unfold(op) => self.send(&format!("rewrite /{op} /=."), Want::Head),
            Step::Split => Ok(false),
        }
    }

    /// `do split.`: each goal it gives is a bullet, opened again in `part`. If it gives one
    /// goal (or is refused), nothing is kept and the goal is a leaf part.
    fn split_part(&mut self, node: usize, pair: Option<&PairRecord>, part: &Part) -> R<()> {
        let before = self.count();
        if !self.attempt(&["do split."], Want::Head, |p| p.count() > before)? {
            return self.atom(node, pair, part);
        }
        // a premise a bullet introduces is that bullet's own
        let (premises, binders) = (self.premises.len(), self.binders.len());
        for _ in 0..=self.count() - before {
            let same = part.clone();
            self.bullet(|p| p.open_part(node, pair, same))?;
            self.premises.truncate(premises);
            self.binders.truncate(binders);
        }
        Ok(())
    }

    /// The part fallback sequence (story 65): `smt().`, `smt(<hints>).`, then the premises the
    /// leaf procedure introduced moved back and crushed (`move: <premises> => />; smt(<hints>).`,
    /// skipped when there are none), then the key case split ([`Self::key_case_split`]). Else
    /// an admit that keeps the unfoldings and introductions already made, with the last
    /// fallback's outcome.
    fn atom(&mut self, node: usize, pair: Option<&PairRecord>, part: &Part) -> R<()> {
        let hints = self.hint_sentence();
        let mut fallbacks = vec!["smt().".to_string(), hints.clone()];
        if !self.premises.is_empty() {
            fallbacks.push(format!("move: {} => />; {hints}", self.premises.join(" ")));
        }
        let mut outcome = None;
        for (k, sentence) in (1..).zip(&fallbacks) {
            let role = Role::PartFallback {
                n: k,
                part: part.claim_label(),
            };
            let closing = Closing::Fallback {
                k,
                of: PART_FALLBACKS,
            };
            let shown = sentence.trim_end_matches('.');
            self.last_smt = None;
            let closed = self.as_role(role, |p| {
                p.closing_attempt(closing, shown, |p| p.try_close(&[sentence]))
            })?;
            if closed {
                return Ok(());
            }
            outcome = self.last_smt;
        }
        if self.key_case_split(part, &hints)? {
            return Ok(());
        }
        self.admit_smt = self.last_smt.or(outcome);
        self.admit_part(node, pair, part, "")
    }

    /// Part fallback 4 (story 66): `case (b = k) => [->|?].` on each pair of
    /// [`goals::key_pairs`] in turn, each case a bullet, and `hints` at the end of each case.
    /// Kept only if every case closes; else everything is undone. It does not run (`false`,
    /// `last_smt` cleared) with no pair or more than [`goals::MAX_KEY_PAIRS`]; after it ran,
    /// `last_smt` is the outcome of its last `smt`.
    fn key_case_split(&mut self, part: &Part, hints: &str) -> R<bool> {
        self.last_smt = None;
        // the opening read the goal at `head` depth: the keys are deep in it
        self.full_front()?;
        let pairs = self
            .front()
            .map(|g| goals::key_pairs(&g.concl, &self.binders))
            .unwrap_or_default();
        if pairs.is_empty() || pairs.len() > goals::MAX_KEY_PAIRS {
            return Ok(false);
        }
        let role = Role::PartFallback {
            n: PART_FALLBACKS,
            part: part.claim_label(),
        };
        let closing = Closing::Fallback {
            k: PART_FALLBACKS,
            of: PART_FALLBACKS,
        };
        let shown = format!("case split on {} key(s)", pairs.len());
        self.as_role(role, |p| {
            p.closing_attempt(closing, &shown, |p| {
                let snap = p.snap();
                let closed = p.split_cases(&pairs, hints)?;
                if !closed {
                    let outcome = p.last_smt;
                    p.rollback(snap)?;
                    p.last_smt = outcome;
                }
                Ok(closed)
            })
        })
    }

    /// The cases of `pairs` on the front goal, as in [`Self::key_case_split`]: whether every
    /// case closed. Stops at the first case that does not; the caller undoes.
    fn split_cases(&mut self, pairs: &[goals::KeyPair], hints: &str) -> R<bool> {
        let Some((first, rest)) = pairs.split_first() else {
            let before = self.count();
            return Ok(self.send(hints, Want::Status)? && self.count() < before);
        };
        let before = self.count();
        let outcome = self.last_smt;
        let sent = self.send(
            &format!("case ({} = {}) => [->|?].", first.binder, first.key),
            Want::Head,
        )?;
        self.last_smt = outcome;
        if !sent || self.count() != before + 1 {
            return Ok(false);
        }
        let equal: Vec<_> = rest
            .iter()
            .filter(|p| p.binder != first.binder)
            .cloned()
            .collect();
        Ok(self.bullet(|p| p.split_cases(&equal, hints))?
            && self.bullet(|p| p.split_cases(rest, hints))?)
    }

    /// Admits the front goal as `part` of the pair's claims: the reason is what Domino itself
    /// concluded about the part.
    fn admit_part(
        &mut self,
        node: usize,
        pair: Option<&PairRecord>,
        part: &Part,
        note: &str,
    ) -> R<()> {
        let claim = format!("{}{note}", part.claim_label());
        match pair {
            Some(p) => {
                let view = pair_view(p, part);
                let reason = match view {
                    DominoView::Fails => AdmitReason::DominoFails,
                    DominoView::Verified => AdmitReason::DominoVerifiedEcFailed,
                    _ => AdmitReason::DominoInconclusive,
                };
                self.admit_of_part(part, reason, &p.id, &claim, view)
            }
            None => self.admit_ec_failed(node, part, &claim),
        }
    }

    // ------------------------------------------------------------------
    // One oracle (§3.2)
    // ------------------------------------------------------------------

    /// Proves the oracle's `equivF` goal, which is in front: `proc; inline.`, the router
    /// prelude by construction, then the joint tree from its root. `align` is given the goal
    /// after `proc; inline.` and returns the descriptions of the alignment's mismatches
    /// ([`Self::mismatches`]); with any, the oracle is proved by the fallback.
    pub(super) fn oracle(&mut self, align: impl FnOnce(&Goal) -> Vec<String>) -> R<()> {
        self.script.enter_bullet(self.count());
        if let Some(live) = &self.live {
            live.node_entered("router prelude", "router", vec![], None);
            live.node_started("router", self.tree.outcome.tree.nodes.len());
        }
        let prelude = SentenceCtx {
            oracle: Some(self.oracle.to_string()),
            node: None,
            role: Role::Structure,
        };
        let result = self.in_context(prelude, |p| p.oracle_inner(align));
        if let Some(live) = &self.live {
            live.node_left();
        }
        self.script.leave_bullet();
        result
    }

    fn oracle_inner(&mut self, align: impl FnOnce(&Goal) -> Vec<String>) -> R<()> {
        if !self.send("proc; inline.", Want::Full)? {
            self.admit(
                AdmitReason::ProgramMismatch,
                "N0",
                "proc; inline.",
                DominoView::NotApplicable,
            )?;
            return Ok(());
        }
        self.mismatches = self.front().map(align).unwrap_or_default();
        match self.judgement {
            Judgement::Hoare => return self.hoare_prelude(),
            // a package procedure has no router: the package tree begins at its first statement
            Judgement::Package => return self.prove_node(0),
            Judgement::Equiv => {}
        }
        // the router prelude, by construction: `sp`, `if`, then the condition, the guarded body
        // (where lockstep begins) and the case where both sides already aborted
        let after_inline = self.snap();
        let before = self.count();
        let prelude = self.sp_front()?
            && self.send("if.", Want::Full)?
            && self.count() == before + 2
            && self.is_if_split();
        if !prelude {
            self.rollback(after_inline)?;
            self.stats.fallbacks += 1;
            return self.prove_blind(0, 64);
        }
        self.bullet(|p| p.close_side_goal(0, "router-condition", true))?;
        if self.mismatches.is_empty() {
            self.bullet(|p| p.prove_node(0))?;
        } else {
            self.stats.fallbacks += 1;
            self.bullet(|p| p.prove_blind(0, 64))?;
        }
        self.bullet(|p| {
            if p.quick_close_program()? {
                return Ok(());
            }
            p.close_side_goal(0, "both-aborted", true)
        })
    }

    /// The router prelude of a side-invariant lemma (story 69): `sp`, then `if.` on
    /// `if (!abort_flag)` gives the arm where the game has not aborted (one-sided execution
    /// begins there), then the arm where it has, which keeps the state: the quick close, else
    /// the fallbacks.
    fn hoare_prelude(&mut self) -> R<()> {
        let after_inline = self.snap();
        let before = self.count();
        let prelude = self.sp_front()?
            && self.send("if.", Want::Full)?
            && self.count() == before + 1
            && self.front().is_some_and(goals::is_program);
        if !prelude {
            self.rollback(after_inline)?;
            self.stats.fallbacks += 1;
            return self.prove_blind(0, 64);
        }
        self.bullet(|p| p.prove_node(0))?;
        self.bullet(|p| {
            if p.quick_close_program()? {
                return Ok(());
            }
            p.close_side_goal(0, "already-aborted", true)
        })
    }

    // ------------------------------------------------------------------
    // The fallback (§3.4): the PDF's trial procedure, without the joint tree
    // ------------------------------------------------------------------

    /// Proves the front goal by trying, at each program head, what `BranchingAlgorithm.pdf`
    /// does: `rcondt`/`rcondf` on either side, `if`, `if{1}`/`if{2}`, `seq` at samplings.
    /// Each trial runs under `undo`. Ends in an admit with reason `program-mismatch`.
    fn prove_blind(&mut self, node: usize, budget: usize) -> R<()> {
        let admit_mismatch = |p: &mut Self| {
            let id = format!("N{node}");
            p.admit(
                AdmitReason::ProgramMismatch,
                &id,
                "program",
                DominoView::Inconclusive,
            )
        };
        if budget == 0 || !self.front().is_some_and(goals::is_program) {
            return admit_mismatch(self);
        }
        if self.quick_close_program()? {
            return Ok(());
        }
        if !self.sp_front()? {
            return admit_mismatch(self);
        }
        if self.judgement.one_program() {
            // no trial procedure for one program: its leaf, or an admit
            let empty = self
                .front()
                .and_then(goals::program)
                .is_some_and(|p| p.stmt.is_empty());
            return if empty {
                self.leaf_of(node, None)
            } else {
                admit_mismatch(self)
            };
        }
        let Some((left, right)) = self.front().and_then(goals::sides) else {
            return admit_mismatch(self);
        };
        if left.stmt.is_empty() && right.stmt.is_empty() {
            return self.leaf_of(node, None);
        }
        let head = |s: &crate::easycrypt::json::Side| s.stmt.first().map(|i| i.kind.clone());
        let (hl, hr) = (head(left), head(right));
        let rnd_name = |s: &crate::easycrypt::json::Side| {
            s.stmt
                .first()
                .and_then(|i| i.lvalue.as_ref())
                .map(|l| l.pp.clone())
        };
        let (xl, xr) = (rnd_name(left), rnd_name(right));
        let before = self.count();

        // 1./2. a side whose condition is decided
        let mut trials: Vec<(String, u8)> = Vec::new(); // (sentence, kind of continuation)
        for (side, h) in [(1, &hl), (2, &hr)] {
            if h.as_deref() == Some("if") {
                for tactic in ["rcondt", "rcondf"] {
                    trials.push((format!("{tactic}{{{side}}} ^if; 1: auto => /#."), 0));
                }
            }
        }
        for (sentence, _) in &trials {
            if self.attempt(&[sentence], Want::Full, |p| p.count() == before)? {
                return self.prove_blind(node, budget - 1);
            }
        }
        // 3. `if`: condition, then, else
        if hl.as_deref() == Some("if") && hr.as_deref() == Some("if") {
            let snap = self.snap();
            if self.send("if.", Want::Full)?
                && self.count() == before + 2
                && self.front().is_some_and(goals::is_ambient)
            {
                self.bullet(|p| p.close_side_goal(node, "branch-condition", false))?;
                self.bullet(|p| p.prove_blind(node, budget - 1))?;
                return self.bullet(|p| p.prove_blind(node, budget - 1));
            }
            self.rollback(snap)?;
        }
        // 4. `if{1}` / `if{2}`
        for (side, h) in [(1, &hl), (2, &hr)] {
            if h.as_deref() != Some("if") {
                continue;
            }
            let snap = self.snap();
            if self.send(&format!("if{{{side}}}."), Want::Full)?
                && self.two_programs_in_front(before)
            {
                self.bullet(|p| p.prove_blind(node, budget - 1))?;
                return self.bullet(|p| p.prove_blind(node, budget - 1));
            }
            self.rollback(snap)?;
        }
        // 5. samplings
        let seqs: Vec<String> = match (&xl, &xr, hl.as_deref(), hr.as_deref()) {
            (Some(x), Some(y), Some("rnd"), Some("rnd")) => {
                vec![format!(
                    "seq 1 1 : (#pre /\\ {x}{{1}} = {y}{{2}}); 1: auto => /#."
                )]
            }
            (Some(_), _, Some("rnd"), _) => vec!["seq 1 0 : (#pre); 1: auto => /#.".into()],
            (_, Some(_), _, Some("rnd")) => vec!["seq 0 1 : (#pre); 1: auto => /#.".into()],
            _ => vec![],
        };
        for sentence in &seqs {
            if self.attempt(&[sentence], Want::Full, |p| p.count() == before)? {
                return self.prove_blind(node, budget - 1);
            }
        }
        admit_mismatch(self)
    }
}

/// When a leaf that starts being split by meaning at `now` runs out of time: `None` when the
/// user gave no leaf budget. A budget of zero is a deadline of `now`.
pub(super) fn leaf_deadline(
    budget: Option<Duration>,
    now: std::time::Instant,
) -> Option<std::time::Instant> {
    budget.map(|b| now + b)
}
