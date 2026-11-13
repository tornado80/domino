// SPDX-License-Identifier: MIT OR Apache-2.0

//! The shape of a program head for the reduction walk (story 105, ADR 0024 decision 2).
//!
//! The reduction walk (story 106) proves a reduction's oracle lemma one program head at a time
//! and picks the step from the shape of the two first statements, [`classify`]. The rules read
//! only what EasyCrypt prints: a condition is a [`Node`](crate::easycrypt::json::Node) with its
//! text in `pp`, so the recognizers read text, after dropping the type annotations `<:…>`.
//!
//! `assumption` is the assumption theory of the reduction, `Comp_MAC` for `Red_H7_1_H7_0`.
//!
//! [`prove_reduction`] is the walk itself (story 106, `docs/proving-algorithm.md` §10): at each
//! program head it sends the one step the shape calls for, and admits a shape it does not
//! expect (`reduction-mismatch`) or a side goal nothing closed (`reduction-ec-failed`).

use crate::easycrypt::json::Instr;
use crate::easycrypt::session::Want;

use super::driver::{exit_decisions, AdmitReason, DominoView, Part, Prover, R};
use super::goals::{self, synchronized_sampling, SyncSampling};

/// What the reduction walk keeps in the prover: the assumption theory `<A>` and the arm path of
/// the goal in front (`R`, `R.t`, `R.t.e`), which is the id of its admits.
#[derive(Debug, Clone, Default)]
pub(crate) struct Walk {
    pub assumption: String,
    pub arm: String,
}

/// Proves a reduction's oracle lemma after `proc; inline *.` (§10.1), from the arm `R`.
pub(super) fn prove_reduction(p: &mut Prover<'_>) -> R<()> {
    walk(p, "R", true)
}

/// Proves the program goal in front, which is the arm `path`.
fn walk(p: &mut Prover<'_>, path: &str, arm_start: bool) -> R<()> {
    p.walk.arm = path.to_string();
    if arm_start && p.quick_close_program()? {
        return Ok(());
    }
    // no `sp` here (story 108 §3.2): the heads are read after the leading assignments, and
    // only a two-sided step (`if.`, `seq`) sends `sp` before it
    if !p.front().is_some_and(goals::is_program) {
        return p.admit_reduction(AdmitReason::ReductionMismatch, "not-a-program");
    }
    // the heads in full: a stub would hide a statement or a variable of `#pre` (story 104)
    p.full_front()?;
    let Some((left, right)) = p.front().and_then(goals::sides) else {
        return p.admit_reduction(AdmitReason::ReductionMismatch, "not-a-program-pair");
    };
    let conds = [head_cond(&left.stmt), head_cond(&right.stmt)];
    match classify(&left.stmt, &right.stmt, &p.walk.assumption) {
        Head::Leaf => leaf(p, arm_start),
        Head::AssumptionGuard => step(p, path, "rcondt{2} ^if.", "assumption-guard", None),
        Head::TailBranch => tail_branch(p, path),
        Head::ExitGuards => exit_guards(p, path, &conds),
        Head::Branches => branches(p, path),
        Head::Samplings { .. } => samplings(p, path),
        Head::Mismatch(m) => p.admit_reduction(AdmitReason::ReductionMismatch, &m.claim()),
    }
}

/// `stmt` from its head on: its leading assignments skipped.
fn from_head(stmt: &[Instr]) -> &[Instr] {
    &stmt[goals::leading_assignments(stmt)..]
}

/// The condition of the `if` at the head of `stmt`, as EasyCrypt prints it.
fn head_cond(stmt: &[Instr]) -> String {
    from_head(stmt)
        .first()
        .and_then(|i| i.cond.as_ref())
        .map_or_else(String::new, |c| c.pp.clone())
}

/// Both programs are empty: the quick close (unless the arm's start tried it), then the leaf
/// procedure with no pair, whose failed parts admit `reduction-ec-failed`.
fn leaf(p: &mut Prover<'_>, arm_start: bool) -> R<()> {
    if !arm_start && p.quick_close_program()? {
        return Ok(());
    }
    p.leaf_of(0, None)
}

/// A structural step whose shape is right: `tactic` leaves its side goal in front of the program
/// goal. A refusal admits `reduction-mismatch` with `refused` (else `claim`); the side goal is a
/// bullet ([`side_goal`]), and the program goal goes on in the next.
fn step(p: &mut Prover<'_>, path: &str, tactic: &str, claim: &str, refused: Option<&str>) -> R<()> {
    let before = p.count();
    if !p.send(tactic, Want::Full)? {
        return p.admit_reduction(AdmitReason::ReductionMismatch, refused.unwrap_or(claim));
    }
    if p.count() == before {
        // EasyCrypt discharged the side goal itself
        return walk(p, path, false);
    }
    p.bullet(|p| side_goal(p, path, claim))?;
    p.bullet(|p| walk(p, path, false))
}

/// A side goal of a step: `auto => />.`, then [`Prover::close_side_goal`], which admits
/// `reduction-ec-failed` on a reduction.
fn side_goal(p: &mut Prover<'_>, path: &str, claim: &str) -> R<()> {
    p.walk.arm = path.to_string();
    if p.try_close(&["auto => />."])? {
        return Ok(());
    }
    p.close_side_goal(0, claim, false)
}

/// The assumption game's tail branch: decided on side 2 in the order of [`decision_order`]
/// (`rcondf` first); else `rcondt{2} ^if.` as a step; refused: an undecided tail branch.
fn tail_branch(p: &mut Prover<'_>, path: &str) -> R<()> {
    if decide(p, 2, ["rcondf", "rcondt"], false)?.is_some() {
        return walk(p, path, false);
    }
    step(
        p,
        path,
        "rcondt{2} ^if.",
        "tail-branch",
        Some("undecided-tail-branch"),
    )
}

/// The sentences `d{side} ^if; 1: auto => <close>.` of a decision, each with its direction `d`,
/// `dirs[0]` the predicted one (story 108 §3.1). On its own the cheap closer `/>` goes first in
/// both directions, then `/#`; `follow`ing a decision already made on the other side, `dirs[0]`
/// is tried with both closers before the other direction.
pub(crate) fn decision_order(
    side: u8,
    dirs: [&'static str; 2],
    follow: bool,
) -> Vec<(&'static str, String)> {
    let [a, b] = dirs;
    let order = if follow {
        [(a, "/>"), (a, "/#"), (b, "/>"), (b, "/#")]
    } else {
        [(a, "/>"), (b, "/>"), (a, "/#"), (b, "/#")]
    };
    order
        .into_iter()
        .map(|(d, close)| (d, format!("{d}{{{side}}} ^if; 1: auto => {close}.")))
        .collect()
}

/// The directions of a decision that repeats `d`: `d` first, then the other one.
fn following(d: &str) -> [&'static str; 2] {
    if d == "rcondt" {
        ["rcondt", "rcondf"]
    } else {
        ["rcondf", "rcondt"]
    }
}

/// Decides the `if` at the head of `side` by the sentences of [`decision_order`]: the direction
/// of the first one accepted with its side goal closed.
fn decide(
    p: &mut Prover<'_>,
    side: u8,
    dirs: [&'static str; 2],
    follow: bool,
) -> R<Option<&'static str>> {
    let before = p.count();
    for (d, sentence) in decision_order(side, dirs, follow) {
        if p.attempt(&[&sentence], Want::Full, |p| {
            p.count() == before && p.front().is_some_and(goals::is_program)
        })? {
            return Ok(Some(d));
        }
    }
    Ok(None)
}

/// Two exit guards: side 1 in the order of [`exit_decisions`], then side 2 repeating side 1's
/// decision first (both sides run the same code). A side that no decision takes undoes both,
/// and the guards are split by `if.` (not a mismatch).
fn exit_guards(p: &mut Prover<'_>, path: &str, conds: &[String; 2]) -> R<()> {
    let snap = p.snap();
    let Some(left) = decide(p, 1, exit_decisions(&conds[0], None), false)? else {
        p.rollback(snap)?;
        return branches(p, path);
    };
    if decide(p, 2, following(left), true)?.is_none() {
        p.rollback(snap)?;
        return branches(p, path);
    }
    walk(p, path, false)
}

/// Two `if`s: `if.`, its condition goal as a side goal, then the *then* arm `<path>.t` and the
/// *else* arm `<path>.e`, each starting with the quick close.
fn branches(p: &mut Prover<'_>, path: &str) -> R<()> {
    if !p.sp_front()? {
        return p.admit_reduction(AdmitReason::ReductionMismatch, "sp");
    }
    let before = p.count();
    if !p.attempt(&["if."], Want::Full, |p| p.count() == before + 2)? {
        return p.admit_reduction(AdmitReason::ReductionMismatch, "if-conditions");
    }
    p.bullet(|p| side_goal(p, path, "if-conditions"))?;
    p.bullet(|p| walk(p, &format!("{path}.t"), true))?;
    p.bullet(|p| walk(p, &format!("{path}.e"), true))
}

/// Two samplings: `seq 1 1 : (#pre /\ x{1} = y{2}).` as a step, unless `#pre` speaks about a
/// sampled variable (§10.3): then a `seq-post` admit and no `seq`.
fn samplings(p: &mut Prover<'_>, path: &str) -> R<()> {
    // the `sp` of the sampling first: story 104's check reads `#pre` after it
    if !p.sp_front()? {
        return p.admit_reduction(AdmitReason::ReductionMismatch, "sp");
    }
    match p.front().and_then(synchronized_sampling) {
        Some(SyncSampling::Seq(post)) => {
            step(p, path, &format!("seq 1 1 : {post}."), "seq-coupling", None)
        }
        Some(SyncSampling::Admit(claim)) => p.admit_reduction(AdmitReason::SeqPost, &claim),
        None => p.admit_reduction(AdmitReason::ReductionMismatch, "seq-coupling"),
    }
}

impl Prover<'_> {
    /// Closes the front goal with an admit of the reduction walk: the arm path as id, no Domino
    /// view.
    pub(super) fn admit_reduction(&mut self, reason: AdmitReason, claim: &str) -> R<()> {
        self.admit_reduction_part(&Part::Whole, reason, claim)
    }

    /// [`Self::admit_reduction`] of `part` of a leaf's claims.
    pub(super) fn admit_reduction_part(
        &mut self,
        part: &Part,
        reason: AdmitReason,
        claim: &str,
    ) -> R<()> {
        let arm = self.walk.arm.clone();
        self.admit_of_part(part, reason, &arm, claim, DominoView::NotApplicable)
    }
}

/// The shape of the two program heads, read after the leading assignments (an assignment is
/// not a head; story 108 §3.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Head {
    /// Both programs are empty.
    Leaf,
    /// The right head is the guard `if (!<A>.Game_<C>.abort_flag)` of the assumption game.
    AssumptionGuard,
    /// The right head is the assumption game's tail branch (`if (x = None) <A>…abort_flag <- true`).
    TailBranch,
    /// Two exit guards: translation's own `if`s, decided by `rcondt`/`rcondf`.
    ExitGuards,
    /// Two `if`s, at least one a real decision.
    Branches,
    /// Two samplings, the lvalues as printed.
    Samplings { x: String, y: String },
    /// Heads the walk does not step through.
    Mismatch(Mismatch),
}

/// Why two heads do not fit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Mismatch {
    LeftOnlyIf,
    RightOnlyIf,
    OneSidedSampling,
    Loop,
    /// The kinds of the two heads (`none` for an empty program).
    Heads {
        left: String,
        right: String,
    },
}

impl Mismatch {
    /// The claim text of the admit.
    pub(crate) fn claim(&self) -> String {
        match self {
            Mismatch::LeftOnlyIf => "left-only-if".to_string(),
            Mismatch::RightOnlyIf => "right-only-if".to_string(),
            Mismatch::OneSidedSampling => "one-sided-sampling".to_string(),
            Mismatch::Loop => "loop".to_string(),
            Mismatch::Heads { left, right } => format!("heads {left}/{right}"),
        }
    }
}

/// The shape of the heads of `left` and `right` (story 105 §3, the first matching rule wins).
pub(crate) fn classify(left: &[Instr], right: &[Instr], assumption: &str) -> Head {
    let (l, r) = (from_head(left).first(), from_head(right).first());
    let (lk, rk) = (kind_of(l), kind_of(r));
    if l.is_none() && r.is_none() {
        return Head::Leaf;
    }
    if r.is_some_and(|r| is_assumption_guard(r, assumption)) {
        return Head::AssumptionGuard;
    }
    if r.is_some_and(|r| is_tail_branch(r, assumption)) {
        return Head::TailBranch;
    }
    if lk == "while" || rk == "while" {
        return Head::Mismatch(Mismatch::Loop);
    }
    classify_pair(l, r)
}

fn kind_of(instr: Option<&Instr>) -> &str {
    instr.map_or("none", |i| i.kind.as_str())
}

/// Rules 6 to 12, for heads that are neither guards of the assumption nor loops.
fn classify_pair(l: Option<&Instr>, r: Option<&Instr>) -> Head {
    let (lk, rk) = (kind_of(l), kind_of(r));
    match (l, r) {
        (Some(l), Some(r)) if lk == "if" && rk == "if" => {
            if is_exit_guard(l) && is_exit_guard(r) {
                Head::ExitGuards
            } else {
                Head::Branches
            }
        }
        (Some(l), Some(r)) if lk == "rnd" && rk == "rnd" => Head::Samplings {
            x: lvalue_pp(l),
            y: lvalue_pp(r),
        },
        _ if lk == "if" => Head::Mismatch(Mismatch::LeftOnlyIf),
        _ if rk == "if" => Head::Mismatch(Mismatch::RightOnlyIf),
        _ if lk == "rnd" || rk == "rnd" => Head::Mismatch(Mismatch::OneSidedSampling),
        _ => Head::Mismatch(Mismatch::Heads {
            left: lk.to_string(),
            right: rk.to_string(),
        }),
    }
}

fn lvalue_pp(instr: &Instr) -> String {
    instr
        .lvalue
        .as_ref()
        .map_or_else(String::new, |lv| lv.pp.clone())
}

/// An `if` whose condition is `!<A>.Game_<C>.abort_flag`.
pub(crate) fn is_assumption_guard(instr: &Instr, assumption: &str) -> bool {
    if_condition(instr).is_some_and(|c| {
        c.strip_prefix('!')
            .is_some_and(|flag| is_game_flag(strip_parens(flag.trim()), assumption))
    })
}

/// An `if (<x> = None…)` whose *then* block is exactly `<A>.Game_<C>.abort_flag <- true` and whose
/// *else* block is empty.
pub(crate) fn is_tail_branch(instr: &Instr, assumption: &str) -> bool {
    let Some(cond) = if_condition(instr) else {
        return false;
    };
    let tests_none = cond
        .split_once(" = ")
        .is_some_and(|(x, rhs)| is_name(x.trim()) && rhs.trim() == "None");
    let [then] = instr.then_block.as_slice() else {
        return false;
    };
    tests_none && instr.else_block.is_empty() && sets_game_flag(then, assumption)
}

/// An `if` whose condition reads only translation locals (`ec_…`), abort flags, `None`, `true`,
/// `false`, and the operators `!`, `=`, `<>`.
pub(crate) fn is_exit_guard(instr: &Instr) -> bool {
    let Some(cond) = if_condition(instr) else {
        return false;
    };
    let mut rest = cond.as_str();
    while let Some(c) = rest.chars().next() {
        let len = if is_name_char(c) {
            let name_len = rest.find(|c| !is_name_char(c)).unwrap_or(rest.len());
            if !is_exit_name(&rest[..name_len]) {
                return false;
            }
            name_len
        } else if rest.starts_with("<>") {
            2
        } else if matches!(c, '!' | '=' | '(' | ')') || c.is_whitespace() {
            c.len_utf8()
        } else {
            return false;
        };
        rest = &rest[len..];
    }
    true
}

fn is_exit_name(name: &str) -> bool {
    matches!(name, "None" | "true" | "false")
        || name.starts_with("ec_") && !name.contains('.')
        || name == "abort_flag"
        || name.ends_with(".abort_flag")
}

/// The condition of an `if`, its type annotations dropped and its outer parentheses removed.
fn if_condition(instr: &Instr) -> Option<String> {
    if instr.kind != "if" {
        return None;
    }
    let text = drop_type_annotations(&instr.cond.as_ref()?.pp);
    Some(strip_parens(text.trim()).to_string())
}

/// `x = None<:bits_n * bits_n>` → `x = None`. Nested `<…>` inside an annotation are skipped.
fn drop_type_annotations(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("<:") {
        out.push_str(&rest[..start]);
        let mut depth = 0usize;
        let mut end = None;
        let mut prev = ' ';
        for (i, c) in rest[start..].char_indices() {
            let arrow = prev == '-';
            prev = c;
            match c {
                '<' => depth += 1,
                '>' if !arrow => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(start + i + 1);
                        break;
                    }
                }
                _ => {}
            }
        }
        // an annotation that never closes: keep the text, so no name hides in it
        let Some(end) = end else {
            out.push_str(&rest[start..]);
            return out;
        };
        rest = &rest[end..];
    }
    out.push_str(rest);
    out
}

fn strip_parens(mut text: &str) -> &str {
    while let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        if !balanced(inner) {
            break;
        }
        text = inner.trim();
    }
    text
}

fn balanced(text: &str) -> bool {
    let mut depth = 0i32;
    for c in text.chars() {
        depth += match c {
            '(' => 1,
            ')' => -1,
            _ => 0,
        };
        if depth < 0 {
            return false;
        }
    }
    depth == 0
}

fn is_name_char(c: char) -> bool {
    c.is_alphanumeric() || matches!(c, '_' | '.' | '\'')
}

fn is_name(text: &str) -> bool {
    !text.is_empty() && text.chars().all(is_name_char)
}

/// `<A>.Game_<C>.abort_flag` (also with `Top.` in front).
fn is_game_flag(text: &str, assumption: &str) -> bool {
    let text = text.strip_prefix("Top.").unwrap_or(text);
    text.strip_prefix(assumption)
        .and_then(|t| t.strip_prefix(".Game_"))
        .and_then(|t| t.strip_suffix(".abort_flag"))
        .is_some_and(|c| !c.is_empty() && is_name(c) && !c.contains('.'))
}

/// An assignment `<A>.Game_<C>.abort_flag <- true`.
fn sets_game_flag(instr: &Instr, assumption: &str) -> bool {
    instr.kind == "asgn"
        && instr
            .pp
            .trim()
            .trim_end_matches(';')
            .split_once("<-")
            .is_some_and(|(lv, rhs)| is_game_flag(lv.trim(), assumption) && rhs.trim() == "true")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::easycrypt::json::{parse_response, Instr};

    const A: &str = "Comp_MAC";

    fn sides(json: &str) -> (Vec<Instr>, Vec<Instr>) {
        let response = parse_response(json).unwrap();
        let concl = &response.proof.unwrap().front.unwrap().concl;
        (
            concl.left.as_ref().unwrap().stmt.clone(),
            concl.right.as_ref().unwrap().stmt.clone(),
        )
    }

    macro_rules! goal {
        ($name:literal) => {
            sides(include_str!(concat!(
                "../../../testdata/easycrypt/reduction-walk-goals/",
                $name
            )))
        };
    }

    #[test]
    fn the_router_guards_at_the_root_are_exit_guards() {
        let (l, r) = goal!("root.json");
        assert_eq!(classify(&l, &r, A), Head::ExitGuards);
    }

    #[test]
    fn the_nonce_is_a_synchronized_sampling() {
        let (l, r) = goal!("nonce.json");
        let x = "ni1".to_string();
        assert_eq!(classify(&l, &r, A), Head::Samplings { x: x.clone(), y: x });
    }

    #[test]
    fn the_guard_around_init_is_an_assumption_guard() {
        let (l, r) = goal!("assumption-guard.json");
        assert!(is_assumption_guard(&r[0], A));
        assert!(!is_assumption_guard(&r[0], "Comp_H7"));
        let mut parens = r[0].clone();
        parens.cond.as_mut().unwrap().pp = "!(Comp_MAC.Game_MAC.abort_flag)".to_string();
        assert!(is_assumption_guard(&parens, A));
        assert_eq!(classify(&l, &r, A), Head::AssumptionGuard);
    }

    #[test]
    fn the_assumption_games_tail_branch_is_recognized() {
        let (l, r) = goal!("tail-branch.json");
        assert!(is_tail_branch(&r[0], A));
        assert_eq!(classify(&l, &r, A), Head::TailBranch);
    }

    #[test]
    fn the_reduction_routers_tail_branch_is_not_the_assumptions() {
        let (_, r) = goal!("root.json");
        // `if (ec_result = None<:…>) Red_H7_1_H7_0.abort_flag <- true`
        assert!(!is_tail_branch(&r[1], A));
        assert!(!is_tail_branch(&r[1], "Red_H7_1_H7_0"));
        assert!(is_exit_guard(&r[1]));
    }

    #[test]
    fn a_tail_branch_with_an_else_block_or_two_statements_is_not_one() {
        let (_, r) = goal!("tail-branch.json");
        let mut with_else = r[0].clone();
        with_else.else_block = with_else.then_block.clone();
        assert!(!is_tail_branch(&with_else, A));
        let mut two = r[0].clone();
        two.then_block.push(two.then_block[0].clone());
        assert!(!is_tail_branch(&two, A));
        let mut trailing = r[0].clone();
        trailing.cond.as_mut().unwrap().pp = "ec_result4 = None<:unit> \\/ b".to_string();
        assert!(!is_tail_branch(&trailing, A));
    }

    #[test]
    fn a_package_variable_tested_against_none_is_a_real_decision() {
        let (l, r) = goal!("mac-key.json");
        assert!(!is_exit_guard(&l[0]));
        assert_eq!(classify(&l, &r, A), Head::Branches);
    }

    #[test]
    fn a_table_lookup_is_not_an_exit_guard() {
        let (l, r) = goal!("prf-table.json");
        assert!(!is_exit_guard(&l[0]));
        assert_eq!(classify(&l, &r, A), Head::Branches);
    }

    #[test]
    fn done_flags_and_call_results_are_exit_guards() {
        let (_, r) = goal!("tail-branch.json");
        assert!(is_exit_guard(&r[1])); // `if (!ec_done0)`
        let mut i = r[1].clone();
        i.cond.as_mut().unwrap().pp = "ec_r10 <> None<:bits_n>".to_string();
        assert!(is_exit_guard(&i));
        i.cond.as_mut().unwrap().pp = "ec_r10 <> Some x".to_string();
        assert!(!is_exit_guard(&i));
    }

    #[test]
    fn a_loop_on_either_side_is_a_mismatch() {
        let (l, r) = goal!("mac-key.json");
        let mut lw = l.clone();
        lw[0].kind = "while".to_string();
        assert_eq!(classify(&lw, &r, A), Head::Mismatch(Mismatch::Loop));
        assert_eq!(classify(&l, &lw, A), Head::Mismatch(Mismatch::Loop));
        assert_eq!(Mismatch::Loop.claim(), "loop");
    }

    #[test]
    fn an_if_on_one_side_only_is_a_mismatch() {
        let (l, r) = goal!("mac-key.json");
        let (nonce, _) = goal!("nonce.json");
        let left_only = classify(&l, &nonce, A);
        assert_eq!(left_only, Head::Mismatch(Mismatch::LeftOnlyIf));
        let right_only = classify(&[], &r, A);
        assert_eq!(right_only, Head::Mismatch(Mismatch::RightOnlyIf));
        assert_eq!(Mismatch::LeftOnlyIf.claim(), "left-only-if");
        assert_eq!(Mismatch::RightOnlyIf.claim(), "right-only-if");
    }

    #[test]
    fn a_sampling_on_one_side_only_is_a_mismatch() {
        let (l, r) = goal!("nonce.json");
        let removed = classify(&l, &r[1..1], A);
        assert_eq!(removed, Head::Mismatch(Mismatch::OneSidedSampling));
        let (asg, _) = goal!("tail-branch.json");
        let other = classify(&asg, &r, A);
        assert_eq!(other, Head::Mismatch(Mismatch::OneSidedSampling));
        assert_eq!(Mismatch::OneSidedSampling.claim(), "one-sided-sampling");
    }

    #[test]
    fn other_heads_are_a_mismatch_with_both_kinds() {
        let (l, _) = goal!("assumption-guard.json"); // a call
        let (asg, _) = goal!("tail-branch.json"); // only an assignment: no head
        let head = classify(&asg, &l, A);
        let heads = Mismatch::Heads {
            left: "none".to_string(),
            right: "call".to_string(),
        };
        assert_eq!(head, Head::Mismatch(heads.clone()));
        assert_eq!(heads.claim(), "heads none/call");
        let none = classify(&l, &asg, A);
        assert_eq!(
            none,
            Head::Mismatch(Mismatch::Heads {
                left: "call".to_string(),
                right: "none".to_string()
            })
        );
    }

    #[test]
    fn two_empty_programs_are_a_leaf() {
        assert_eq!(classify(&[], &[], A), Head::Leaf);
    }

    #[test]
    fn type_annotations_and_outer_parentheses_are_dropped() {
        assert_eq!(
            drop_type_annotations("ec_result = None<:bits_n * (int -> bool) option>"),
            "ec_result = None"
        );
        assert_eq!(strip_parens("((a) = (b))"), "(a) = (b)");
        assert_eq!(strip_parens("(a) = (b)"), "(a) = (b)");
        assert!(is_game_flag("Top.Comp_MAC.Game_MAC.abort_flag", A));
        assert!(!is_game_flag("Comp_MAC.Game_MAC.X.abort_flag", A));
        assert_eq!(drop_type_annotations("x = None<:int"), "x = None<:int");
    }

    /// Story 108 §3.2: the heads are read after the leading assignments, as `sp` would leave them.
    #[test]
    fn leading_assignments_do_not_change_the_shape_of_the_heads() {
        let (asg, _) = goal!("tail-branch.json");
        assert_eq!(asg[0].kind, "asgn");
        let with = |stmt: &[Instr]| [asg.clone(), asg.clone(), stmt.to_vec()].concat();
        for name in [
            "root.json",
            "nonce.json",
            "assumption-guard.json",
            "tail-branch.json",
            "mac-key.json",
        ] {
            let (l, r) = sides(
                &std::fs::read_to_string(format!(
                    "{}/testdata/easycrypt/reduction-walk-goals/{name}",
                    env!("CARGO_MANIFEST_DIR")
                ))
                .unwrap(),
            );
            let bare = classify(&l, &r, A);
            assert_eq!(classify(&with(&l), &with(&r), A), bare, "{name}");
            assert_eq!(head_cond(&with(&l)), head_cond(&l), "{name}");
        }
        assert_eq!(classify(&with(&[]), &asg, A), Head::Leaf);
    }

    /// Story 108 §3.1 item 1: `/>` in both directions before any `/#`, the predicted one first.
    #[test]
    fn a_decision_tries_the_cheap_closer_in_both_directions_first() {
        let order: Vec<String> = decision_order(1, ["rcondf", "rcondt"], false)
            .into_iter()
            .map(|(_, s)| s)
            .collect();
        assert_eq!(
            order,
            [
                "rcondf{1} ^if; 1: auto => />.",
                "rcondt{1} ^if; 1: auto => />.",
                "rcondf{1} ^if; 1: auto => /#.",
                "rcondt{1} ^if; 1: auto => /#.",
            ]
        );
    }

    /// Story 108 §3.1 item 2: side 2 repeats side 1's decision with both closers first.
    #[test]
    fn the_right_exit_guard_repeats_the_left_decision_first() {
        let order = decision_order(2, following("rcondt"), true);
        let sentences: Vec<&str> = order.iter().map(|(_, s)| s.as_str()).collect();
        assert_eq!(
            sentences,
            [
                "rcondt{2} ^if; 1: auto => />.",
                "rcondt{2} ^if; 1: auto => /#.",
                "rcondf{2} ^if; 1: auto => />.",
                "rcondf{2} ^if; 1: auto => /#.",
            ]
        );
        assert_eq!(order[0].0, "rcondt");
        assert_eq!(following("rcondf"), ["rcondf", "rcondt"]);
    }
}
