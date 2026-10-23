// SPDX-License-Identifier: MIT OR Apache-2.0

//! Reading goals as EasyCrypt's JSON shows them (story 27 §3.2.4): subgoals are told apart by
//! their **kind** (an ambient formula, an `equivS`, an `hoareS` under a quantifier) and by the
//! head of their programs, never by position in EasyCrypt's list or in our listing. Only the
//! front goal is read in full; of the goals behind it only their [`GoalKind`] is known
//! (ADR 0009).

use std::collections::BTreeSet;

use crate::easycrypt::json::{Form, Goal, GoalKind, Instr, Side};
use crate::writers::easycrypt::invariant::{SideConjunct, SideConjuncts};

/// A program goal: `equiv[ S1 ~ S2 : pre ==> post ]`, or `hoare[ S : pre ==> post ]` in a
/// side-invariant lemma (story 69).
pub(super) fn is_program(goal: &Goal) -> bool {
    matches!(goal.concl.kind.as_str(), "equivS" | "hoareS")
}

/// The one program of a `hoare[ S : pre ==> post ]` goal.
pub(super) fn program(goal: &Goal) -> Option<&Side> {
    (goal.concl.kind == "hoareS")
        .then_some(goal.concl.program.as_ref())
        .flatten()
}

/// Whether the goal is a formula of the ambient logic, possibly with a program judgement under
/// its quantifier (what `rcondt` leaves as its side goal): anything that is not itself a
/// program judgement.
pub(super) fn is_ambient(goal: &Goal) -> bool {
    !matches!(
        goal.concl.kind.as_str(),
        "equivS"
            | "equivF"
            | "hoareS"
            | "hoareF"
            | "phoareS"
            | "phoareF"
            | "ehoareS"
            | "ehoareF"
            | "eagerF"
    )
}

/// The shape `if.` leaves on a pair of programs: the condition (an ambient formula) in front,
/// then the two arms (program judgements). `kind(i)` is the kind of the open goal at `i`.
pub(super) fn is_if_split(front: Option<&Goal>, kind: impl Fn(usize) -> Option<GoalKind>) -> bool {
    front.is_some_and(is_ambient)
        && kind(1) == Some(GoalKind::Program)
        && kind(2) == Some(GoalKind::Program)
}

pub(super) fn sides(goal: &Goal) -> Option<(&Side, &Side)> {
    if goal.concl.kind != "equivS" {
        return None;
    }
    Some((goal.concl.left.as_ref()?, goal.concl.right.as_ref()?))
}

/// Both programs are empty (`<skip> ~ <skip>`).
pub(super) fn is_skip_pair(goal: &Goal) -> bool {
    sides(goal).is_some_and(|(l, r)| l.stmt.is_empty() && r.stmt.is_empty())
}

/// The number of assignments at the start of a statement list: what `sp k l` consumes.
pub(super) fn leading_assignments(stmts: &[Instr]) -> usize {
    stmts.iter().take_while(|s| s.kind == "asgn").count()
}

/// The `(k, l)` of `sp k l` for a program goal.
pub(super) fn sp_counts(goal: &Goal) -> Option<(usize, usize)> {
    let (l, r) = sides(goal)?;
    Some((leading_assignments(&l.stmt), leading_assignments(&r.stmt)))
}

/// The first instruction that is not an assignment, and how many assignments precede it.
pub(super) fn head_after_assignments(stmts: &[Instr]) -> (usize, Option<&Instr>) {
    let k = leading_assignments(stmts);
    (k, stmts.get(k))
}

pub(super) fn op_name(form: &Form) -> Option<&str> {
    form.op.as_deref()
}

fn op_is(form: &Form, last: &str) -> bool {
    form.kind == "app"
        && op_name(form).is_some_and(|op| op.rsplit_once('.').is_some_and(|(_, n)| n == last))
}

/// `A => B`.
pub(super) fn as_implication(form: &Form) -> Option<(&Form, &Form)> {
    if op_is(form, "=>") && form.args.len() == 2 {
        Some((&form.args[0], &form.args[1]))
    } else {
        None
    }
}

/// `A /\ B`. Only tests read it: a leaf is opened by `do split`, whatever the head.
#[cfg(test)]
pub(super) fn as_conjunction(form: &Form) -> Option<(&Form, &Form)> {
    if op_is(form, "/\\") && form.args.len() == 2 {
        Some((&form.args[0], &form.args[1]))
    } else {
        None
    }
}

/// `forall b1 … bk, body`: the names of the binders as `move =>` spells them, and the body.
///
/// No binder is skipped. `move =>` must name every binder, and a goal of Domino's never binds a
/// type. A filter on the kind would drop a value binder (kind `"var"`; `"type"` before
/// `domino-json/3`). A memory binder's name already has its `&` (`&m`).
pub(super) fn as_forall(form: &Form) -> Option<(Vec<&str>, &Form)> {
    if form.kind == "quant" && form.quantifier.as_deref() == Some("forall") {
        let names = form.binders.iter().map(|b| b.name.as_str()).collect();
        return Some((names, form.body.as_deref()?));
    }
    None
}

/// A quantifier over a program judgement: `forall &m0, hoare[…]`.
pub(super) fn wraps_program(form: &Form) -> bool {
    match form.kind.as_str() {
        "quant" => form.body.as_deref().is_some_and(|b| {
            matches!(
                b.kind.as_str(),
                "equivS" | "hoareS" | "phoareS" | "ehoareS" | "equivF" | "hoareF"
            ) || wraps_program(b)
        }),
        _ => false,
    }
}

/// The last path component of an application's operator: `StateRelation_rel` for
/// `Top.Eq_A_B_Invariants.StateRelation_rel`.
pub(super) fn app_op_leaf(form: &Form) -> Option<&str> {
    if form.kind != "app" {
        return None;
    }
    op_name(form).map(|op| op.rsplit_once('.').map_or(op, |(_, n)| n))
}

/// Whether the formula may hold an application of an operator named `name`: `true` if a node
/// is one, or if a node is a stub ([`Form::stub`]), below which it can be. A formula read with
/// `head` is cut at depth 4, and a premise can hold `inv` deeper (story 86). `false` only for a
/// formula seen in full that does not hold it.
pub(super) fn may_mention_op(form: &Form, name: &str) -> bool {
    if op_is(form, name) || form.stub {
        return true;
    }
    form.children().any(|c| may_mention_op(c, name))
}

/// The most pairs a key case split takes: `2^6` cases.
pub(super) const MAX_KEY_PAIRS: usize = 6;

/// The most pairs a named split takes (story 90 §3.5): at most 4 `smt` calls in its sentence.
pub(super) const MAX_NAMED_PAIRS: usize = 2;

/// The read index of an updated map, and a written key (story 66): the split
/// `case (index = key)`. Both are EasyCrypt text. The index is a binder (`binder` is `Some`, the
/// same text), or a term over binders (story 90 §3.6, `binder` is `None`), which a `case` can
/// name but not substitute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct KeyPair {
    pub index: String,
    pub binder: Option<String>,
    pub key: String,
}

impl KeyPair {
    /// `index = key`, the equation a `case` splits on.
    pub(super) fn equation(&self) -> String {
        format!("{} = {}", self.index, self.key)
    }
}

/// Whether the operator path ends in the operator `name` (an FMap operator name has dots:
/// `Top.FMap._.[_<-_]`).
fn op_ends(form: &Form, name: &str) -> bool {
    form.kind == "app"
        && op_name(form).is_some_and(|op| op.strip_suffix(name).is_some_and(|p| p.ends_with('.')))
}

/// An atom as EasyCrypt reads it: a program variable at a memory (`M.x{2}`, `x{1}`) or a local
/// (`c`). `None` for anything else.
fn atom_text(form: &Form) -> Option<String> {
    match form.kind.as_str() {
        "local" => form.name.clone(),
        "pvar" => {
            let side = form.mem.as_deref()?.trim_start_matches('&');
            let var = match global_var(form) {
                Some((var, _)) => var,
                None => form.name.clone()?,
            };
            Some(format!("{var}{{{side}}}"))
        }
        _ => None,
    }
}

/// A module variable as a goal prints it without its memory (`Comp_C.Pkg_Inst_I.x` for the
/// path `Top.Comp_C.Pkg_Inst_I./x`), and its memory (`&hr`). `None` for any other node.
fn global_var(form: &Form) -> Option<(String, &str)> {
    if form.kind != "pvar" || form.scope.as_deref() != Some("global") {
        return None;
    }
    let path = form.path.as_deref()?;
    let var = path.strip_prefix("Top.").unwrap_or(path).replace("./", ".");
    Some((var, form.mem.as_deref()?))
}

/// A term as EasyCrypt reads it (story 90 §3.6): an atom ([`atom_text`]), `oget t`, a map read
/// `t.[u]`, or a tuple projection ``t.`n``. A read and a projection bind tighter than `oget`,
/// so only an `oget` under another term is in parentheses. `None` for any other shape.
fn term_text(form: &Form) -> Option<String> {
    let inner = |f: &Form| {
        let text = term_text(f)?;
        Some(if op_is(f, "oget") {
            format!("({text})")
        } else {
            text
        })
    };
    if form.kind == "proj" {
        return Some(format!("{}.`{}", inner(form.arg.as_deref()?)?, form.index?));
    }
    if op_is(form, "oget") && form.args.len() == 1 {
        return Some(format!("oget {}", inner(&form.args[0])?));
    }
    if op_ends(form, "_.[_]") && form.args.len() == 2 {
        let index = term_text(&form.args[1])?;
        return Some(format!("{}.[{index}]", inner(&form.args[0])?));
    }
    atom_text(form)
}

/// Whether a local named in `binders` occurs in `form`.
fn mentions_binder(form: &Form, binders: &[String]) -> bool {
    (form.kind == "local" && form.name.as_ref().is_some_and(|n| binders.contains(n)))
        || form.children().any(|c| mentions_binder(c, binders))
}

/// The atom keys written into `map` by a chain of updates `m.[k1 <- v1].[k2 <- v2]…`.
fn written_keys(map: &Form) -> Vec<String> {
    let mut keys = Vec::new();
    let mut m = map;
    while op_ends(m, "_.[_<-_]") && m.args.len() == 3 {
        keys.extend(atom_text(&m.args[1]));
        m = &m.args[0];
    }
    keys
}

/// The `(map, index)` of a read `m.[b]` or of a membership test `b \in m` (`dom m b`).
fn map_access(form: &Form) -> Option<(&Form, &Form)> {
    let read = op_ends(form, "_.[_]") || op_ends(form, "dom");
    (read && form.args.len() == 2).then(|| (&form.args[0], &form.args[1]))
}

/// The pairs of a key case split on `form` (story 66 §3.1): the index of a read or a membership
/// test on an updated map, with each atom key written into that map, where the index is a binder
/// in `binders` or a term [`term_text`] prints that mentions one (story 90 §3.6). In the order
/// they occur, without duplicates.
pub(super) fn key_pairs(form: &Form, binders: &[String]) -> Vec<KeyPair> {
    let mut pairs = Vec::new();
    collect_key_pairs(form, binders, &mut pairs);
    pairs
}

fn collect_key_pairs(form: &Form, binders: &[String], pairs: &mut Vec<KeyPair>) {
    if let Some((map, index)) = map_access(form) {
        let binder = (index.kind == "local")
            .then_some(index.name.as_ref())
            .flatten()
            .filter(|b| binders.contains(b));
        let text = match binder {
            Some(b) => Some(b.clone()),
            None if mentions_binder(index, binders) => term_text(index),
            None => None,
        };
        if let Some(text) = text {
            for key in written_keys(map) {
                let pair = KeyPair {
                    index: text.clone(),
                    binder: binder.cloned(),
                    key,
                };
                if !pairs.contains(&pair) {
                    pairs.push(pair);
                }
            }
        }
    }
    for child in form.children() {
        collect_key_pairs(child, binders, pairs);
    }
}

/// A hypothesis name that no hypothesis of the goal has.
pub(super) fn fresh_name(goal: &Goal, base: &str) -> String {
    fresh_name_besides(goal, base, &[])
}

/// [`fresh_name`], also not one of `used`: names given in sentences the goal does not show yet.
pub(super) fn fresh_name_besides(goal: &Goal, base: &str, used: &[String]) -> String {
    let taken = |n: &str| goal.hyps.iter().any(|h| h.name == n) || used.iter().any(|u| u == n);
    if !taken(base) {
        return base.to_string();
    }
    (1..)
        .map(|i| format!("{base}{i}"))
        .find(|n| !taken(n))
        .expect("an unused name exists")
}

/// The pruned crush of a goal (story 92 §3.2), sent after `move=> /> <mems>.`: each binder and
/// premise of the conclusion named in order, each premise whose head operator is in `drop_ops`
/// given `_`, and every other name moved back into the goal before `smt()`:
/// `move=> x0 h0 _ h1; move: x0 h0 h1; smt().` A `forall` between two premises is walked too.
/// Each name is fresh against the hypotheses of `goal`. A memory binder keeps its name and stays
/// in the context. `None` if the conclusion has no premise.
pub(super) fn pruned_crush_sentence(goal: &Goal, drop_ops: &[String]) -> Option<String> {
    let mut intro: Vec<String> = Vec::new();
    let mut kept: Vec<String> = Vec::new();
    let mut premises = 0;
    let mut form = &goal.concl;
    loop {
        if let Some((names, body)) = as_forall(form) {
            for name in names {
                let fresh = if name.starts_with('&') {
                    fresh_name_besides(goal, name, &intro)
                } else {
                    let x = fresh_name_besides(goal, &format!("x{}", kept.len()), &intro);
                    kept.push(x.clone());
                    x
                };
                intro.push(fresh);
            }
            form = body;
        } else if let Some((premise, rest)) = as_implication(form) {
            premises += 1;
            if is_dropped(premise, drop_ops) {
                intro.push("_".into());
            } else {
                let h = fresh_name_besides(goal, &format!("h{}", kept.len()), &intro);
                kept.push(h.clone());
                intro.push(h);
            }
            form = rest;
        } else {
            break;
        }
    }
    if premises == 0 {
        return None;
    }
    let intro = intro.join(" ");
    Some(if kept.is_empty() {
        format!("move=> {intro}; smt().")
    } else {
        format!("move=> {intro}; move: {}; smt().", kept.join(" "))
    })
}

/// Whether the head operator of `premise` is one of `drop_ops`, compared by qualified name: EasyCrypt
/// may print the operator with more qualifiers before it (`Top.Comp_C.side_inv_C`).
fn is_dropped(premise: &Form, drop_ops: &[String]) -> bool {
    dropped_op(premise, drop_ops).is_some()
}

/// The name of `drop_ops` that is the head operator of `premise` ([`is_dropped`]).
fn dropped_op<'d>(premise: &Form, drop_ops: &'d [String]) -> Option<&'d str> {
    let op = op_name(premise).filter(|_| premise.kind == "app")?;
    drop_ops
        .iter()
        .find(|d| {
            op == d.as_str()
                || op
                    .strip_suffix(d.as_str())
                    .is_some_and(|p| p.ends_with('.'))
        })
        .map(String::as_str)
}

/// The invariant selection of a goal (story 93 §3.2), sent after `move=> /> <mems>.` like
/// [`pruned_crush_sentence`]. A premise `side_inv_<C> r` of `drop_ops` is kept when `r` reads a
/// memory of the conclusion, the abort premise `!Comp_<C>.Game_<C>.abort_flag{m}` of that memory
/// `m` is a premise too, and a conjunct of `conjuncts` (the list under that operator) has a
/// footprint that meets the tables of the conclusion (its module variables). The kept premise is
/// opened with the abort premise, and only the selected conjuncts are named:
///
/// `move=> h0 hs1; have := hs1; rewrite /<side_inv> /= => /(_ h0) [#] _ g1_1; clear hs1;
/// move: h0 g1_1; rewrite /<selected ops> /=; smt().`
///
/// Every other premise of `drop_ops` gets `_`, the rest are moved back as in the pruned crush.
/// `None` if no premise is kept.
pub(super) fn selection_sentence(
    goal: &Goal,
    drop_ops: &[String],
    conjuncts: &SideConjuncts,
) -> Option<String> {
    let (slots, concl) = walk_premises(&goal.concl);
    let (tables, mems): (BTreeSet<String>, BTreeSet<&str>) = global_vars(concl).into_iter().unzip();
    let premises: Vec<&Form> = slots.iter().filter_map(Slot::premise).collect();
    let mut opened: Vec<Opened> = Vec::new();
    for (i, premise) in premises.iter().enumerate() {
        let selected = dropped_op(premise, drop_ops)
            .and_then(|op| select(premise, op, conjuncts.get(op)?, &premises, &tables, &mems));
        opened.extend(selected.map(|s| Opened { premise: i, ..s }));
    }
    if opened.is_empty() {
        return None;
    }
    Some(Selection::name(goal, &slots, &premises, drop_ops, &opened).sentence(&opened))
}

/// A binder or a premise of a conclusion, in order.
enum Slot<'g> {
    Binder(&'g str),
    Premise(&'g Form),
}

impl<'g> Slot<'g> {
    fn premise(&self) -> Option<&'g Form> {
        match self {
            Slot::Premise(p) => Some(p),
            Slot::Binder(_) => None,
        }
    }
}

/// The binders and premises of `form` in order (a `forall` between two premises too), and the
/// conclusion after them.
fn walk_premises(form: &Form) -> (Vec<Slot<'_>>, &Form) {
    let mut slots = Vec::new();
    let mut form = form;
    loop {
        if let Some((names, body)) = as_forall(form) {
            slots.extend(names.into_iter().map(Slot::Binder));
            form = body;
        } else if let Some((premise, rest)) = as_implication(form) {
            slots.push(Slot::Premise(premise));
            form = rest;
        } else {
            return (slots, form);
        }
    }
}

/// Each module variable of `form` at its memory ([`global_var`]).
fn global_vars(form: &Form) -> Vec<(String, &str)> {
    let mut out: Vec<(String, &str)> = global_var(form).into_iter().collect();
    for child in form.children() {
        out.extend(global_vars(child));
    }
    out
}

/// A side-invariant premise that the selection opens: its index among the premises, its
/// operator, the index of its abort premise, the number of its conjuncts, and the indexes of
/// the selected conjuncts with their operators.
struct Opened<'c> {
    premise: usize,
    op: &'c str,
    abort: usize,
    count: usize,
    selected: Vec<(usize, &'c str)>,
}

/// The selection of the side-invariant premise `premise` of operator `op` (§3.2 steps 2–3), its
/// `premise` index not yet set; `None` if its record reads no memory of the conclusion, if no
/// abort premise of that memory is in `premises`, or if no conjunct meets `tables`.
fn select<'c>(
    premise: &Form,
    op: &'c str,
    conjuncts: &'c [SideConjunct],
    premises: &[&Form],
    tables: &BTreeSet<String>,
    mems: &BTreeSet<&str>,
) -> Option<Opened<'c>> {
    let mem = global_vars(premise)
        .into_iter()
        .map(|(_, m)| m)
        .find(|m| mems.contains(m))?;
    let theory = op.rsplit_once('.')?.0;
    let abort = premises.iter().position(|p| is_abort(p, theory, mem))?;
    let selected: Vec<(usize, &str)> = conjuncts
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.footprint.is_disjoint(tables))
        .map(|(j, c)| (j, c.op.as_str()))
        .collect();
    (!selected.is_empty()).then_some(Opened {
        premise: 0,
        op,
        abort,
        count: conjuncts.len(),
        selected,
    })
}

/// Whether `premise` is `!<theory>.Game_<C>.abort_flag{mem}`.
fn is_abort(premise: &Form, theory: &str, mem: &str) -> bool {
    let negation = premise.kind == "app"
        && matches!(app_op_leaf(premise), Some("!" | "[!]"))
        && premise.args.len() == 1;
    negation
        && global_var(&premise.args[0]).is_some_and(|(var, m)| {
            m == mem
                && var
                    .strip_prefix(theory)
                    .is_some_and(|rest| rest.starts_with(".Game_"))
                && var.ends_with(".abort_flag")
        })
}

/// The names of a selection sentence: the `move=>` names, the names moved back, and the name
/// of each premise.
struct Selection {
    intro: Vec<String>,
    kept: Vec<String>,
    names: Vec<String>,
    conjunct_names: Vec<Vec<String>>,
}

impl Selection {
    /// Names the slots as [`pruned_crush_sentence`] does; a premise that `opened` opens is
    /// `hs<k>`, and its selected conjuncts `g<k>_<j>`, which take its place among the kept.
    fn name(
        goal: &Goal,
        slots: &[Slot<'_>],
        premises: &[&Form],
        drop_ops: &[String],
        opened: &[Opened<'_>],
    ) -> Self {
        let mut sel = Selection {
            intro: Vec::new(),
            kept: Vec::new(),
            names: Vec::new(),
            conjunct_names: Vec::new(),
        };
        let mut i = 0;
        for slot in slots {
            let name = match slot {
                Slot::Binder(name) if name.starts_with('&') => sel.fresh(goal, name),
                Slot::Binder(_) => {
                    let x = sel.fresh(goal, &format!("x{}", sel.kept.len()));
                    sel.kept.push(x.clone());
                    x
                }
                Slot::Premise(_) => {
                    let name = sel.premise_name(goal, i, premises, drop_ops, opened);
                    i += 1;
                    name
                }
            };
            sel.intro.push(name);
        }
        sel
    }

    fn fresh(&self, goal: &Goal, base: &str) -> String {
        let used: Vec<String> = self
            .intro
            .iter()
            .chain(self.conjunct_names.iter().flatten())
            .cloned()
            .collect();
        fresh_name_besides(goal, base, &used)
    }

    /// The name of premise `i`; an opened premise also names its conjuncts.
    fn premise_name(
        &mut self,
        goal: &Goal,
        i: usize,
        premises: &[&Form],
        drop_ops: &[String],
        opened: &[Opened<'_>],
    ) -> String {
        let k = self.kept.len();
        let name = if let Some(o) = opened.iter().find(|o| o.premise == i) {
            let hs = self.fresh(goal, &format!("hs{k}"));
            let gs: Vec<String> = o
                .selected
                .iter()
                .map(|(j, _)| self.fresh(goal, &format!("g{k}_{j}")))
                .collect();
            self.kept.extend(gs.iter().cloned());
            self.conjunct_names.push(gs);
            hs
        } else if is_dropped(premises[i], drop_ops) {
            "_".to_string()
        } else {
            let h = self.fresh(goal, &format!("h{k}"));
            self.kept.push(h.clone());
            h
        };
        self.names.push(name.clone());
        name
    }

    /// The sentence: `move=>`, one `have` for each opened premise, `move:`, the unfold of the
    /// selected operators, `smt()`.
    fn sentence(&self, opened: &[Opened<'_>]) -> String {
        let mut parts = vec![format!("move=> {}", self.intro.join(" "))];
        let mut ops: Vec<&str> = Vec::new();
        for (o, gs) in opened.iter().zip(&self.conjunct_names) {
            let hs = &self.names[o.premise];
            let mut pattern = vec!["_"; o.count];
            for ((j, op), g) in o.selected.iter().zip(gs) {
                pattern[*j] = g;
                if !ops.contains(op) {
                    ops.push(op);
                }
            }
            parts.push(format!(
                "have := {hs}; rewrite /{} /= => /(_ {}) [#] {}; clear {hs}",
                o.op,
                self.names[o.abort],
                pattern.join(" ")
            ));
        }
        parts.push(format!("move: {}", self.kept.join(" ")));
        let unfold: Vec<String> = ops.iter().map(|op| format!("/{op}")).collect();
        parts.push(format!("rewrite {} /=", unfold.join(" ")));
        parts.push("smt().".to_string());
        parts.join("; ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::easycrypt::json::parse_response;

    const FIXTURE: &str = include_str!(
        "../../../testdata/easycrypt/story25/hello_world_useful_oracle_after_inline.json"
    );

    #[test]
    fn the_recorded_goal_is_a_program_goal_and_its_prefix_is_counted() {
        let response = parse_response(FIXTURE).unwrap();
        let goal = response.proof.as_ref().unwrap().front.as_ref().unwrap();
        assert!(is_program(goal));
        assert!(!is_ambient(goal));
        assert!(!is_skip_pair(goal));
        // `ec_result <- None; if (…) {…}`: one assignment on each side, then the router guard
        assert_eq!(sp_counts(goal), Some((1, 1)));
        let (l, _) = sides(goal).unwrap();
        let (k, head) = head_after_assignments(&l.stmt);
        assert_eq!(k, 1);
        assert_eq!(head.unwrap().kind, "if");
    }

    #[test]
    fn implications_conjunctions_and_operators_are_read_from_the_formula_tree() {
        let response = parse_response(FIXTURE).unwrap();
        let goal = response.proof.as_ref().unwrap().front.as_ref().unwrap();
        let pre = goal.concl.pre.as_ref().unwrap();
        // the precondition is `true /\ inv …` (or a conjunction with it)
        assert!(may_mention_op(pre, "inv"), "{}", pre.pp);
        let post = goal.concl.post.as_ref().unwrap();
        let (a, b) = as_conjunction(post).expect("equal-output /\\ inv");
        assert!(!may_mention_op(a, "inv"));
        assert_eq!(app_op_leaf(b), Some("inv"));
    }

    /// Story 86: an `/\` of two atoms, the second at depth 2 being `atom`.
    fn conj_with(atom: &str) -> Form {
        form(&format!(
            r#"{{"kind":"app","pp":"x","op":"Top.Logic./\\","args":[
                {{"kind":"app","pp":"a","op":"Top.a"}},{atom}]}}"#
        ))
    }

    #[test]
    fn an_operator_at_depth_2_may_be_mentioned() {
        let f = conj_with(r#"{"kind":"app","pp":"inv","op":"Top.Eq.inv"}"#);
        assert!(may_mention_op(&f, "inv"));
    }

    #[test]
    fn an_operator_below_a_stub_may_be_mentioned() {
        let f = conj_with(r#"{"kind":"app","pp":"","op":"Top.Logic./\\","stub":true}"#);
        assert!(may_mention_op(&f, "inv"));
    }

    #[test]
    fn a_formula_without_stubs_and_without_the_operator_does_not_mention_it() {
        let f = conj_with(r#"{"kind":"app","pp":"b","op":"Top.b"}"#);
        assert!(!may_mention_op(&f, "inv"));
    }

    fn formula_goal() -> Goal {
        serde_json::from_str(r#"{"id":1,"concl":{"kind":"app","pp":"c"}}"#).unwrap()
    }

    #[test]
    fn an_if_split_is_a_formula_in_front_and_two_programs_behind_it() {
        use GoalKind::{Formula, Program};
        let front = formula_goal();
        let split =
            |front: Option<&Goal>, k: Vec<GoalKind>| is_if_split(front, |i| k.get(i).copied());
        assert!(split(Some(&front), vec![Formula, Program, Program]));
        assert!(!split(Some(&front), vec![Formula, Program, Formula]));
        assert!(!split(Some(&front), vec![Formula, Program]));
        assert!(!split(None, vec![Program, Program]));
        let proof = parse_response(FIXTURE).unwrap().proof.unwrap();
        let program = proof.front.unwrap();
        assert!(!split(Some(&program), vec![Program, Program, Program]));
    }

    fn quant(binder: &str) -> Form {
        let json = format!(
            r#"{{"kind":"quant","pp":"","quantifier":"forall","binders":[{binder}],
                "body":{{"kind":"app","pp":"P","op":"P","args":[]}}}}"#
        );
        serde_json::from_str(&json).unwrap()
    }

    #[test]
    fn a_value_binder_is_kept_and_the_driver_can_introduce_it() {
        // EasyCrypt writes a value binder (`GTty`) with the kind "var"
        let form = quant(
            r#"{"name":"ctr","ident":{"name":"ctr","tag":1},"kind":"var","type":{"pp":"int"}}"#,
        );
        let (names, _) = as_forall(&form).unwrap();
        assert_eq!(names, ["ctr"]);
        assert_eq!(format!("move => {}.", names.join(" ")), "move => ctr.");
    }

    #[test]
    fn a_memory_binder_keeps_its_ampersand() {
        let form = quant(r#"{"name":"&m","ident":{"name":"&m","tag":2},"kind":"mem"}"#);
        let (names, _) = as_forall(&form).unwrap();
        assert_eq!(names, ["&m"]);
    }

    fn implies(a: &str, b: &str) -> String {
        format!(r#"{{"kind":"app","op":"Top.Logic.=>","args":[{a},{b}]}}"#)
    }

    fn forall(names: &[&str], body: &str) -> String {
        let binders: Vec<String> = names
            .iter()
            .map(|n| format!(r#"{{"name":"{n}","kind":"var"}}"#))
            .collect();
        format!(
            r#"{{"kind":"quant","quantifier":"forall","binders":[{}],"body":{body}}}"#,
            binders.join(",")
        )
    }

    fn atom(op: &str) -> String {
        app(op, &[])
    }

    fn goal_of(concl: &str) -> Goal {
        serde_json::from_str(&format!(r#"{{"id":1,"concl":{concl}}}"#)).unwrap()
    }

    const SIDE_INV: &str = "Comp_H5.side_inv_H5";

    /// `forall (a b : int), A => side_inv_H5 r => B => forall z, C => D`.
    fn story92_goal(side_inv: &str) -> Goal {
        let tail = implies(&atom("C"), &atom("D"));
        let inner = implies(&atom("B"), &forall(&["z"], &tail));
        goal_of(&forall(
            &["a", "b"],
            &implies(&atom("A"), &implies(side_inv, &inner)),
        ))
    }

    #[test]
    fn the_pruned_crush_drops_the_side_invariant_and_reverts_the_rest_in_order() {
        let side_inv = app(&format!("Top.{SIDE_INV}"), &[local("r")]);
        let sentence = pruned_crush_sentence(&story92_goal(&side_inv), &[SIDE_INV.into()]);
        assert_eq!(
            sentence.as_deref(),
            Some("move=> x0 x1 h2 _ h3 x4 h5; move: x0 x1 h2 h3 x4 h5; smt().")
        );
    }

    #[test]
    fn without_drop_ops_the_pruned_crush_drops_nothing() {
        let side_inv = app(&format!("Top.{SIDE_INV}"), &[local("r")]);
        let sentence = pruned_crush_sentence(&story92_goal(&side_inv), &[]);
        assert_eq!(
            sentence.as_deref(),
            Some("move=> x0 x1 h2 h3 h4 x5 h6; move: x0 x1 h2 h3 h4 x5 h6; smt().")
        );
    }

    #[test]
    fn a_side_invariant_applied_to_a_record_literal_is_dropped() {
        // parentheses leave no node in the formula tree: the application is the premise
        let record = r#"{"kind":"record","fields":[]}"#.to_string();
        let side_inv = app(SIDE_INV, &[record]);
        let sentence = pruned_crush_sentence(&story92_goal(&side_inv), &[SIDE_INV.into()]);
        assert!(sentence.unwrap().starts_with("move=> x0 x1 h2 _ "));
    }

    #[test]
    fn a_goal_without_a_premise_has_no_pruned_crush_and_one_with_only_dropped_premises_no_move() {
        let none = goal_of(&forall(&["a"], &atom("A")));
        assert_eq!(pruned_crush_sentence(&none, &[SIDE_INV.into()]), None);
        let only = goal_of(&implies(&atom(SIDE_INV), &atom("A")));
        assert_eq!(
            pruned_crush_sentence(&only, &[SIDE_INV.into()]).as_deref(),
            Some("move=> _; smt().")
        );
    }

    #[test]
    fn the_pruned_crush_names_are_fresh_against_the_hypotheses() {
        let mut goal = goal_of(&implies(&atom("A"), &atom("B")));
        goal.hyps = serde_json::from_str(r#"[{"name":"h0","kind":"hyp"}]"#).unwrap();
        assert_eq!(
            pruned_crush_sentence(&goal, &[]).as_deref(),
            Some("move=> h01; move: h01; smt().")
        );
    }

    const SIDE_INV_H: &str = "Comp_H.side_inv_H";

    /// A module variable of `Comp_H` at memory `mem`.
    fn gvar(path: &str, mem: &str) -> String {
        format!(r#"{{"kind":"pvar","scope":"global","path":"Top.Comp_H.{path}","mem":"&{mem}"}}"#)
    }

    /// `!Comp_H.Game_H.abort_flag{mem}`.
    fn not_abort(mem: &str) -> String {
        app("Top.Logic.[!]", &[gvar("Game_H./abort_flag", mem)])
    }

    /// `Comp_H.side_inv_H` applied to a record that reads `ctr{mem}`.
    fn side_inv_at(mem: &str) -> String {
        let record = app("Top.Comp_H.H_side", &[gvar("Pkg_Inst_K./ctr", mem)]);
        app("Top.Comp_H.side_inv_H", &[record])
    }

    /// `P d_Kmac{mem}`.
    fn reads_kmac(mem: &str) -> String {
        app("Top.P", &[gvar("Pkg_Inst_K./d_Kmac", mem)])
    }

    fn conjunct(op: &str, footprint: &[&str]) -> SideConjunct {
        SideConjunct {
            op: format!("Comp_H.{op}"),
            footprint: footprint
                .iter()
                .map(|v| format!("Comp_H.Pkg_Inst_K.{v}"))
                .collect(),
        }
    }

    /// The conjuncts of `side_inv_H`: only `GameInv_b_of_H` reads `d_Kmac`.
    fn story93_conjuncts() -> SideConjuncts {
        let list = vec![
            conjunct("PkgInv_a_of_K_in_H", &["ctr"]),
            conjunct("GameInv_b_of_H", &["d_Kmac", "d_PRF"]),
            conjunct("GameInv_c_of_H", &["d_PRF"]),
        ];
        [(SIDE_INV_H.to_string(), list)].into_iter().collect()
    }

    fn selection(goal: &Goal) -> Option<String> {
        selection_sentence(goal, &[SIDE_INV_H.into()], &story93_conjuncts())
    }

    #[test]
    fn the_selection_names_only_the_conjuncts_that_read_a_table_of_the_conclusion() {
        let goal = goal_of(&implies(
            &not_abort("hr"),
            &implies(&atom("A"), &implies(&side_inv_at("hr"), &reads_kmac("hr"))),
        ));
        assert_eq!(
            selection(&goal).as_deref(),
            Some(concat!(
                "move=> h0 h1 hs2; ",
                "have := hs2; rewrite /Comp_H.side_inv_H /= => /(_ h0) [#] _ g2_1 _; clear hs2; ",
                "move: h0 h1 g2_1; rewrite /Comp_H.GameInv_b_of_H /=; smt()."
            ))
        );
    }

    #[test]
    fn without_an_abort_premise_a_table_or_a_selected_conjunct_there_is_no_selection() {
        let no_abort = goal_of(&implies(&side_inv_at("hr"), &reads_kmac("hr")));
        assert_eq!(selection(&no_abort), None);
        let no_table = goal_of(&implies(
            &not_abort("hr"),
            &implies(&side_inv_at("hr"), &atom("B")),
        ));
        assert_eq!(selection(&no_table), None);
        let other = app("Top.P", &[gvar("Pkg_Inst_K./d_Other", "hr")]);
        let none_selected = goal_of(&implies(
            &not_abort("hr"),
            &implies(&side_inv_at("hr"), &other),
        ));
        assert_eq!(selection(&none_selected), None);
    }

    #[test]
    fn a_branch_condition_that_reads_only_memory_2_keeps_only_the_side_invariant_of_2() {
        let concl = reads_kmac("2");
        let goal = goal_of(&implies(
            &not_abort("1"),
            &implies(
                &not_abort("2"),
                &implies(&side_inv_at("1"), &implies(&side_inv_at("2"), &concl)),
            ),
        ));
        assert_eq!(
            selection(&goal).as_deref(),
            Some(concat!(
                "move=> h0 h1 _ hs2; ",
                "have := hs2; rewrite /Comp_H.side_inv_H /= => /(_ h1) [#] _ g2_1 _; clear hs2; ",
                "move: h0 h1 g2_1; rewrite /Comp_H.GameInv_b_of_H /=; smt()."
            ))
        );
    }

    fn local(name: &str) -> String {
        format!(r#"{{"kind":"local","name":"{name}"}}"#)
    }

    fn pvar_k2() -> String {
        r#"{"kind":"pvar","scope":"global","path":"Top.Comp_H3.Pkg_Inst_KX./k","mem":"&2"}"#.into()
    }

    fn app(op: &str, args: &[String]) -> String {
        format!(
            r#"{{"kind":"app","op":"{op}","args":[{}]}}"#,
            args.join(",")
        )
    }

    fn set(map: &str, key: &str) -> String {
        app("Top.FMap._.[_<-_]", &[map.into(), key.into(), local("v")])
    }

    fn read(map: &str, index: &str) -> String {
        app("Top.FMap._.[_]", &[map.into(), index.into()])
    }

    fn form(json: &str) -> Form {
        serde_json::from_str(json).unwrap()
    }

    fn binders(names: &[&str]) -> Vec<String> {
        names.iter().map(|n| n.to_string()).collect()
    }

    #[test]
    fn a_read_of_an_updated_map_at_a_binder_gives_one_pair() {
        // forall c, (m.[k{2} <- v]).[c] <> None => ..., after `move => c`
        let m = local("m");
        let lhs = read(&set(&m, &pvar_k2()), &local("c"));
        let ne = app("Top.Logic.<>", &[lhs, r#"{"kind":"op"}"#.into()]);
        let goal = form(&app("Top.Logic.=>", &[ne, r#"{"kind":"op"}"#.into()]));
        let pairs = key_pairs(&goal, &binders(&["c"]));
        assert_eq!(
            pairs,
            [KeyPair {
                index: "c".into(),
                binder: Some("c".into()),
                key: "Comp_H3.Pkg_Inst_KX.k{2}".into()
            }]
        );
        // a membership test gives the same pair, once
        let both = app(
            "Top.Logic.and",
            &[
                read(&set(&m, &pvar_k2()), &local("c")),
                app("Top.FMap.dom", &[set(&m, &pvar_k2()), local("c")]),
            ],
        );
        assert_eq!(key_pairs(&form(&both), &binders(&["c"])).len(), 1);
    }

    #[test]
    fn a_key_that_is_not_an_atom_and_a_binder_outside_an_updated_map_give_no_pair() {
        let m = local("m");
        let k_plus_1 = app(
            "Top.CoreInt.add",
            &[pvar_k2(), r#"{"kind":"int","value":"1"}"#.into()],
        );
        let not_atom = read(&set(&m, &k_plus_1), &local("c"));
        assert!(key_pairs(&form(&not_atom), &binders(&["c"])).is_empty());
        let plain = app(
            "Top.Logic.and",
            &[read(&m, &local("c")), set(&m, &pvar_k2())],
        );
        assert!(key_pairs(&form(&plain), &binders(&["c"])).is_empty());
        // an index that the opening loop did not introduce
        let other = read(&set(&m, &pvar_k2()), &local("d"));
        assert!(key_pairs(&form(&other), &binders(&["c"])).is_empty());
    }

    #[test]
    fn a_chain_of_updates_gives_a_pair_for_each_key_in_order() {
        let x1 = r#"{"kind":"pvar","scope":"local","name":"x","mem":"&1"}"#;
        let chain = set(&set(&local("m"), x1), &pvar_k2());
        let pairs = key_pairs(&form(&read(&chain, &local("c"))), &binders(&["c"]));
        let keys: Vec<_> = pairs.iter().map(|p| p.key.as_str()).collect();
        assert_eq!(keys, ["Comp_H3.Pkg_Inst_KX.k{2}", "x{1}"]);
    }

    /// Story 88: the read `d.[ctr0{hr} <- state{hr}].[ctr1]` of §1 of the story.
    fn state_read() -> String {
        let ctr0 = r#"{"kind":"pvar","scope":"local","name":"ctr0","mem":"&hr"}"#;
        read(&set(&local("d"), ctr0), &local("ctr1"))
    }

    fn ctr_pairs(json: &str) -> Vec<KeyPair> {
        key_pairs(&form(json), &binders(&["ctr1"]))
    }

    #[test]
    fn a_read_under_a_projection_gives_its_pair() {
        // (oget d.[ctr0{hr} <- state{hr}].[ctr1]).`7 <> None
        let oget = app("Top.Core.oget", &[state_read()]);
        let proj = format!(r#"{{"kind":"proj","arg":{oget},"index":7}}"#);
        let ne = app("Top.Logic.<>", &[proj, r#"{"kind":"op"}"#.into()]);
        assert_eq!(
            ctr_pairs(&ne),
            [KeyPair {
                index: "ctr1".into(),
                binder: Some("ctr1".into()),
                key: "ctr0{hr}".into()
            }]
        );
    }

    /// The same atom `r` under each node kind that is not an `app` or a `quant`.
    fn under_each_kind(r: &str) -> [String; 5] {
        let t = r#"{"kind":"op"}"#;
        [
            format!(r#"{{"kind":"if","cond":{r},"then":{t},"else":{t}}}"#),
            format!(r#"{{"kind":"tuple","items":[{t},{r}]}}"#),
            format!(r#"{{"kind":"let","bound":{r},"body":{t}}}"#),
            format!(r#"{{"kind":"match","scrutinee":{r},"branches":[{t}]}}"#),
            format!(r#"{{"kind":"proj","arg":{r},"index":1}}"#),
        ]
    }

    #[test]
    fn a_read_under_an_if_a_tuple_a_let_or_a_match_gives_one_pair() {
        for json in under_each_kind(&state_read()) {
            assert_eq!(ctr_pairs(&json).len(), 1, "{json}");
        }
    }

    #[test]
    fn an_operator_under_each_node_kind_may_be_mentioned() {
        let inv = r#"{"kind":"app","op":"Top.Eq.inv"}"#;
        for json in under_each_kind(inv) {
            assert!(may_mention_op(&form(&json), "inv"), "{json}");
        }
        // the other arms of an `if`, a `let` body, a branch
        let t = r#"{"kind":"op"}"#;
        for json in [
            format!(r#"{{"kind":"if","cond":{t},"then":{t},"else":{inv}}}"#),
            format!(r#"{{"kind":"let","bound":{t},"body":{inv}}}"#),
            format!(r#"{{"kind":"match","scrutinee":{t},"branches":[{t},{inv}]}}"#),
        ] {
            assert!(may_mention_op(&form(&json), "inv"), "{json}");
        }
    }

    /// Story 90 §3.6: `d.[ctr0{hr} <- v].[oget d_First{hr}.[sid0]]`.
    fn first_read(index: &str) -> Vec<KeyPair> {
        let ctr0 = r#"{"kind":"pvar","scope":"local","name":"ctr0","mem":"&hr"}"#;
        let first = r#"{"kind":"pvar","scope":"local","name":"d_First","mem":"&hr"}"#;
        let oget = app("Top.Core.oget", &[read(first, index)]);
        key_pairs(
            &form(&read(&set(&local("d"), ctr0), &oget)),
            &binders(&["sid0"]),
        )
    }

    #[test]
    fn a_read_at_a_term_over_a_binder_gives_a_named_pair() {
        assert_eq!(
            first_read(&local("sid0")),
            [KeyPair {
                index: "oget d_First{hr}.[sid0]".into(),
                binder: None,
                key: "ctr0{hr}".into()
            }]
        );
    }

    #[test]
    fn a_term_index_without_a_binder_or_that_does_not_print_gives_no_pair() {
        assert!(first_read(&local("other")).is_empty());
        let odd = app("Top.Int.+", &[local("sid0"), local("sid0")]);
        assert!(first_read(&odd).is_empty());
    }

    /// Story 90 §3.6: the goal EasyCrypt printed after `auto => &hr hpre s /=.` on the read of
    /// Send5 J3 (`testdata/easycrypt/story90/requests.jsonl` gives the lemma): the index prints
    /// as EasyCrypt prints it.
    #[test]
    fn the_term_index_prints_as_easycrypt_prints_it() {
        let answer = include_str!("../../../testdata/easycrypt/story90/term_index_goal.json");
        let goal = parse_response(answer)
            .unwrap()
            .proof
            .unwrap()
            .front
            .unwrap();
        let pairs = key_pairs(&goal.concl, &binders(&["s"]));
        let [pair] = pairs.as_slice() else {
            panic!("{pairs:?}")
        };
        assert_eq!(pair.index, "oget d_First{hr}.[s]");
        assert_eq!(pair.binder, None);
        assert_eq!(pair.key, "ctr0{hr}");
        assert!(
            goal.concl.pp.contains(&format!(".[{}]", pair.index)),
            "{}",
            goal.concl.pp
        );
    }

    /// Story 90 §3.6, with a `-json` EasyCrypt (`DOMINO_EASYCRYPT`): the `case` on the printed
    /// term index re-parses in the leaf, and gives two goals.
    #[test]
    fn easycrypt_accepts_the_case_on_the_printed_term_index() {
        use crate::easycrypt::json::Status;
        use crate::easycrypt::session::{json_binary_configured, Session, Want};
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let dir = tempfile::tempdir().unwrap();
        let mut session = Session::start(dir.path()).unwrap();
        let requests = include_str!("../../../testdata/easycrypt/story90/requests.jsonl");
        for line in requests.lines() {
            let req: serde_json::Value = serde_json::from_str(line).unwrap();
            let sentence = req["sentence"].as_str().unwrap();
            let r = session.send(sentence, Want::Full).unwrap();
            assert_eq!(r.status, Status::Ok, "{sentence}");
        }
        let pairs = key_pairs(&session.front().unwrap().concl, &binders(&["s"]));
        let case = format!("case ({}) => [hc|hc].", pairs[0].equation());
        let r = session.send(&case, Want::Status).unwrap();
        assert_eq!(r.status, Status::Ok, "{case}");
        assert_eq!(session.count(), 2);
    }

    #[test]
    fn a_stub_projection_has_no_children() {
        let stub = form(r#"{"kind":"proj","stub":true}"#);
        assert_eq!(stub.children().count(), 0);
        assert!(key_pairs(&stub, &binders(&["ctr1"])).is_empty());
        assert!(may_mention_op(&stub, "inv"));
    }
}
