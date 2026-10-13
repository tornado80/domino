// SPDX-License-Identifier: MIT OR Apache-2.0

//! Reading goals as EasyCrypt's JSON shows them (story 27 §3.2.4): subgoals are told apart by
//! their **kind** (an ambient formula, an `equivS`, an `hoareS` under a quantifier) and by the
//! head of their programs, never by position in EasyCrypt's list or in our listing. Only the
//! front goal is read in full; of the goals behind it only their [`GoalKind`] is known
//! (ADR 0009).

use crate::easycrypt::json::{Form, Goal, GoalKind, Instr, Side};

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

/// Whether any node of the formula tree is an application of an operator named `name`.
pub(super) fn mentions_op(form: &Form, name: &str) -> bool {
    if op_is(form, name) {
        return true;
    }
    let children = form
        .head
        .iter()
        .map(|b| &**b)
        .chain(form.args.iter())
        .chain(form.body.iter().map(|b| &**b))
        .chain(form.pre.iter().map(|b| &**b))
        .chain(form.post.iter().map(|b| &**b));
    children.into_iter().any(|c| mentions_op(c, name))
}

/// The most pairs a key case split takes: `2^6` cases.
pub(super) const MAX_KEY_PAIRS: usize = 6;

/// A binder over the keys of an updated map, and the written key (story 66): the split
/// `case (binder = key)`. Both are EasyCrypt text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct KeyPair {
    pub binder: String,
    pub key: String,
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
            let var = match form.scope.as_deref() {
                Some("global") => {
                    let path = form.path.as_deref()?;
                    path.strip_prefix("Top.").unwrap_or(path).replace("./", ".")
                }
                _ => form.name.clone()?,
            };
            Some(format!("{var}{{{side}}}"))
        }
        _ => None,
    }
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

/// The pairs of a key case split on `form` (story 66 §3.1): a binder in `binders` that is the
/// index of a read or a membership test on an updated map, with each atom key written into that
/// map. In the order they occur, without duplicates.
pub(super) fn key_pairs(form: &Form, binders: &[String]) -> Vec<KeyPair> {
    let mut pairs = Vec::new();
    collect_key_pairs(form, binders, &mut pairs);
    pairs
}

fn collect_key_pairs(form: &Form, binders: &[String], pairs: &mut Vec<KeyPair>) {
    if let Some((map, index)) = map_access(form) {
        if let Some(binder) = (index.kind == "local")
            .then_some(index.name.as_ref())
            .flatten()
            .filter(|b| binders.contains(b))
        {
            for key in written_keys(map) {
                let pair = KeyPair {
                    binder: binder.clone(),
                    key,
                };
                if !pairs.contains(&pair) {
                    pairs.push(pair);
                }
            }
        }
    }
    let children = form
        .head
        .iter()
        .map(|b| &**b)
        .chain(form.args.iter())
        .chain(form.body.iter().map(|b| &**b))
        .chain(form.pre.iter().map(|b| &**b))
        .chain(form.post.iter().map(|b| &**b));
    for child in children {
        collect_key_pairs(child, binders, pairs);
    }
}

/// A hypothesis name that no hypothesis of the goal has.
pub(super) fn fresh_name(goal: &Goal, base: &str) -> String {
    let taken = |n: &str| goal.hyps.iter().any(|h| h.name == n);
    if !taken(base) {
        return base.to_string();
    }
    (1..)
        .map(|i| format!("{base}{i}"))
        .find(|n| !taken(n))
        .expect("an unused name exists")
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
        assert!(mentions_op(pre, "inv"), "{}", pre.pp);
        let post = goal.concl.post.as_ref().unwrap();
        let (a, b) = as_conjunction(post).expect("equal-output /\\ inv");
        assert!(!mentions_op(a, "inv"));
        assert_eq!(app_op_leaf(b), Some("inv"));
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
        let form = quant(r#"{"name":"ctr","ident":{"name":"ctr","tag":1},"kind":"var","type":{"pp":"int"}}"#);
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

    fn local(name: &str) -> String {
        format!(r#"{{"kind":"local","name":"{name}"}}"#)
    }

    fn pvar_k2() -> String {
        r#"{"kind":"pvar","scope":"global","path":"Top.Comp_H3.Pkg_Inst_KX./k","mem":"&2"}"#.into()
    }

    fn app(op: &str, args: &[String]) -> String {
        format!(r#"{{"kind":"app","op":"{op}","args":[{}]}}"#, args.join(","))
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
                binder: "c".into(),
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
        let k_plus_1 = app("Top.CoreInt.add", &[pvar_k2(), r#"{"kind":"int","value":"1"}"#.into()]);
        let not_atom = read(&set(&m, &k_plus_1), &local("c"));
        assert!(key_pairs(&form(&not_atom), &binders(&["c"])).is_empty());
        let plain = app("Top.Logic.and", &[read(&m, &local("c")), set(&m, &pvar_k2())]);
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
}
