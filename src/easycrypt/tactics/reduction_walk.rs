// SPDX-License-Identifier: MIT OR Apache-2.0

//! The shape of a program head for the reduction walk (story 105, ADR 0024 decision 2).
//!
//! The reduction walk (story 106) proves a reduction's oracle lemma one program head at a time
//! and picks the step from the shape of the two first statements, [`classify`]. The rules read
//! only what EasyCrypt prints: a condition is a [`Node`](crate::easycrypt::json::Node) with its
//! text in `pp`, so the recognizers read text, after dropping the type annotations `<:…>`.
//!
//! `assumption` is the assumption theory of the reduction, `Comp_MAC` for `Red_H7_1_H7_0`.

// story 106 is the first caller
#![allow(dead_code)]

use crate::easycrypt::json::Instr;

/// The shape of the two program heads, after `sp` (an assignment is not a head).
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
    let (l, r) = (left.first(), right.first());
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
    use crate::easycrypt::json::{Instr, parse_response};

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
        let (asg, _) = goal!("tail-branch.json"); // an assignment left after `sp`
        let head = classify(&l, &asg, A);
        let heads = Mismatch::Heads {
            left: "call".to_string(),
            right: "asgn".to_string(),
        };
        assert_eq!(head, Head::Mismatch(heads.clone()));
        assert_eq!(heads.claim(), "heads call/asgn");
        let none = classify(&l, &[], A);
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
}
