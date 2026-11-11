// SPDX-License-Identifier: MIT OR Apache-2.0

//! The concrete part of a reduction step of a proposition (story 102, ADR 0023 decisions 1, 3
//! and 4): the **reduction adversary** `B_<L>_<R><s>`, the equivalence lemma(s)
//! `equiv_<L>_<R><s>` (or `_L`/`_R`) and the **bound lemma** `bound_<L>_<R><s>`.
//!
//! The **merge rule**: each pair of values that differ between the two sides gets one binder,
//! and a game position and an assumption position with the same pair share it. The two sides
//! merge into one lemma when both sides use the same game composition and the same assumption
//! composition, and the game's set of differing pairs equals the assumption's.

use super::ast::{EcBinop, EcExpr, EcType};
use super::render::render_expr;

/// The suffix `<s>` of a reduction step: `_<const>_<value>` for each constant, in the given
/// order, with `neg<n>` for a negative integer.
pub(super) fn suffix(values: &[(String, String)]) -> String {
    values
        .iter()
        .map(|(c, v)| match v.strip_prefix('-') {
            Some(n) => format!("_{c}_neg{n}"),
            None => format!("_{c}_{v}"),
        })
        .collect()
}

/// A run parameter of an experiment: its name and its type.
pub(super) type Param = (String, EcType);

/// The result of the merge rule.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Merged {
    /// One binder for each differing pair, named after the game's parameter at its first
    /// position.
    pub binders: Vec<Param>,
    /// The game's `run` arguments, a binder at each differing position.
    pub game: Vec<EcExpr>,
    /// The assumption's `run` arguments, a binder at each differing position.
    pub assm: Vec<EcExpr>,
}

/// The differing pairs of a two-sided tuple, by rendered value, with their positions.
fn differing(sides: [&[EcExpr]; 2]) -> Vec<(usize, (String, String))> {
    sides[0]
        .iter()
        .zip(sides[1])
        .enumerate()
        .map(|(i, (l, r))| (i, (render_expr(l), render_expr(r))))
        .filter(|(_, (l, r))| l != r)
        .collect()
}

/// The merge rule. `game` and `assm` are the `run` arguments of the left and right side;
/// `same_compositions` says that both sides use the same game and the same assumption
/// composition. `taken` are names that a binder may not use. `None`: write `_L` and `_R`.
pub(super) fn merge(
    game: [&[EcExpr]; 2],
    assm: [&[EcExpr]; 2],
    game_params: &[Param],
    same_compositions: bool,
    taken: &[String],
) -> Option<Merged> {
    if !same_compositions || game[0].len() != game[1].len() || assm[0].len() != assm[1].len() {
        return None;
    }
    let g = differing(game);
    let a = differing(assm);
    let set = |d: &[(usize, (String, String))]| {
        let mut s: Vec<(String, String)> = d.iter().map(|(_, p)| p.clone()).collect();
        s.sort();
        s.dedup();
        s
    };
    if set(&g) != set(&a) {
        return None;
    }
    let mut pairs: Vec<(String, String)> = Vec::new();
    let mut binders: Vec<Param> = Vec::new();
    for (i, pair) in &g {
        if pairs.contains(pair) {
            continue;
        }
        let (name, ty) = game_params[*i].clone();
        let mut name = name;
        while taken.contains(&name) || binders.iter().any(|(b, _)| b == &name) {
            name.push('_');
        }
        pairs.push(pair.clone());
        binders.push((name, ty));
    }
    let fill = |values: &[EcExpr], d: &[(usize, (String, String))]| -> Vec<EcExpr> {
        let mut out = values.to_vec();
        for (i, pair) in d {
            let k = pairs.iter().position(|p| p == pair).expect("a known pair");
            out[*i] = EcExpr::Var(binders[k].0.clone());
        }
        out
    };
    Some(Merged {
        game: fill(game[0], &g),
        assm: fill(assm[0], &a),
        binders: binders.clone(),
    })
}

/// `arg{mem} = v` or `arg{mem} = (v, ..)`; `None` for no arguments.
pub(super) fn arg_conjunct(args: &[EcExpr], mem: u8) -> Option<String> {
    let value = match args.len() {
        0 => return None,
        1 => render_expr(&args[0]),
        _ => render_expr(&EcExpr::Tuple(args.to_vec())),
    };
    Some(format!("arg{{{mem}}} = {value}"))
}

/// `Pr[module.run(args) @ &m : res]`.
pub(super) fn pr(module: String, args: Vec<EcExpr>) -> EcExpr {
    EcExpr::Pr {
        module,
        proc: "run".to_string(),
        args,
        memory: "m".to_string(),
        event: Box::new(EcExpr::Var("res".to_string())),
    }
}

/// `` `|a - b| ``.
pub(super) fn abs_diff(a: EcExpr, b: EcExpr) -> EcExpr {
    EcExpr::Abs(Box::new(EcExpr::Binop {
        op: EcBinop::Sub,
        lhs: Box::new(a),
        rhs: Box::new(b),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(b: bool) -> EcExpr {
        EcExpr::Bool(b)
    }

    fn params(names: &[&str]) -> Vec<Param> {
        names
            .iter()
            .map(|n| (n.to_string(), EcType::Bool))
            .collect()
    }

    #[test]
    fn equal_pair_sets_merge_and_share_the_binder() {
        let gl = [lit(false), lit(false)];
        let gr = [lit(false), lit(true)];
        let (al, ar) = ([lit(false)], [lit(true)]);
        let m = merge([&gl, &gr], [&al, &ar], &params(&["kx", "ideal"]), true, &[]).unwrap();
        assert_eq!(m.binders, params(&["ideal"]));
        let var = EcExpr::Var("ideal".to_string());
        assert_eq!(m.game, vec![lit(false), var.clone()]);
        assert_eq!(m.assm, vec![var]);
    }

    #[test]
    fn an_assumption_pair_that_the_game_does_not_have_gives_two_lemmas() {
        let g = [lit(false)];
        let (al, ar) = ([lit(false)], [lit(true)]);
        assert_eq!(
            merge([&g, &g], [&al, &ar], &params(&["x"]), true, &[]),
            None
        );
    }

    #[test]
    fn different_compositions_give_two_lemmas() {
        let (gl, gr) = ([lit(false)], [lit(true)]);
        assert_eq!(
            merge([&gl, &gr], [&gl, &gr], &params(&["x"]), false, &[]),
            None
        );
    }

    #[test]
    fn a_reversed_pair_is_a_different_pair() {
        let (gl, gr) = ([lit(false)], [lit(true)]);
        assert_eq!(
            merge([&gl, &gr], [&gr, &gl], &params(&["x"]), true, &[]),
            None
        );
    }

    #[test]
    fn a_binder_does_not_take_a_name_in_use() {
        let (gl, gr) = ([lit(false)], [lit(true)]);
        let m = merge(
            [&gl, &gr],
            [&gl, &gr],
            &params(&["b"]),
            true,
            &["b".to_string()],
        )
        .unwrap();
        assert_eq!(m.binders, params(&["b_"]));
    }

    #[test]
    fn a_negative_integer_gives_neg_in_the_suffix() {
        let values = [
            ("b".to_string(), "false".to_string()),
            ("n".to_string(), "-3".to_string()),
        ];
        assert_eq!(suffix(&values), "_b_false_n_neg3");
        assert_eq!(suffix(&[]), "");
    }
}
