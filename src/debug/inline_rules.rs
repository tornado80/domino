// SPDX-License-Identifier: MIT OR Apache-2.0

//! The rules both inlined listings follow: the debugger's ([`super::ir`],
//! also used by `domino inline`) and the read-only view ([`super::view`]).
//! Each renderer keeps its own output; this module only decides.
//!
//! - **Early return.** In an inlined callee, a `return` that is not in tail
//!   position of its oracle is an early return. The listings print it as
//!   `bind <- e; goto end_P_O;` and print `end_P_O:` after the inlined body.
//!   [`tail_positions`] tells which statements of a block are in tail position.
//! - **Frame label.** [`EndLabels::fresh`] gives `end_<Inst>_<Oracle>`, with
//!   `_2`, `_3`, … for a second inlining of the same oracle in one listing.
//! - **Always exits.** [`always_exits`]: a `return`, an `abort`, or an `if`
//!   whose remaining branches all exit. A `for` loop never counts.
//! - **Trivial condition.** [`condition_value`]: the Boolean value of a
//!   condition once its literals are folded, or `None`.
//!
//! All functions work on the transformed AST. A caller that knows more
//! constants substitutes them into a condition before it asks.

use std::collections::HashSet;

use crate::{
    expressions::{Expression, ExpressionKind},
    statement::Statement,
};

/// The labels handed out in one listing.
#[derive(Default)]
pub(super) struct EndLabels(HashSet<String>);

impl EndLabels {
    /// A new label for the end of the inlined frame of `frame` (`Inst.Oracle`):
    /// `end_Inst_Oracle`, with every character that is not a letter or a digit
    /// replaced by `_`; `end_Inst_Oracle_2`, … when the label is already used.
    pub(super) fn fresh(&mut self, frame: &str) -> String {
        let base: String = format!("end_{frame}")
            .chars()
            .map(|c| if c.is_alphanumeric() { c } else { '_' })
            .collect();
        let label = if self.0.contains(&base) {
            fresh_name(&base, &self.0)
        } else {
            base
        };
        self.0.insert(label.clone());
        label
    }
}

/// `name_2`, `name_3`, … (`pk_2` for `pk_`), the first one not in `taken`.
pub(super) fn fresh_name(name: &str, taken: &HashSet<String>) -> String {
    let sep = if name.ends_with('_') { "" } else { "_" };
    (2..)
        .map(|k| format!("{name}{sep}{k}"))
        .find(|n| !taken.contains(n))
        .expect("an unbounded range has a fresh name")
}

/// For each statement of `block`, whether it is in tail position: `tail` tells
/// whether `block` ends its oracle, and a statement is in tail position when
/// `block` is and the statement is the last one or always exits. `value` gives
/// the value of a condition (see [`always_exits`]).
///
/// A `return` of an inlined callee that is not in tail position is an early
/// return. The statements after one that always exits never run.
pub(super) fn tail_positions(
    block: &[Statement],
    tail: bool,
    value: &dyn Fn(&Expression) -> Option<bool>,
) -> Vec<bool> {
    block
        .iter()
        .enumerate()
        .map(|(i, stmt)| tail && (i + 1 == block.len() || always_exits(stmt, value)))
        .collect()
}

/// Every path through `stmt` returns or aborts. An `if` counts only the
/// branches that can run: `value` gives the value of its condition (`None`
/// when it is not known). A `for` loop never counts.
pub(super) fn always_exits(stmt: &Statement, value: &dyn Fn(&Expression) -> Option<bool>) -> bool {
    let block_exits = |block: &[Statement]| block.iter().any(|s| always_exits(s, value));
    match stmt {
        Statement::Return(..) | Statement::Abort(_) => true,
        Statement::IfThenElse(ite) => match value(&ite.cond) {
            Some(true) => block_exits(&ite.then_block.0),
            Some(false) => block_exits(&ite.else_block.0),
            None => block_exits(&ite.then_block.0) && block_exits(&ite.else_block.0),
        },
        _ => false,
    }
}

/// The value of condition `e` once its Boolean structure and its literal
/// comparisons are folded: `Some(true)`, `Some(false)`, or `None`.
pub(super) fn condition_value(e: &Expression) -> Option<bool> {
    as_bool(&fold(e))
}

pub(super) fn as_bool(e: &Expression) -> Option<bool> {
    match e.kind() {
        ExpressionKind::BooleanLiteral(b) => Some(b == "true"),
        _ => None,
    }
}

pub(super) fn is_literal(e: &Expression) -> bool {
    matches!(
        e.kind(),
        ExpressionKind::BooleanLiteral(_)
            | ExpressionKind::IntegerLiteral(_)
            | ExpressionKind::StringLiteral(_)
            | ExpressionKind::BitsLiteral(..)
            | ExpressionKind::None(_)
            | ExpressionKind::Bot
    )
}

/// Evaluates the Boolean structure of `e` as far as literals allow.
pub(super) fn fold(e: &Expression) -> Expression {
    use ExpressionKind as K;
    e.map(|sub| {
        let folded = match sub.kind() {
            K::Not(x) => as_bool(x).map(|b| Expression::boolean(!b)),
            K::And(xs) | K::Or(xs) => fold_junction(&sub, xs),
            K::Equals(xs) if xs.len() == 2 && xs.iter().all(is_literal) => {
                Some(Expression::boolean(xs[0] == xs[1]))
            }
            K::LessThen(l, r)
            | K::GreaterThen(l, r)
            | K::LessThenEq(l, r)
            | K::GreaterThenEq(l, r) => match (l.kind(), r.kind()) {
                (K::IntegerLiteral(l), K::IntegerLiteral(r)) => {
                    Some(Expression::boolean(match sub.kind() {
                        K::LessThen(..) => l < r,
                        K::GreaterThen(..) => l > r,
                        K::LessThenEq(..) => l <= r,
                        _ => l >= r,
                    }))
                }
                _ => None,
            },
            _ => None,
        };
        folded.unwrap_or(sub)
    })
}

/// `sub` is `And(xs)` or `Or(xs)`: the folded form, or `None` if no operand is
/// a literal.
fn fold_junction(sub: &Expression, xs: &[Expression]) -> Option<Expression> {
    use ExpressionKind as K;
    // `absorbing` decides the result; `neutral` operands drop out.
    let absorbing = !matches!(sub.kind(), K::And(_));
    if xs.iter().any(|x| as_bool(x) == Some(absorbing)) {
        return Some(Expression::boolean(absorbing));
    }
    let rest: Vec<_> = xs
        .iter()
        .filter(|x| as_bool(x).is_none())
        .cloned()
        .collect();
    match rest.len() {
        0 => Some(Expression::boolean(!absorbing)),
        1 => rest.into_iter().next(),
        n if n == xs.len() => None,
        _ if absorbing => Some(Expression::from_kind(K::Or(rest))),
        _ => Some(Expression::from_kind(K::And(rest))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_second_label_for_the_same_oracle_is_numbered() {
        let mut labels = EndLabels::default();
        assert_eq!(labels.fresh("PRF.Eval"), "end_PRF_Eval");
        assert_eq!(labels.fresh("PRF.Eval"), "end_PRF_Eval_2");
        assert_eq!(labels.fresh("PRF.Eval"), "end_PRF_Eval_3");
    }

    #[test]
    fn literals_fold_to_a_value() {
        let t = Expression::boolean(true);
        let f = Expression::boolean(false);
        let and = Expression::from_kind(ExpressionKind::And(vec![t.clone(), f.clone()]));
        assert_eq!(condition_value(&and), Some(false));
        let not = Expression::from_kind(ExpressionKind::Not(Box::new(f)));
        assert_eq!(condition_value(&not), Some(true));
    }
}
