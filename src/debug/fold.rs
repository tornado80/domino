// SPDX-License-Identifier: MIT OR Apache-2.0

//! The **folded listing** (symbolic-execution story 28, `CONTEXT.md`): a
//! second rendering of an inlined oracle with its trivial branches folded.
//! It is a view, not other code: the executor always walks the full IR, and
//! every line of the folded listing is a line of the full listing, named by
//! its label.
//!
//! - A **trivial branch** is an `if` with no exit guard whose condition has a
//!   known value once the constants the IR knows are substituted (see
//!   [`known_value`]). An `assert` is never trivial.
//! - A trivial `false` branch prints its `else` body, or nothing. A trivial
//!   `true` branch prints its `then` body. The body moves out to the branch's
//!   indentation; the `if`, `} else {` and `}` lines and the body that cannot
//!   run are left out.
//! - **Exit guards are never folded.** The done-flag guard of the EasyCrypt
//!   listing has the literal condition `true`, but EasyCrypt has to step over
//!   it.
//!
//! The fold reads the full listing's text and the line ranges the IR records
//! for each branch, so it is the same for the Domino listing and the
//! EasyCrypt listing.

use serde_derive::Serialize;

use super::inline_rules::{condition_value, is_literal};
use super::ir::{resolve_const, InlBlock, InlStmt, InlinedOracle, Label};
use crate::expressions::{Expression, ExpressionKind};

/// The folded listing of one inlined oracle.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct FoldedListing {
    /// The folded code, one line for each entry of `labels`.
    pub text: String,
    /// For each folded line, in order, the label (the full-listing line) it
    /// shows. The labels increase strictly.
    pub labels: Vec<Label>,
}

impl FoldedListing {
    /// Folds the trivial branches of `inlined` (see the module comment).
    pub fn of(inlined: &InlinedOracle) -> Self {
        let full: Vec<&str> = inlined.listing.text.lines().collect();
        let mut plan = Plan {
            hidden: vec![false; full.len() + 1],
            dedent: vec![0; full.len() + 1],
            full: &full,
        };
        plan.block(&inlined.body);
        let mut text = String::new();
        let mut labels = Vec::new();
        for (i, line) in full.iter().enumerate() {
            let label = i + 1;
            if plan.hidden[label] {
                continue;
            }
            let strip = plan.dedent[label].min(indent_of(line));
            text.push_str(&line[strip..]);
            text.push('\n');
            labels.push(label);
        }
        FoldedListing { text, labels }
    }

    /// The folded line (1-based) that shows `label`, or for a label the fold
    /// leaves out, the first folded line after it. A label after the last
    /// folded line gives the last line.
    pub fn line_of(&self, label: Label) -> usize {
        let i = self.labels.partition_point(|l| *l < label);
        i.min(self.labels.len().saturating_sub(1)) + 1
    }

    /// The folded lines, each with the label it shows.
    pub fn numbered_lines(&self) -> impl Iterator<Item = (Label, &str)> {
        self.labels.iter().copied().zip(self.text.lines())
    }
}

/// The value of a branch condition once each constant with a literal value is
/// replaced by it: `Some(true)`, `Some(false)` or `None`. The constants of a
/// game instance resolve to their values; a free parameter (a side tree's, or
/// a theorem constant) does not resolve, so there only literal conditions
/// have a value.
pub fn known_value(cond: &Expression) -> Option<bool> {
    let substituted = cond.map(|sub| match sub.kind() {
        ExpressionKind::Identifier(_) => {
            let resolved = resolve_const(&sub);
            if is_literal(resolved) {
                resolved.clone()
            } else {
                sub
            }
        }
        _ => sub,
    });
    condition_value(&substituted)
}

/// Which lines of the full listing the fold leaves out, and how many
/// characters of indentation each kept line loses. Indexed by label.
struct Plan<'a> {
    hidden: Vec<bool>,
    dedent: Vec<usize>,
    full: &'a [&'a str],
}

impl Plan<'_> {
    /// Plans `block`. The statements after one that always exits never run:
    /// they are left out, as the read-only view does (story 26).
    fn block(&mut self, block: &InlBlock) {
        for (i, stmt) in block.0.iter().enumerate() {
            self.stmt(stmt);
            if always_exits(stmt) {
                if let (Some(next), Some(last)) = (block.0.get(i + 1), block.0.last()) {
                    self.hide(label_of(next), last_line(last));
                }
                return;
            }
        }
    }

    /// Folds `stmt` if it is a trivial branch, and plans the blocks in it.
    fn stmt(&mut self, stmt: &InlStmt) {
        match stmt {
            InlStmt::Branch {
                label,
                cond,
                then,
                els,
                is_assert: false,
                then_lines: Some(then_lines),
                else_lines,
                exit_guard: None,
            } => match known_value(cond) {
                Some(value) => self.fold(*label, value, *then_lines, *else_lines, then, els),
                None => {
                    self.block(then);
                    self.block(els);
                }
            },
            InlStmt::Branch { then, els, .. } => {
                self.block(then);
                self.block(els);
            }
            InlStmt::Call { body, .. } => self.block(body),
            _ => {}
        }
    }

    /// Folds the branch at `label`, whose condition is `value`. The `then`
    /// body is the lines strictly inside `then_lines`; `then_lines.1` is its
    /// `}` or `} else {`. The `else` body is the lines before `else_lines.1`.
    fn fold(
        &mut self,
        label: Label,
        value: bool,
        then_lines: (Label, Label),
        else_lines: Option<(Label, Label)>,
        then: &InlBlock,
        els: &InlBlock,
    ) {
        let last = else_lines.map_or(then_lines.1, |(_, close)| close);
        let (kept, body) = match (value, else_lines) {
            (true, _) => ((then_lines.0, then_lines.1 - 1), then),
            (false, Some((first, close))) => ((first, close - 1), els),
            (false, None) => ((then_lines.1, then_lines.1 - 1), els),
        };
        let unit = self.indent(kept.0).saturating_sub(self.indent(label));
        for n in label..=last {
            if (kept.0..=kept.1).contains(&n) {
                self.dedent[n] += unit;
            } else {
                self.hidden[n] = true;
            }
        }
        self.block(body);
    }

    /// Leaves out the lines `first..=last`.
    fn hide(&mut self, first: Label, last: Label) {
        for n in first..=last {
            self.hidden[n] = true;
        }
    }

    fn indent(&self, label: Label) -> usize {
        self.full.get(label - 1).map_or(0, |line| indent_of(line))
    }
}

/// Every path through `stmt` returns or aborts, with the conditions of
/// trivial branches taken at their value. An exit guard counts as unknown;
/// an inlined call never counts (a `return` in it resumes the caller).
fn always_exits(stmt: &InlStmt) -> bool {
    let block_exits = |block: &InlBlock| block.0.iter().any(always_exits);
    match stmt {
        InlStmt::Return { .. } | InlStmt::Abort { .. } => true,
        InlStmt::Branch {
            cond,
            then,
            els,
            exit_guard,
            ..
        } => match exit_guard.is_none().then(|| known_value(cond)).flatten() {
            Some(true) => block_exits(then),
            Some(false) => block_exits(els),
            None => block_exits(then) && block_exits(els),
        },
        _ => false,
    }
}

/// The first line of `stmt`.
fn label_of(stmt: &InlStmt) -> Label {
    match stmt {
        InlStmt::Assign { label, .. }
        | InlStmt::Sample { label, .. }
        | InlStmt::Unwrap { label, .. }
        | InlStmt::Branch { label, .. }
        | InlStmt::Call { label, .. }
        | InlStmt::Return { label, .. }
        | InlStmt::Abort { label } => *label,
    }
}

/// The last line of `stmt`: the closing line of a branch or an inlined call.
fn last_line(stmt: &InlStmt) -> Label {
    match stmt {
        InlStmt::Branch {
            label,
            then_lines,
            else_lines,
            ..
        } => else_lines
            .or(*then_lines)
            .map_or(*label, |(_, close)| close),
        InlStmt::Call { frame_lines, .. } => frame_lines.1,
        other => label_of(other),
    }
}

/// The number of leading spaces of `line`.
fn indent_of(line: &str) -> usize {
    line.len() - line.trim_start_matches(' ').len()
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::*;
    use crate::debug::inline_rules::condition_value;
    use crate::debug::ir::{inline_oracle, ExitGuard};
    use crate::project::{DirectoryFiles, DirectoryProject, Project as _};
    use crate::theorem::Theorem;
    use crate::transforms::theorem_transforms::{DebugTransform, EasyCryptTransform};
    use crate::transforms::TheoremTransform;
    use crate::writers::easycrypt::lower::inline_oracle_ec;

    const FOUR_WHS: &str = "example-projects/4WHS";

    fn with_theorem(dir: &str, name: &str, f: impl FnOnce(&Theorem)) {
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        f(project.get_theorem(name).unwrap());
    }

    /// Every branch of `block`, nested ones too.
    fn branches(block: &InlBlock) -> Vec<&InlStmt> {
        let mut out = Vec::new();
        for stmt in &block.0 {
            match stmt {
                InlStmt::Branch { then, els, .. } => {
                    out.push(stmt);
                    out.extend(branches(then));
                    out.extend(branches(els));
                }
                InlStmt::Call { body, .. } => out.extend(branches(body)),
                _ => {}
            }
        }
        out
    }

    /// Each folded line is the full listing's line at its label, moved left at most.
    fn assert_lines_come_from_their_labels(inlined: &InlinedOracle, folded: &FoldedListing) {
        let full: Vec<&str> = inlined.listing.text.lines().collect();
        assert_eq!(folded.labels.len(), folded.text.lines().count());
        assert!(folded.labels.windows(2).all(|w| w[0] < w[1]));
        for (label, line) in folded.numbered_lines() {
            assert_eq!(full[label - 1].trim(), line.trim(), "label {label}");
        }
    }

    #[test]
    fn hybrid2_folds_the_ideal_branch_of_prf_eval_away() {
        // Hybrid2 instantiates PRF with `b: bprf`, and the theorem sets `bprf: false`
        with_theorem(FOUR_WHS, "Simple4WHS", |theorem| {
            let (dbg, _) = DebugTransform.transform_theorem(theorem).unwrap();
            let inlined =
                inline_oracle(dbg.find_game_instance("Hybrid2").unwrap(), "Send2").unwrap();
            let folded = FoldedListing::of(&inlined);
            let ideal = |text: &str| text.lines().filter(|l| l.contains("Prf.PRF[")).count();
            assert!(ideal(&inlined.listing.text) > 0, "{}", inlined.listing.text);
            assert_eq!(ideal(&folded.text), 0, "{}", folded.text);
            assert!(folded.labels.len() < inlined.listing.text.lines().count());
            assert_lines_come_from_their_labels(&inlined, &folded);
            // a label the fold leaves out maps to the first folded line after it
            let hidden = (1..=inlined.listing.text.lines().count())
                .find(|l| !folded.labels.contains(l))
                .unwrap();
            let line = folded.line_of(hidden);
            assert!(folded.labels[line - 1] > hidden);
            assert!(line == 1 || folded.labels[line - 2] < hidden);
        });
    }

    #[test]
    fn the_easycrypt_listing_folds_the_game_constants_too() {
        with_theorem(FOUR_WHS, "Simple4WHS", |theorem| {
            let (ec, _) = EasyCryptTransform.transform_theorem(theorem).unwrap();
            let inlined =
                inline_oracle_ec(ec.find_game_instance("Hybrid2").unwrap(), "Send2").unwrap();
            let folded = FoldedListing::of(&inlined);
            let ideal = |text: &str| text.lines().filter(|l| l.contains("Prf.d_PRF.[")).count();
            assert!(ideal(&inlined.listing.text) > 0, "{}", inlined.listing.text);
            assert_eq!(ideal(&folded.text), 0, "{}", folded.text);
            assert_lines_come_from_their_labels(&inlined, &folded);
        });
    }

    #[test]
    fn the_easycrypt_listing_keeps_its_done_flag_guards() {
        let dir = "example-projects/kem-dem/kem-dem-cca-ssp";
        with_theorem(dir, "kem_dem_cca_ssp", |theorem| {
            let (ec, _) = EasyCryptTransform.transform_theorem(theorem).unwrap();
            let game = ec.find_game_instance("Game_MON_CCA_PKE").unwrap();
            let inlined = inline_oracle_ec(game, "PKENC").unwrap();
            let folded = FoldedListing::of(&inlined);
            let guards: Vec<Label> = branches(&inlined.body)
                .into_iter()
                .filter_map(|b| match b {
                    InlStmt::Branch {
                        label,
                        exit_guard: Some(ExitGuard::DoneFlag),
                        ..
                    } => Some(*label),
                    _ => None,
                })
                .collect();
            assert!(!guards.is_empty(), "{}", inlined.listing.text);
            for guard in guards {
                assert!(folded.labels.contains(&guard), "L{guard}\n{}", folded.text);
            }
            assert_lines_come_from_their_labels(&inlined, &folded);
        });
    }

    #[test]
    fn a_side_tree_with_free_parameters_folds_only_literal_conditions() {
        // Full4WHS has no instance named `Hybrid2`, so the side tree's free instance can take it
        with_theorem(FOUR_WHS, "Full4WHS", |theorem| {
            let files = DirectoryFiles::load(Path::new(FOUR_WHS)).unwrap();
            let project = DirectoryProject::load(PathBuf::from(FOUR_WHS), &files).unwrap();
            let comp = project.get_game("Hybrid2").unwrap();
            let (free, _) = crate::debug::side_run::free_theorem(theorem, comp).unwrap();
            let (ec, _) = EasyCryptTransform.transform_theorem(&free).unwrap();
            let inlined =
                inline_oracle_ec(ec.find_game_instance("Hybrid2").unwrap(), "Send2").unwrap();
            let folded = FoldedListing::of(&inlined);
            // `bprf` is free: the ideal branch of `Prf.Eval` stays
            assert!(folded.text.contains("Prf.d_PRF.["), "{}", folded.text);
            for branch in branches(&inlined.body) {
                let InlStmt::Branch {
                    label,
                    cond,
                    is_assert: false,
                    exit_guard: None,
                    ..
                } = branch
                else {
                    continue;
                };
                assert_eq!(known_value(cond), condition_value(cond), "L{label}");
            }
            assert_lines_come_from_their_labels(&inlined, &folded);
        });
    }
}
