// SPDX-License-Identifier: MIT OR Apache-2.0

//! Support code for the symbolic-execution proof debugger (`domino debug` /
//! `domino inline`).
//!
//! [`ir`] holds the AST-level inlined representation of one exported oracle,
//! together with the textual listing its line-number labels index into.
//! [`view`] renders the same inlining as readable code for `domino html`.

pub mod claims;
pub mod driver;
pub mod effect;
pub mod exec;
pub mod fold;
pub mod game_run;
pub mod index;
mod inline_rules;
pub mod ir;
pub mod layout;
pub mod lockstep;
pub mod lockstep_fingerprint;
pub mod lockstep_report;
pub mod lockstep_run;
pub mod lockstep_viewer;
pub mod pkg_run;
pub mod progress;
pub mod render;
pub mod report;
pub mod side;
pub mod side_run;
pub mod smtout;
pub mod sweep;
pub mod view;

#[cfg(test)]
mod easycryptify_differential;
