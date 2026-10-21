// SPDX-License-Identifier: MIT OR Apache-2.0

//! The game invariants of a composition, on their own (symbolic-execution story 30, ADR 0021).
//!
//! A game invariant is a property of the state of a composition `C`. `domino prove --game C`
//! proves each game invariant of `C` for every value of the parameters of `C`, with no theorem,
//! by induction over the exported oracles of `C`:
//!
//!  * *invariant start*: each game invariant holds after `init`, and
//!  * *one claim group per oracle*: if all package invariants of the instances of `C` and all
//!    game invariants of `C` hold on the old state, and the call does not abort, then each game
//!    invariant holds on the new state.
//!
//! The package invariants are assumed. `domino prove --package P` proves them (ADR 0016).
//!
//! [`free`] owns the free composition (`C` and its copy `C$side`). The side tree of
//! `domino easycrypt debug --side-inv C` reads the same claims and base frame.

pub mod error;

mod free;
mod lookup;
mod prove;
mod verify;

/// The line that names the package invariants which a game-invariant check of `comp`
/// assumes; `None` when no instance of `comp` has a package invariant.
pub(crate) fn assumption_note(comp: &crate::package::Composition) -> Option<String> {
    verify::assumption_line(&verify::assumed_packages(comp))
}

pub(crate) use free::{base_frame, claims, composition_theorem, free_theorem};
pub(crate) use lookup::{check_export, composition_of, export_names};
pub use prove::{prove_game, GameRequest};
