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
mod prove;
mod verify;

pub(crate) use free::{base_frame, claims, free_theorem};
pub use prove::{prove_game, GameRequest};
