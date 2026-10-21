// SPDX-License-Identifier: MIT OR Apache-2.0

//! The checks that `domino prove --game C` and `domino debug --game C` share (stories 30, 32):
//! the composition exists, and it exports the oracle.

use crate::package::Composition;
use crate::project::Project;

use super::error::{Error, Result};

/// The composition `name` (as in `games/C.comp.ssp`).
///
/// Errors: [`Error::UnknownComposition`]; its help lists the compositions of the project.
pub(crate) fn composition_of<'p, P: Project>(
    project: &'p P,
    name: &str,
) -> Result<&'p Composition> {
    project.get_game(name).ok_or_else(|| {
        let mut known_compositions: Vec<String> = project.games().map(str::to_string).collect();
        known_compositions.sort();
        Error::UnknownComposition {
            composition: name.to_string(),
            known_compositions,
        }
    })
}

/// The names of the exported oracles of `comp`, in declaration order.
pub(crate) fn export_names(comp: &Composition) -> Vec<String> {
    comp.exports.iter().map(|e| e.name().to_string()).collect()
}

/// Makes sure that `comp` exports `oracle`.
///
/// Errors: [`Error::UnknownOracle`]; its help lists the exports of `comp`.
pub(crate) fn check_export(comp: &Composition, oracle: &str) -> Result<()> {
    let known_oracle_names = export_names(comp);
    if known_oracle_names.iter().any(|name| name == oracle) {
        return Ok(());
    }
    Err(Error::UnknownOracle {
        composition: comp.name.clone(),
        oracle_name: oracle.to_string(),
        known_oracle_names,
    })
}
