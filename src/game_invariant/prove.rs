// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    project::Project,
    transforms::{theorem_transforms::EquivalenceTransform, TheoremTransform},
    ui::{indicatif::IndicatifTheoremUI, TheoremUI},
    util::smtsolver::SmtSolverBackend,
    writers::smt::contexts::EquivalenceContext,
};

use super::error::{Error, Result};
use super::free::{claims, composition_theorem};
use super::verify::{assumed_packages, assumption_line, GameInvariantSmtDriver, UI_SECTION_NAME};

/// What `domino prove --game` selects.
pub struct GameRequest<'r> {
    /// The composition (as in `games/C.comp.ssp`), not a game instance.
    pub composition: &'r str,
    /// `--oracle`: only the claim group of this export.
    pub oracle: Option<&'r str>,
    /// `--invariant-start`: only the start group.
    pub invariant_start: bool,
    pub transcript: bool,
    pub parallel: usize,
}

/// `domino prove --game C`: proves each game invariant of composition `C`, for every value of
/// its parameters, with no theorem. The UI has one section with one row for `C`. When an
/// instance of `C` has a package invariant, one line names the package invariants that the
/// check assumes.
///
/// Errors: [`Error::UnknownComposition`] (the help lists the compositions),
/// [`Error::NoGameInvariant`], [`Error::UnknownOracle`] (the help lists the exports of `C`),
/// and [`Error::Parallel`] when a claim is not proved.
pub fn prove_game<P: Project + Sync>(
    project: &P,
    backend: &(impl SmtSolverBackend + Sync),
    req: &GameRequest<'_>,
) -> Result<()> {
    let composition = req.composition;
    let Some(comp) = project.get_game(composition) else {
        let mut known_compositions: Vec<String> = project.games().map(str::to_string).collect();
        known_compositions.sort();
        return Err(Error::UnknownComposition {
            composition: composition.to_string(),
            known_compositions,
        });
    };

    let (theorem, eq) = composition_theorem(comp);
    let (theorem_eq, auxs_eq) = EquivalenceTransform.transform_theorem(&theorem)?;
    let mut eqctx = EquivalenceContext::new(&eq, &theorem_eq, &auxs_eq);
    eqctx.load_invariants(project).map_err(Box::new)?;
    if claims(&eqctx).is_empty() {
        return Err(Error::NoGameInvariant {
            composition: composition.to_string(),
        });
    }

    let mut ui = IndicatifTheoremUI::new(1);
    if let Some(line) = assumption_line(&assumed_packages(comp)) {
        println!("{line}");
    }
    ui.start_theorem(UI_SECTION_NAME, 1);
    ui.start_proofstep(UI_SECTION_NAME, composition);
    GameInvariantSmtDriver::new(
        &eqctx,
        comp,
        project,
        backend,
        req.transcript,
        req.oracle,
        req.parallel,
        req.invariant_start,
    )
    .verify(&mut ui)?;
    ui.finish_proofstep(UI_SECTION_NAME, composition);
    ui.finish_theorem(UI_SECTION_NAME);
    Ok(())
}
