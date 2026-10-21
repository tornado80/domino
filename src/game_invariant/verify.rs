// SPDX-License-Identifier: MIT OR Apache-2.0

use std::io::Write as _;
use std::sync::{Arc, Mutex};

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::{
    debug::claims::ClaimQuery,
    invariant_claim::select,
    package::Composition,
    project::Project,
    theorem::ResolvedClaim,
    ui::TheoremUI,
    util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse},
    writers::smt::{contexts::EquivalenceContext, exprs::SmtExpr},
};

use super::error::{ClaimFailedError, Error, Result};
use super::free::{claims, oracle_frame};

/// The name the game invariant checks appear under in the UI, in place of a theorem name.
pub(crate) const UI_SECTION_NAME: &str = "Game Invariants";

/// One thing we prove about the game invariants of a composition.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ClaimGroup {
    /// each game invariant holds after `init`
    InvariantStart,
    /// each game invariant is preserved by a call to this exported oracle
    Oracle { oracle_name: String },
}

impl ClaimGroup {
    fn ui_name(&self) -> &str {
        match self {
            Self::InvariantStart => "invariant-start",
            Self::Oracle { oracle_name } => oracle_name,
        }
    }

    fn file_system_name(&self) -> String {
        match self {
            Self::InvariantStart => "!invariant-start!".to_string(),
            Self::Oracle { oracle_name } => oracle_name.clone(),
        }
    }
}

/// The packages of the instances of `comp` that declare an invariant, sorted and each once:
/// `domino prove --game` assumes their invariants.
pub(crate) fn assumed_packages(comp: &Composition) -> Vec<String> {
    let mut names: Vec<String> = comp
        .pkgs
        .iter()
        .filter(|inst| !inst.pkg.invariants.is_empty())
        .map(|inst| inst.pkg.name.clone())
        .collect();
    names.sort();
    names.dedup();
    names
}

/// The report line that names the package invariants a game-invariant check assumes; `None`
/// when no instance of the composition has a package invariant.
pub(crate) fn assumption_line(packages: &[String]) -> Option<String> {
    let first = packages.first()?;
    Some(format!(
        "assumes the package invariants of {}; prove them with domino prove --package {first}",
        packages.join(", ")
    ))
}

/// Proves the game invariants of one composition, on the free composition of
/// [`super::free`], for every value of its parameters.
///
/// `eqctx` is the context of `C` against `C$side`, with the invariants loaded. Only the left
/// side is read: the encoding is that of the side tree.
pub(crate) struct GameInvariantSmtDriver<'a, Backend: SmtSolverBackend + Sync, Proj: Project + Sync>
{
    eqctx: &'a EquivalenceContext<'a>,
    comp: &'a Composition,
    project: &'a Proj,
    backend: &'a Backend,
    transcript: bool,
    req_oracle: Option<&'a str>,
    req_claim: Option<&'a str>,
    parallel: usize,
    invariant_start_only: bool,
}

impl<'a, Backend: SmtSolverBackend + Sync, Proj: Project + Sync>
    GameInvariantSmtDriver<'a, Backend, Proj>
{
    /// `req_claim` is the `--claim` pattern on the declared game invariant names
    /// ([`crate::invariant_claim`]); `None` proves every game invariant.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        eqctx: &'a EquivalenceContext<'a>,
        comp: &'a Composition,
        project: &'a Proj,
        backend: &'a Backend,
        transcript: bool,
        req_oracle: Option<&'a str>,
        req_claim: Option<&'a str>,
        parallel: usize,
        invariant_start_only: bool,
    ) -> Self {
        Self {
            eqctx,
            comp,
            project,
            backend,
            transcript,
            req_oracle,
            req_claim,
            parallel,
            invariant_start_only,
        }
    }

    /// The claim groups to verify, by `--oracle` and `--invariant-start`.
    ///
    /// Errors: [`Error::UnknownOracle`] when `--oracle` names no export of the composition.
    fn claim_groups(&self) -> Result<Vec<ClaimGroup>> {
        if self.invariant_start_only {
            return Ok(vec![ClaimGroup::InvariantStart]);
        }
        let oracle_names: Vec<String> = self
            .comp
            .exports
            .iter()
            .map(|e| e.name().to_string())
            .collect();
        if let Some(req_oracle) = self.req_oracle {
            if !oracle_names.iter().any(|name| name == req_oracle) {
                return Err(Error::UnknownOracle {
                    composition: self.comp.name.clone(),
                    oracle_name: req_oracle.to_string(),
                    known_oracle_names: oracle_names,
                });
            }
            return Ok(vec![ClaimGroup::Oracle {
                oracle_name: req_oracle.to_string(),
            }]);
        }
        Ok(std::iter::once(ClaimGroup::InvariantStart)
            .chain(
                oracle_names
                    .into_iter()
                    .map(|oracle_name| ClaimGroup::Oracle { oracle_name }),
            )
            .collect())
    }

    /// Verifies each claim group for the game invariants that `--claim` selects. Each query
    /// still assumes all package and game invariants on the old state. The caller has made
    /// sure that the composition has a game invariant.
    pub(crate) fn verify<UI: TheoremUI + Send>(&self, ui: &mut UI) -> Result<()> {
        let composition = self.comp.name.as_str();
        let claim_groups = self.claim_groups()?;
        let claims = select(claims(self.eqctx), self.req_claim, composition)?;
        log::info!("verify: game invariants of {composition}");

        let ui = Arc::new(Mutex::new(ui));
        ui.lock().unwrap().proofstep_set_claim_groups_count(
            UI_SECTION_NAME,
            composition,
            claim_groups.len().try_into().unwrap(),
        );

        let results: Vec<Result<()>> = rayon::ThreadPoolBuilder::new()
            .num_threads(self.parallel + 1) // one thread is reserved for the "main" method
            .build()
            .unwrap()
            .install(|| {
                claim_groups
                    .par_iter()
                    .map(|group| self.verify_claim_group(ui.clone(), &claims, group))
                    .collect()
            });

        let failed_claims: Vec<_> = results.into_iter().filter_map(Result::err).collect();
        if !failed_claims.is_empty() {
            return Err(Error::Parallel {
                composition: composition.to_string(),
                failed_claims,
            });
        }
        Ok(())
    }

    /// The query of `claim` in `group`: the frame, then the claim's dependencies and its negated
    /// goal, as the side tree checks them at a terminal.
    fn query(&self, claim: &ResolvedClaim, group: &ClaimGroup) -> Vec<SmtExpr> {
        match group {
            ClaimGroup::InvariantStart => {
                let mut smt = self.start_frame();
                smt.push(
                    self.eqctx
                        .emit_game_or_package_invariant_start_assert(claim),
                );
                smt
            }
            ClaimGroup::Oracle { oracle_name } => {
                let mut smt = oracle_frame(self.eqctx, oracle_name);
                let query = ClaimQuery::of(self.eqctx, claim, oracle_name);
                smt.extend(query.dependencies.into_iter().map(|(_, assert)| assert));
                smt.push(query.negated);
                smt
            }
        }
    }

    /// The declarations and definitions, the constants, the invariants and the initial state.
    fn start_frame(&self) -> Vec<SmtExpr> {
        let mut smt = self.eqctx.emit_base_declarations();
        smt.extend(self.eqctx.emit_theorem_paramfuncs());
        smt.extend(self.eqctx.emit_game_definitions());
        smt.extend(self.eqctx.emit_constant_declarations(None));
        smt.extend(self.eqctx.emit_invariant());
        smt.extend(self.eqctx.emit_initial_state_values());
        smt
    }

    /// Checks each game invariant in `group`, one solver query each.
    fn verify_claim_group<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        claims: &[ResolvedClaim],
        group: &ClaimGroup,
    ) -> Result<()> {
        let composition = self.comp.name.as_str();
        let group_name = group.ui_name();
        ui.lock().unwrap().start_claim_group(
            UI_SECTION_NAME,
            composition,
            group_name,
            claims.len().try_into().unwrap(),
        );

        let mut result = Ok(());
        for claim in claims {
            ui.lock()
                .unwrap()
                .start_claim(UI_SECTION_NAME, composition, group_name, claim.name());
            let claim_result =
                self.verify_with_solver(self.query(claim, group), group, claim.name());
            ui.lock()
                .unwrap()
                .finish_claim(UI_SECTION_NAME, composition, group_name, claim.name());
            if result.is_ok() {
                result = claim_result;
            }
        }

        ui.lock()
            .unwrap()
            .finish_claim_group(UI_SECTION_NAME, composition, group_name);
        result
    }

    fn verify_with_solver(
        &self,
        smt: Vec<SmtExpr>,
        group: &ClaimGroup,
        claim_name: &str,
    ) -> Result<()> {
        let composition = self.comp.name.as_str();
        let group_name = group.ui_name();
        let process_err = |err| Error::prover_process(composition, group_name, err);

        let mut solver = if self.transcript {
            let transcript_file = self
                .project
                .get_game_invariant_smt_file(
                    composition,
                    &format!("{}-{claim_name}", group.file_system_name()),
                )
                .unwrap();
            self.backend.new_smtsolver_with_transcript(transcript_file)
        } else {
            self.backend.new_smtsolver()
        }
        .map_err(process_err)?;

        for entry in smt {
            solver.write_smt(entry).map_err(process_err)?;
        }

        match solver.check_sat().map_err(process_err)? {
            SmtSolverResponse::Unsat => Ok(()),
            response => {
                let modelfile = solver.get_model().map(|(modelstring, _model)| {
                    let mut modelfile =
                        tempfile::Builder::new().suffix(".smt2").tempfile().unwrap();
                    modelfile.write_all(modelstring.as_bytes()).unwrap();
                    let (_, fname) = modelfile.keep().unwrap();
                    fname
                });
                solver.close();
                Err(ClaimFailedError {
                    composition: composition.to_string(),
                    claim_group_name: group_name.to_string(),
                    claim_name: claim_name.to_string(),
                    response,
                    modelfile,
                }
                .into())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_assumption_line_names_each_package_and_the_command() {
        let line = assumption_line(&["P".to_string(), "Q".to_string()]).unwrap();
        assert_eq!(
            line,
            "assumes the package invariants of P, Q; prove them with domino prove --package P"
        );
        assert_eq!(assumption_line(&[]), None);
    }
}
