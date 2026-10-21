// SPDX-License-Identifier: MIT OR Apache-2.0

use miette::Diagnostic;
use std::path::PathBuf;
use thiserror::Error;

use crate::util::smtsolver::{Result as SmtSolverResponseResult, SmtSolverResponse};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error, Diagnostic)]
pub enum Error {
    #[error("there is no composition named {composition} in this project")]
    #[diagnostic(help("known compositions: {}", .known_compositions.join(", ")))]
    UnknownComposition {
        composition: String,
        known_compositions: Vec<String>,
    },

    #[error("composition `{composition}` has no game invariant")]
    #[diagnostic(help(
        "its package invariants are proved with `--package`. To give it a game invariant, add \
         an `invariant: [ ./path/to/file.smt2 ]` entry to the composition."
    ))]
    NoGameInvariant { composition: String },

    #[error("composition {composition} does not export an oracle named {oracle_name}")]
    #[diagnostic(help("exports of {composition}: {}", .known_oracle_names.join(", ")))]
    UnknownOracle {
        composition: String,
        oracle_name: String,
        known_oracle_names: Vec<String>,
    },

    #[error(transparent)]
    #[diagnostic(transparent)]
    Transform(#[from] crate::transforms::theorem_transforms::EquivalenceTransformError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    Invariant(#[from] Box<crate::gamehops::equivalence::error::Error>),

    #[error(transparent)]
    ClaimFailed(#[from] ClaimFailedError),

    #[error("failed to prove the game invariants of composition {composition}")]
    Parallel {
        composition: String,

        #[related]
        failed_claims: Vec<Error>,
    },

    #[error("SMT solver failed when verifying {claim_group_name} of composition {composition}")]
    ProverProcess {
        composition: String,
        claim_group_name: String,
        #[related]
        solver_errors: Vec<crate::util::smtsolver::Error>,
    },
}

impl Error {
    pub(crate) fn prover_process(
        composition: &str,
        claim_group_name: &str,
        err: crate::util::smtsolver::Error,
    ) -> Self {
        Self::ProverProcess {
            composition: composition.to_string(),
            claim_group_name: claim_group_name.to_string(),
            solver_errors: vec![err],
        }
    }
}

#[derive(Debug, Error, Diagnostic)]
#[error("the game invariant {claim_name} of composition {composition} could not be proved for {claim_group_name} (solver said {response})")]
#[diagnostic(help("{}", format_modelfile(.modelfile)))]
pub struct ClaimFailedError {
    pub composition: String,
    pub claim_group_name: String,
    pub claim_name: String,
    pub response: SmtSolverResponse,
    pub modelfile: SmtSolverResponseResult<PathBuf>,
}

fn format_modelfile(modelfile: &SmtSolverResponseResult<PathBuf>) -> String {
    match modelfile {
        Ok(path) => format!("the model is at {}", path.display()),
        Err(err) => format!("could not get a model from the solver: {err}"),
    }
}
