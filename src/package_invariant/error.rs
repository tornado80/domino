// SPDX-License-Identifier: MIT OR Apache-2.0

use miette::Diagnostic;
use std::path::PathBuf;
use thiserror::Error;

use crate::util::smtsolver::{Result as SmtSolverResponseResult, SmtSolverResponse};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error, Diagnostic)]
pub enum Error {
    #[error("there is no package named {pkg_name} in this project")]
    #[diagnostic(help("known packages: {}", .known_pkg_names.join(", ")))]
    UnknownPackage {
        pkg_name: String,
        known_pkg_names: Vec<String>,
    },

    #[error("package {pkg_name} does not declare an invariant")]
    #[diagnostic(help(
        "add an `invariant: [ ./path/to/file.smt2 ]` entry to the package to give it one."
    ))]
    NoInvariant { pkg_name: String },

    #[error("package {pkg_name} does not have an oracle named {oracle_name}")]
    #[diagnostic(help("oracles of {pkg_name}: {}", .known_oracle_names.join(", ")))]
    UnknownOracle {
        pkg_name: String,
        oracle_name: String,
        known_oracle_names: Vec<String>,
    },

    #[error("oracle {oracle_name} of package {pkg_name} calls an import in a loop that could not be unrolled")]
    #[diagnostic(help(
        "the package check gives each import call site its own outcome (ADR 0017), so it needs \
         every call site once. Give this loop literal integer bounds."
    ))]
    OpenCallInLoop {
        pkg_name: String,
        oracle_name: String,
        #[source_code]
        src: miette::NamedSource<String>,
        #[label("this loop calls an import")]
        at: miette::SourceSpan,
    },

    #[error("error reading invariant file {invariant_file_name}: {err}")]
    InvariantFileRead {
        invariant_file_name: String,
        err: std::io::Error,
    },

    #[error(transparent)]
    #[diagnostic(transparent)]
    InvariantRewrite(#[from] Box<crate::gamehops::equivalence::error::Error>),

    #[error(transparent)]
    ClaimFailed(#[from] ClaimFailedError),

    #[error("failed to prove the invariant of package {pkg_name}")]
    Parallel {
        pkg_name: String,

        #[related]
        failed_claims: Vec<Error>,
    },

    #[error("SMT solver failed when verifying {claim_group_name} of package {pkg_name}")]
    ProverProcess {
        pkg_name: String,
        claim_group_name: String,
        #[related]
        solver_errors: Vec<crate::util::smtsolver::Error>,
    },
}

impl Error {
    pub(crate) fn prover_process(
        pkg_name: &str,
        claim_group_name: &str,
        err: crate::util::smtsolver::Error,
    ) -> Self {
        Self::ProverProcess {
            pkg_name: pkg_name.to_string(),
            claim_group_name: claim_group_name.to_string(),
            solver_errors: vec![err],
        }
    }
}

#[derive(Debug, Error, Diagnostic)]
#[error("the invariant {claim_name} of package {pkg_name} could not be proved for {claim_group_name} (solver said {response})")]
#[diagnostic(help("{}", format_modelfile(.modelfile)))]
pub struct ClaimFailedError {
    pub pkg_name: String,
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
