// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    gamehops::equivalence::Equivalence,
    util::smtsolver::{Result as SmtSolverResponseResult, SmtSolverResponse},
};

use itertools::Itertools;
use miette::Diagnostic;
use std::path::PathBuf;
use thiserror::Error;

#[derive(Debug, Error, Diagnostic)]
pub enum Error {
    // #[error(
    //     "It seems the provided invariant file for the equivalence of \
    //      game instances {left_game_inst_name} and {right_game_inst_name} \
    //      contains unsatisfiable assert statements at oracle {oracle_name}. \
    //      This is most likely an issue with the invariant file. \
    //      Hint: Most invariant file should not contains assert statements at all."
    // )]
    #[error("It seems the provided invariant file for the equivalence {} = {} contains unsatisfiable assert statements at oracle {oracle_name}.", equivalence.left_name(), equivalence.right_name())]
    UnsatAfterInvariantRead {
        equivalence: Equivalence,
        oracle_name: String,
    },
    #[error("error reading invariant file {invariant_file_name}: {err}")]
    InvariantFileReadError {
        invariant_file_name: String,
        err: std::io::Error,
    },
    #[error("parameter {mismatching_param_name} does not match in equivalence theorem of game instances {left_game_inst_name} and {right_game_inst_name}")]
    CompositionParamMismatch {
        left_game_inst_name: String,
        right_game_inst_name: String,
        mismatching_param_name: String,
    },
    #[error("neither game instance {left_game_inst_name} nor {right_game_inst_name} exports any oracles")]
    #[diagnostic(help(
        "an equivalence needs both game instances to export at least one oracle. \
         check that each composition declares an `adversary: {{ ... }}` block."
    ))]
    NoOraclesExported {
        left_game_inst_name: String,
        right_game_inst_name: String,
    },
    #[error("game instances {left_game_inst_name} and {right_game_inst_name} in this equivalence theorem do not export the same oracles")]
    #[diagnostic(help("{}", format_export_name_mismatch(.left_game_inst_name, .right_game_inst_name, .only_left, .only_right)))]
    CompositionExportsMismatch {
        left_game_inst_name: String,
        right_game_inst_name: String,
        /// oracle names (after aliasing) exported only by the left game instance
        only_left: Vec<String>,
        /// oracle names (after aliasing) exported only by the right game instance
        only_right: Vec<String>,
    },
    #[error("oracle(s) {} are exported with different signatures by game instances {left_game_inst_name} and {right_game_inst_name}", .mismatches.iter().map(|mismatch| mismatch.oracle_name.as_str()).join(", "))]
    #[diagnostic(help("{}", format_export_signature_mismatch(.left_game_inst_name, .right_game_inst_name, .mismatches)))]
    CompositionExportSignatureMismatch {
        left_game_inst_name: String,
        right_game_inst_name: String,
        mismatches: Vec<ExportSignatureMismatch>,
    },
    #[error("the oracles declared in the equivalence of {left_game_inst_name} and {right_game_inst_name} do not match the oracles exported by the games")]
    #[diagnostic(help("{}", format_equivalence_oracle_mismatch(.missing_oracle_names, .unknown_oracle_names)))]
    EquivalenceOraclesMismatch {
        left_game_inst_name: String,
        right_game_inst_name: String,
        /// exported oracles that have no entry in the equivalence block
        missing_oracle_names: Vec<String>,
        /// entries in the equivalence block that are not exported oracles
        unknown_oracle_names: Vec<String>,
    },
    #[error(transparent)]
    ClaimTheoremFailed(#[from] ClaimTheoremFailedError),
    #[error("Failed to prove equivalence {left_game_inst_name} = {right_game_inst_name}")]
    ParallelEquivalenceError {
        left_game_inst_name: String,
        right_game_inst_name: String,

        #[related]
        failed_claims: Vec<Error>,
    },
    #[error("found lemma named \"{lemma_name}\". Expected name ending in the name of the oracle. followed by a closing angle bracket")]
    IllegalLemmaName { lemma_name: String },
    #[error("found lemma named \"{lemma_name}\" for oracle \"{oracle_name}\" but couldn't find matching oracle")]
    UnknownLemmaName {
        lemma_name: String,
        oracle_name: String,
    },
    #[error("{equivalence}: Expected symbol name for argument but got {argument}")]
    IncorrectArgument {
        argument: String,
        equivalence: String,
    },
    #[error("{equivalence}: Expected {expected} arguments but found {argument}")]
    IncorrectNumberOfArguments {
        argument: String,
        expected: String,
        equivalence: String,
    },
    #[error("define-game-invariant only valid in game contexts: {defn}")]
    RewriteNeedsGameContext { defn: String },
    #[error("define-package-invariant only valid in package contexts: {defn}")]
    RewriteNeedsPackageContext { defn: String },
    #[error(transparent)]
    ParserError(#[from] crate::util::smtparser::Error),
    #[error("SMT Solver failed in claim {claim_name} when verifying {claim_group_name}")]
    ProverProcessError {
        claim_name: String,
        claim_group_name: String,
        #[related]
        solver_errors: Vec<crate::util::smtsolver::Error>,
    },
    #[error("could not synthesize an invariant for {scope} of the equivalence {left_game_inst_name} = {right_game_inst_name}. solver answered: {answer}")]
    #[diagnostic(help("the synthesis query is in {}", .query_file.display()))]
    InvariantSynthesisFailed {
        left_game_inst_name: String,
        right_game_inst_name: String,
        scope: String,
        answer: String,
        query_file: PathBuf,
    },
    #[error("cannot synthesize an invariant for oracle {oracle_name}, because game instances {left_game_inst_name} and {right_game_inst_name} don't export it")]
    #[diagnostic(help("exported oracles: {}", .exported_oracle_names.iter().join(", ")))]
    InvariantSynthesisUnknownOracle {
        oracle_name: String,
        left_game_inst_name: String,
        right_game_inst_name: String,
        exported_oracle_names: Vec<String>,
    },
    #[error("cannot synthesize an invariant for claim {claim_pattern}, because no claim of oracle {oracle_name} matches it")]
    #[diagnostic(help("claims of oracle {oracle_name}: {}", .available_claim_names.iter().join(", ")))]
    InvariantSynthesisUnknownClaim {
        claim_pattern: String,
        oracle_name: String,
        available_claim_names: Vec<String>,
    },
    #[error("synthesizing an invariant for claim {claim_pattern} needs an oracle")]
    #[diagnostic(help(
        "claims belong to the proof tree of an oracle. pass the oracle with --oracle"
    ))]
    InvariantSynthesisClaimWithoutOracle { claim_pattern: String },
    #[error("error accessing {} during invariant synthesis", .path.display())]
    InvariantSynthesisIo {
        path: PathBuf,
        #[source]
        err: std::io::Error,
    },
    #[error("error running {solver} for invariant synthesis")]
    #[diagnostic(help("SyGuS invariant synthesis needs {solver} on the PATH"))]
    InvariantSynthesisSolverSpawn {
        solver: &'static str,
        #[source]
        err: std::io::Error,
    },
}

impl Error {
    pub(super) fn prover_process_error(
        claim_name: &str,
        claim_group_name: &str,
        err: crate::util::smtsolver::Error,
    ) -> Self {
        Self::ProverProcessError {
            claim_name: claim_name.to_string(),
            claim_group_name: claim_group_name.to_string(),
            solver_errors: vec![err],
        }
    }
}

#[derive(Debug, Error, Diagnostic)]
#[error("{claim_group_name}: error proving claim {claim_name}. status: {response}. modelfile {}",
        if let Ok(modfile) = modelfile {modfile.to_str().unwrap()} else {""})]
pub struct ClaimTheoremFailedError {
    pub claim_name: String,
    pub claim_group_name: String,
    pub response: SmtSolverResponse,
    pub modelfile: SmtSolverResponseResult<PathBuf>,
}

/// An oracle that both game instances of an equivalence export, but with differing signatures.
#[derive(Debug, Clone)]
pub struct ExportSignatureMismatch {
    /// the name the oracle is exported under, i.e. the alias if there is one
    pub oracle_name: String,
    /// the signature the left game instance exports, rendered as `oracle (<args>) -> <ret>`
    pub left_sig: String,
    /// the signature the right game instance exports, rendered as `oracle (<args>) -> <ret>`
    pub right_sig: String,
}

fn format_export_name_mismatch(
    left_game_inst_name: &str,
    right_game_inst_name: &str,
    only_left: &[String],
    only_right: &[String],
) -> String {
    let mut help = String::new();

    if !only_left.is_empty() {
        help.push_str(&format!(
            "only exported by {left_game_inst_name}: {}\n",
            only_left.iter().join(", ")
        ));
    }
    if !only_right.is_empty() {
        help.push_str(&format!(
            "only exported by {right_game_inst_name}: {}\n",
            only_right.iter().join(", ")
        ));
    }

    help.push_str(
        "both game instances need to export the same set of oracle names. \
         note that an export with an alias is matched by its alias, not by the original oracle name.",
    );

    help
}

fn format_export_signature_mismatch(
    left_game_inst_name: &str,
    right_game_inst_name: &str,
    mismatches: &[ExportSignatureMismatch],
) -> String {
    mismatches
        .iter()
        .map(|mismatch| {
            let ExportSignatureMismatch {
                oracle_name,
                left_sig,
                right_sig,
            } = mismatch;

            format!(
                "{oracle_name}:\n  {left_game_inst_name}: {left_sig}\n  {right_game_inst_name}: {right_sig}"
            )
        })
        .join("\n")
}

fn format_equivalence_oracle_mismatch(
    missing_oracle_names: &[String],
    unknown_oracle_names: &[String],
) -> String {
    let mut help = String::new();

    if !missing_oracle_names.is_empty() {
        help.push_str(&format!(
            "exported, but not declared in the equivalence: {}\n",
            missing_oracle_names.iter().join(", ")
        ));
    }
    if !unknown_oracle_names.is_empty() {
        help.push_str(&format!(
            "declared in the equivalence, but not exported by the games: {}\n",
            unknown_oracle_names.iter().join(", ")
        ));
    }

    help.push_str("the equivalence needs to declare exactly the exported oracles, one entry per exported oracle name.");

    help
}

pub type Result<T> = std::result::Result<T, Error>;

pub(crate) fn new_invariant_file_read_error(
    invariant_file_name: String,
    err: std::io::Error,
) -> Error {
    Error::InvariantFileReadError {
        invariant_file_name,
        err,
    }
}
