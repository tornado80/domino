// SPDX-License-Identifier: MIT OR Apache-2.0

use clap::Subcommand;
use sspverif::util::smtsolver::process::SolverVariant;

#[derive(Subcommand, Debug)]
pub(crate) enum Commands {
    /// Export to LaTeX
    Latex(Latex),

    /// Prove the whole project.
    Prove(Prove),

    /// Reformat file or directory
    Format(Format),

    Proofsteps(Proofsteps),
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Format {
    /// Input to reformat
    pub(crate) input: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Latex {
    /// Solver for graph layouting
    /// TODO: given we have a default here, it seems impossible to choose none
    #[clap(short, long, default_value = "z3")]
    pub(crate) smtsolver: Option<SolverVariant>,
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Prove {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
    #[clap(short, long, default_value = "cvc5")]
    pub(crate) smtsolver: SolverVariant,
    #[clap(short, long)]
    pub(crate) transcript: bool,
    // only check randomness mapping is injective
    #[clap(long)]
    pub(crate) injective_randmap: bool,
    #[clap(long)]
    pub(crate) invariant_start: bool,
    /// Instead of proving, synthesize an invariant with an SMT query: `invariant` is an
    /// uninterpreted function and each clause is a quantified assertion. Needs --proof and
    /// --proofstep. --oracle and --claim narrow down what the invariant has to prove.
    #[clap(
        long,
        requires = "proofstep",
        conflicts_with_all = ["invariant_synthesis_sygus", "invariant_start", "injective_randmap"]
    )]
    pub(crate) invariant_synthesis_smt: bool,
    /// Instead of proving, synthesize an invariant by posing the clauses as a SyGuS problem to
    /// cvc5. Needs --proof and --proofstep. --oracle and --claim narrow down what the invariant
    /// has to prove.
    #[clap(
        long,
        requires = "proofstep",
        conflicts_with_all = ["invariant_start", "injective_randmap"]
    )]
    pub(crate) invariant_synthesis_sygus: bool,
    #[clap(long)]
    pub(crate) proofstep: Option<usize>,
    #[clap(long)]
    pub(crate) proof: Option<String>,
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    #[clap(long)]
    pub(crate) claim: Option<String>,
    #[clap(long, default_value_t = 1)]
    pub(crate) parallel: usize,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Proofsteps {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
}
