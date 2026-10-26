// SPDX-License-Identifier: MIT OR Apache-2.0

use clap::Subcommand;
use sspverif::util::smtsolver::process::SolverVariant;

/// How `domino debug` and `domino easycrypt` (`export`, `prove`, `debug`) render live progress (on stderr).
#[derive(Copy, Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum ProgressMode {
    /// An `indicatif` bar on a terminal, plain stderr log lines when piped.
    Auto,
    /// One terse stderr line per `(left, right)` pair. For logs and CI.
    Plain,
    /// A live `indicatif` two-bar display (goes quiet when stderr is not a TTY).
    Bar,
    /// No progress output at all.
    None,
}

/// Which per-path SMT files `domino debug` writes under `<out>/smt/` (story 11).
#[derive(Copy, Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum SmtOutArg {
    /// Write nothing — no `smt/` directory.
    None,
    /// Self-contained, directly runnable `.smt2` for each goal-fails /
    /// inconclusive pair (the default).
    Failures,
    /// Self-contained files for every explored pair (large — one copy of the
    /// base frame per pair).
    All,
    /// `base.smt2` plus the small per-path deltas only; reassemble with `cat`.
    Deltas,
}

/// Which claims `domino debug` checks (story 23).
#[derive(Copy, Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum ClaimSetArg {
    /// Every claim of the game hop, each under its declared dependencies, as `domino prove`
    /// does (the default).
    Obligations,
    /// Only `equal-aborts`, `same-output`, `invariant` and the package and game invariants,
    /// each under its built-in dependencies only. Project lemmas are neither checked nor
    /// assumed, as in EasyCrypt.
    Core,
}

/// What `domino easycrypt prove` keeps of EasyCrypt's answers in
/// `progress/ec-transcript.jsonl` (story 31).
#[derive(Copy, Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum EcTranscriptArg {
    /// Each answer's front goal cut to what the live page shows: its conclusion to 4 000
    /// characters and its hypotheses to 1 000 (the default). A failed write drops the
    /// transcript with a warning.
    Capped,
    /// EasyCrypt's answers verbatim: the front goal in full and the kind of each open goal. A
    /// failed write fails the run.
    Full,
}

/// When `domino easycrypt prove` rewrites `Eq_*.ec` and its report (story 33).
#[derive(Copy, Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum WriteGranularityArg {
    /// After each oracle.
    Oracle,
    /// After every joint node too, the oracle in flight sealed: its open goals admitted,
    /// labelled `interrupted`.
    Node,
    /// After every sentence EasyCrypt accepts (the default): the oracle in flight sealed as for
    /// `node`. Rejected and timed-out sentences are never written.
    Tactic,
}

/// How `domino easycrypt prove` resumes an oracle the session record holds as `interrupted`
/// (ADR 0008).
#[derive(Copy, Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum ResumeArg {
    /// Walk the saved joint tree; each node the earlier job closed is closed with `admit.` and
    /// its recorded proof goes into the file unchecked (the default).
    Trust,
    /// As `trust`, but EasyCrypt checks each closed node's recorded proof again; a node whose
    /// proof is rejected is proved again.
    Replay,
    /// Prove the oracle from scratch, lockstep execution included.
    Restart,
}

#[derive(Subcommand, Debug)]
pub(crate) enum Commands {
    /// Export to LaTeX
    Latex(Latex),

    /// Prove the whole project.
    Prove(Prove),

    /// Reformat file or directory
    Format(Format),

    /// List the game hops of each theorem, with the index that `--gamehop` takes.
    Gamehops(Gamehops),

    /// Symbolically execute both sides of an equivalence game hop and debug one claim.
    Debug(Debug),

    /// Inline the code of an oracle for both sides of an equivalence game hop, side by side.
    Inline(Inline),

    /// Export one HTML page per theorem: every game instance's composition
    /// diagram and inlined oracles, one column per game in hop order.
    Html(Html),
    /// Export a Domino theorem to an EasyCrypt project.
    Easycrypt(Easycrypt),
}

/// `domino easycrypt`: the EasyCrypt export. `export` is **translation** (story 35, ADR 0006): it
/// writes an EasyCrypt project and runs no EasyCrypt. The other subcommands are proof jobs: they
/// never translate, they only make sure the files translation writes are there.
#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
#[clap(subcommand_required = true, arg_required_else_help = true)]
pub(crate) struct Easycrypt {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long, global = true)]
    pub(crate) project: Option<std::path::PathBuf>,
    /// Output directory holding one subdirectory per exported theorem.
    /// Defaults to `<project>/_build/easycrypt`.
    #[clap(long, global = true)]
    pub(crate) out: Option<std::path::PathBuf>,
    #[clap(subcommand)]
    pub(crate) command: EasycryptCommand,
}

/// `domino easycrypt export` (stories 35, 45): translation only. Runs no EasyCrypt.
#[derive(clap::Args, Debug)]
pub(crate) struct EcExport {
    /// Name of the theorem to export. Without it, every theorem in the
    /// project is exported.
    #[clap(long)]
    pub(crate) theorem: Option<String>,
    /// Overwrite what is already in `<out>/<theorem>/`. Without it the command refuses,
    /// before any other work, if a theorem's directory holds a file other than a run
    /// artifact (`progress/`, `!debug!/`, `*.report.txt`, `alignment.txt`) or `<out>`
    /// itself holds a file, and lists them. Proofs written by `domino easycrypt prove`, their
    /// session records and saved joint trees (`session/`, and the older `*.session.json` and
    /// `*.tree.json`) are discarded.
    #[clap(long)]
    pub(crate) force: bool,
    /// How the export reports what it is translating, on stderr (stdout and the written
    /// files are the same in every mode).
    #[clap(long, value_enum, default_value_t = ProgressMode::Auto)]
    pub(crate) progress: ProgressMode,
}

/// The subcommands of `domino easycrypt`: `export` is translation; the rest are proof jobs. A
/// proof job needs the translation's result in memory but writes none of translation's files over
/// what is there; a missing file is created.
#[derive(Subcommand, Debug)]
pub(crate) enum EasycryptCommand {
    /// Translate a theorem to an EasyCrypt project; runs no EasyCrypt.
    Export(EcExport),
    /// Prove as much of each oracle of an equivalence as possible against a live EasyCrypt.
    Prove(EcProve),
    /// Run lockstep execution on the EasyCrypt listing of every oracle.
    Debug(EcDebug),
    /// Check that the decision skeleton of every oracle's program after `proc; inline.`
    /// aligns with the one the debugger's lowering has.
    CheckAlignment(EcCheckAlignment),
}

/// `domino easycrypt prove` (stories 27, 35). Never run it on 4WHS or yao: it runs lockstep
/// execution, which is the debugger.
#[derive(clap::Args, Debug)]
pub(crate) struct EcProve {
    /// Name of the theorem to prove.
    #[clap(long)]
    pub(crate) theorem: String,
    /// Only this game hop (as printed by `domino gamehops`). Without it the game hops run
    /// one after another in this process; to run them at once start one process each. Its
    /// equivalence does not start when the side-invariant files `SideInv_<C>.ec` and
    /// `SideInv_<C>_<O>.ec` of one of its compositions are missing (a file with admits counts):
    /// prove them first with `--game <C>`. Without `--gamehop` and `--game`, the
    /// side-invariant jobs of the compositions run in parallel with the equivalences (story 69).
    #[clap(long, conflicts_with_all = ["game", "package"])]
    pub(crate) gamehop: Option<usize>,
    /// Only the side-invariant job of this composition: the lemma `SideInv_<C>_<O>.ec` of each
    /// of its oracles. Its game invariants are proved here, along the side tree of one-sided
    /// execution; its package invariants come from the package-invariant and frame lemmas of
    /// `--package`, which must exist first. Its records and pages are under
    /// `session/SideInv_<C>/` and `progress/SideInv_<C>/`.
    #[clap(long)]
    pub(crate) game: Option<String>,
    /// Only the package-invariant job of this package (story 76), for each variant of it that
    /// the theorem uses: the package-invariant lemma `PkgInv_<V>_<O>.ec` of each oracle, proved
    /// along the package tree with each import call an open call, then the frame lemmas
    /// `Frame_<V>_<O>.ec` and the start lemma `PkgInv_<V>_init.ec`. Its records and pages are
    /// under `session/PkgInv_<V>/` and `progress/PkgInv_<V>/`.
    #[clap(long, conflicts_with = "game")]
    pub(crate) package: Option<String>,
    /// Only this exported oracle; the rest keep what their session records hold, or
    /// `+ proc; inline. admit.`. Each oracle has its own lock, so jobs on different oracles of
    /// one equivalence can run at once.
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    /// How many oracles of an equivalence are proved at once, each in an EasyCrypt process of
    /// its own (story 68). Each worker has its own page and transcript under
    /// `progress/Eq_<L>_<R>/<O>/`.
    #[clap(long, default_value_t = 1)]
    pub(crate) jobs: usize,
    /// Discard the equivalence's session records and prove it again from the skeleton (with
    /// `--oracle O`: prove `O` again, keeping the other oracles' proofs). Without it a complete
    /// record skips the equivalence and a partial one is resumed: the oracles it holds are not
    /// proved again. Never rewrites a translation file: a stale one is fixed by
    /// `domino easycrypt export --force`. Overrides `--resume`.
    #[clap(long, short = 'f')]
    pub(crate) force: bool,
    /// How an oracle the session record holds as `interrupted` is resumed: on its saved joint
    /// tree, keeping the nodes the earlier job closed (`trust`, `replay`), or from scratch
    /// (`restart`). Oracles the record holds as done are never proved again.
    #[clap(long, value_enum, default_value_t = ResumeArg::Trust)]
    pub(crate) resume: ResumeArg,
    /// Seconds one EasyCrypt sentence may run before it is interrupted.
    #[clap(long, default_value_t = 60)]
    pub(crate) ec_timeout: u64,
    /// The seconds one leaf may spend being split by meaning before its remaining parts are
    /// admitted. Off unless given; each sentence is still bounded by `--ec-timeout`.
    #[clap(long)]
    pub(crate) leaf_budget: Option<u64>,
    /// Retry a part's closing sentence once, with this smt timeout in seconds, after it failed
    /// with `smt: timeout`. Off unless given; `--ec-timeout` must be at least this plus 10.
    #[clap(long, value_parser = clap::value_parser!(u32).range(1..))]
    pub(crate) smt_retry_timeout: Option<u32>,
    /// Skip the quick close (`auto => /#.` on every program goal), so the walk of the joint
    /// tree is exercised even where one tactic closes an oracle. For testing.
    #[clap(long, alias = "no-rung0")]
    pub(crate) no_quick_close: bool,
    /// What `progress/ec-transcript.jsonl` keeps of EasyCrypt's answers. Not `--transcript`,
    /// which is the solver transcript of `domino debug`/`prove`.
    #[clap(long, value_enum, default_value_t = EcTranscriptArg::Capped)]
    pub(crate) ec_transcript: EcTranscriptArg,
    /// When an oracle lemma file `Eq_<L>_<R>_<O>.ec` and its report are rewritten. The file on disk always holds what has been
    /// proved so far: `node` also writes after every joint node, `tactic` (the default) after
    /// every accepted sentence, the oracle in flight sealed (its open goals admitted, labelled
    /// `interrupted`).
    #[clap(long, value_enum, default_value_t = WriteGranularityArg::Tactic)]
    pub(crate) write_granularity: WriteGranularityArg,
    /// How the run reports what it is doing, on stderr.
    #[clap(long, value_enum, default_value_t = ProgressMode::Auto)]
    pub(crate) progress: ProgressMode,
}

/// `domino easycrypt check-alignment`: starts EasyCrypt (`DOMINO_EASYCRYPT`, an
/// `easycrypt cli -json` binary) on the export and compares skeletons. The base case is
/// admitted, so no prover runs. Exits non-zero on any mismatch and writes
/// `<out>/<theorem>/alignment.txt`.
#[derive(clap::Args, Debug)]
pub(crate) struct EcCheckAlignment {
    /// Name of the theorem to check.
    #[clap(long)]
    pub(crate) theorem: String,
    /// Only this game hop (as printed by `domino gamehops`).
    #[clap(long)]
    pub(crate) gamehop: Option<usize>,
    /// Only this exported oracle.
    #[clap(long)]
    pub(crate) oracle: Option<String>,
}

/// `domino easycrypt debug`: lockstep execution on the EasyCrypt listing of every oracle: both
/// oracles advance together and each decision is resolved jointly, as an EasyCrypt proof
/// would. Writes `<out>/<theorem>/!debug!/<left>-<right>/<oracle>/` (a page, a trace and the
/// runnable queries of what failed) and exits non-zero if any joint path fails equal-output or
/// the invariant. EasyCrypt has no `no-abort` and no project lemmas, so there are no claims to
/// choose: there is no `--claim`. Needs the `cvc5-lib` build. Never run it on 4WHS or yao: it
/// is the debugger.
#[derive(clap::Args, Debug)]
pub(crate) struct EcDebug {
    /// Name of the theorem to debug.
    #[clap(long)]
    pub(crate) theorem: String,
    /// Only this game hop (as printed by `domino gamehops`).
    #[clap(long)]
    pub(crate) gamehop: Option<usize>,
    /// Only this exported oracle.
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    /// One-sided execution of this composition instead of lockstep execution
    /// (symbolic-execution story 25): the side tree of each oracle (or of `--oracle`), with the
    /// composition's parameters free, written under `!debug!/SideInv_<C>/<oracle>/`.
    #[clap(long, conflicts_with = "gamehop")]
    pub(crate) game: Option<String>,
    /// One-sided execution of this package (symbolic-execution story 29): the package tree of
    /// each of its oracles (or of `--oracle`), with its parameters free and each import call an
    /// open call, written under `!debug!/PkgInv_<P>/<oracle>/`.
    #[clap(long, conflicts_with_all = ["gamehop", "game"])]
    pub(crate) package: Option<String>,
    /// Per-query solver timeout in milliseconds (cvc5 `tlimit-per`), as for
    /// `domino debug --timeout`. A timeout counts as `unknown`, never as verified.
    #[clap(long)]
    pub(crate) timeout: Option<u64>,
    /// How the run reports what it is doing, on stderr.
    #[clap(long, value_enum, default_value_t = ProgressMode::Auto)]
    pub(crate) progress: ProgressMode,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Html {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) project: Option<std::path::PathBuf>,
    /// Only export this theorem (default: all theorems).
    #[clap(long)]
    pub(crate) theorem: Option<String>,
    /// Solver for the composition-diagram layout (as `domino latex`). Without
    /// one, a simple solver-free layout is drawn.
    #[clap(short, long, default_value = "z3")]
    pub(crate) smtsolver: SolverVariant,
    /// Use the solver-free diagram layout.
    #[clap(long)]
    pub(crate) no_solver: bool,
    /// Open the pages showing the lossy listings (`Some(x)` as `x`, `None` as
    /// `⊥`, ...). Both renderings are always included; the page toggles them.
    #[clap(long)]
    pub(crate) lossy: bool,
    /// Output directory. Defaults to `_build/html/`.
    #[clap(long)]
    pub(crate) out: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Inline {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) project: Option<std::path::PathBuf>,
    /// Name of the theorem the equivalence game hop belongs to.
    #[clap(long)]
    pub(crate) theorem: String,
    /// Index (starting at 0) of the equivalence game hop within the theorem,
    /// as printed by `domino gamehops`.
    #[clap(long)]
    pub(crate) gamehop: usize,
    /// Name of the oracle to inline, as exported by the games in the game hop.
    #[clap(long)]
    pub(crate) oracle: String,
    /// Print without line numbers (useful for diffing two runs).
    #[clap(long)]
    pub(crate) no_line_numbers: bool,
    /// Show the generated EasyCrypt code (as `domino easycrypt export` exports it)
    /// instead of the Domino code, on both sides.
    #[clap(long)]
    pub(crate) easycrypt: bool,
    /// Print the folded listing: a branch whose condition the game's constants decide is
    /// replaced by the body that runs. Exit guards are never folded. Each line keeps its
    /// number in the full listing.
    #[clap(long)]
    pub(crate) fold_trivial_branches: bool,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Debug {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) project: Option<std::path::PathBuf>,
    /// Name of the theorem. Without it, every theorem is debugged.
    #[clap(long)]
    pub(crate) theorem: Option<String>,
    /// One-sided execution of each oracle of this composition (as in `games/C.comp.ssp`; not a
    /// game instance) on the Domino listing, with its parameters free. Needs no theorem. Checks
    /// the game invariants; assumes the package invariants. The start check is
    /// `domino prove --game C --invariant-start`.
    #[clap(long, conflicts_with_all = [
        "theorem",
        "gamehop",
        "claim_set",
        "lockstep",
        "no_check_left",
        "no_check_right",
        "first_failure_per_claim",
    ])]
    pub(crate) game: Option<String>,
    /// One-sided execution of each oracle of this package on the Domino listing, with its
    /// parameters free and each import call an open call. Needs no theorem. The start check is
    /// `domino prove --package P --invariant-start`.
    #[clap(long, conflicts_with_all = [
        "game",
        "theorem",
        "gamehop",
        "claim_set",
        "lockstep",
        "no_check_left",
        "no_check_right",
        "first_failure_per_claim",
    ])]
    pub(crate) package: Option<String>,
    /// Index (starting at 0) of the equivalence game hop, as printed by `domino gamehops`.
    /// Without it, every equivalence game hop is debugged; reductions and conjectures are
    /// skipped with a note. Needs `--theorem`.
    #[clap(long)]
    pub(crate) gamehop: Option<usize>,
    /// Exported oracle name. Without it, every exported oracle is debugged.
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    /// Claim to debug. Without it, the oracle's whole obligation set (what `domino prove`
    /// discharges) is checked on one exploration: an all-claim run. With it, that claim's
    /// dependencies stay in the base frame and prune, as before. With `--game C`: the exact
    /// declared name of one game invariant of `C`; with `--package P`, of one package invariant
    /// of `P`.
    #[clap(long)]
    pub(crate) claim: Option<String>,
    /// Which claims to check. `obligations` (the default): every claim of the game hop, each
    /// under its declared dependencies, as `domino prove` does. `core`: only `equal-aborts`,
    /// `same-output`, `invariant` and the package and game invariants, each under its built-in
    /// dependencies only (`no-abort`, `equal-aborts`, …). Project lemmas are neither checked
    /// nor assumed, as in EasyCrypt.
    #[clap(long, value_enum, default_value_t = ClaimSetArg::Obligations)]
    pub(crate) claim_set: ClaimSetArg,
    /// Advance both oracles together and resolve each decision jointly, as an
    /// EasyCrypt proof would, instead of exploring the left oracle and then the
    /// right one under each of its paths. Domino code either way — for the
    /// EasyCrypt listing use `domino easycrypt debug`.
    #[clap(long)]
    pub(crate) lockstep: bool,
    /// Do NOT prune unreachable LEFT branches early (default: it does). With this
    /// set, every syntactic left path is explored. Sequential strategy only.
    #[clap(long, conflicts_with = "lockstep")]
    pub(crate) no_check_left: bool,
    /// Do NOT prune unreachable RIGHT branches early (default: it does). This only
    /// disables early branch pruning; the terminal-pair vacuity check that
    /// distinguishes `unreachable` from `verified` still runs unconditionally.
    /// Sequential strategy only.
    #[clap(long, conflicts_with = "lockstep")]
    pub(crate) no_check_right: bool,
    /// In an all-claim run, stop checking a claim after its first `GoalFails`, for large
    /// sweeps. Sequential strategy only.
    #[clap(long, conflicts_with = "lockstep")]
    pub(crate) first_failure_per_claim: bool,
    /// Per-query solver timeout in milliseconds (cvc5 `tlimit-per`). A timeout counts
    /// as `unknown` (explored, never pruned, never "verified").
    #[clap(long)]
    pub(crate) timeout: Option<u64>,
    /// Stop after this many explored paths (left paths + right paths per left
    /// path; with `--lockstep`, joint paths). Unlimited by default; `Ctrl-C` is
    /// the interactive stop.
    #[clap(long)]
    pub(crate) max_paths: Option<usize>,
    /// Live progress while exploring, on stderr (stdout carries only the final
    /// concise report): `auto` shows a bar on a terminal and plain log lines when
    /// piped; `plain` and `bar` force one; `none` is silent.
    #[clap(long, value_enum, default_value_t = ProgressMode::Auto)]
    pub(crate) progress: ProgressMode,
    /// Which per-path SMT files to write under `<out>/<strategy>/smt/`. `failures` (the
    /// default) writes a self-contained, directly runnable `.smt2` for each
    /// goal-fails / inconclusive pair; `all` does it for every pair (large — one
    /// copy of the base frame per pair); `deltas` writes only `base.smt2` plus
    /// the small per-path deltas; `none` writes nothing.
    #[clap(long, value_enum, default_value_t = SmtOutArg::Failures)]
    pub(crate) smt: SmtOutArg,
    /// Also write the raw incremental solver transcript to `<strategy>/transcript.smt2`
    /// (large; for debugging `domino debug` itself).
    #[clap(long)]
    pub(crate) transcript: bool,
    /// Root of the debug output. Defaults to `_build/debug`. Each run writes to
    /// `<root>/<theorem>/<left>-<right>/<oracle>/<claim>/` (`!all-claims!` for an all-claim
    /// run; `!core-claims!` and `<claim>!core!` with `--claim-set core`). Indexes are written at the level the run selects.
    #[clap(long)]
    pub(crate) out: Option<std::path::PathBuf>,
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
    pub(crate) project: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Prove {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) project: Option<std::path::PathBuf>,
    #[clap(short, long, default_value = "cvc5")]
    pub(crate) smtsolver: SolverVariant,
    #[clap(short, long)]
    pub(crate) transcript: bool,
    // only check randomness mapping is injective
    #[clap(long)]
    pub(crate) injective_randmap: bool,
    /// Only prove that the invariants hold in the initial state.
    /// Also restricts package invariants to their induction start.
    #[clap(long)]
    pub(crate) invariant_start: bool,
    /// Only this game hop (as printed by `domino gamehops`). Needs `--theorem`.
    #[clap(long)]
    pub(crate) gamehop: Option<usize>,
    /// Only prove this theorem (default: all theorems).
    #[clap(long)]
    pub(crate) theorem: Option<String>,
    /// Only prove the invariant of this package, and nothing else.
    /// Cannot be combined with --theorem or --gamehop.
    #[clap(long, conflicts_with = "injective_randmap")]
    pub(crate) package: Option<String>,
    /// Only prove the game invariants of this composition (as in `games/C.comp.ssp`; not a
    /// game instance), for every value of its parameters. Needs no theorem. It assumes the
    /// package invariants of its instances: prove them with `--package`. Plain `domino prove`
    /// does not run this check.
    #[clap(long, conflicts_with_all = ["package", "injective_randmap"])]
    pub(crate) game: Option<String>,
    /// Only prove the claims of this oracle. Package invariants are then only checked for
    /// packages that have an oracle of this name, and only for that oracle.
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    /// With `--package` or `--game`: a wildcard on the names of the owner's invariants.
    /// Otherwise: a wildcard on the names of the equivalence claims.
    #[clap(long)]
    pub(crate) claim: Option<String>,
    #[clap(long, default_value_t = 1)]
    pub(crate) parallel: usize,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Gamehops {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) project: Option<std::path::PathBuf>,
}

#[cfg(test)]
mod tests {
    use clap::{CommandFactory, Parser};

    use super::EcProve;

    #[derive(Parser)]
    struct Wrap {
        #[clap(flatten)]
        prove: EcProve,
    }

    fn skips_quick_close(flag: &str) -> bool {
        Wrap::try_parse_from(["prove", "--theorem", "T", flag])
            .unwrap()
            .prove
            .no_quick_close
    }

    #[test]
    fn no_quick_close_and_its_hidden_alias_no_rung0_both_skip_the_quick_close() {
        assert!(skips_quick_close("--no-quick-close"));
        assert!(skips_quick_close("--no-rung0"));
    }

    /// Parses `domino <args>` as the binary does.
    fn parse(args: &[&str]) -> Result<crate::Cli, clap::Error> {
        crate::Cli::try_parse_from(std::iter::once("domino").chain(args.iter().copied()))
    }

    fn words(line: &str) -> Vec<&str> {
        line.split_whitespace().collect()
    }

    #[test]
    fn every_command_takes_the_one_vocabulary() {
        for line in [
            "prove --project D --theorem T --gamehop 3",
            "debug --project D --theorem T --gamehop 3 --oracle O",
            "inline --project D --theorem T --gamehop 3 --oracle O",
            "html --theorem T",
            "latex --project D",
            "gamehops --project D",
            "easycrypt prove --theorem T --gamehop 3",
            "easycrypt prove --theorem T --game C",
            "easycrypt prove --theorem T --package P",
            "easycrypt debug --theorem T --game C --timeout 500",
            "easycrypt check-alignment --theorem T --gamehop 3",
        ] {
            if let Err(e) = parse(&words(line)) {
                panic!("{line}: {e}");
            }
        }
    }

    #[test]
    fn the_old_names_are_refused() {
        for line in [
            "prove --path D",
            "prove --proof T",
            "prove --theorem T --proofstep 3",
            "debug --path D",
            "debug --proof T",
            "inline --path D --theorem T --gamehop 0 --oracle O",
            "inline --proof T --gamehop 0 --oracle O",
            "inline --theorem T --proofstep 0 --oracle O",
            "html --proof T",
            "latex --path D",
            "proofsteps",
            "easycrypt prove --theorem T --proofstep 3",
            "easycrypt prove --theorem T --side-inv C",
            "easycrypt prove --theorem T --pkg-inv P",
            "easycrypt debug --theorem T --side-inv C",
            "easycrypt debug --theorem T --pkg-inv P",
            "easycrypt debug --theorem T --game C --debug-timeout 500",
            "easycrypt check-alignment --theorem T --proofstep 3",
        ] {
            assert!(parse(&words(line)).is_err(), "{line} parsed");
        }
    }

    #[test]
    fn the_easycrypt_targets_still_conflict() {
        for line in [
            "easycrypt prove --theorem T --gamehop 3 --game C",
            "easycrypt prove --theorem T --gamehop 3 --package P",
            "easycrypt prove --theorem T --game C --package P",
            "easycrypt debug --theorem T --gamehop 3 --game C",
            "easycrypt debug --theorem T --game C --package P",
        ] {
            let err = parse(&words(line)).expect_err(line);
            assert_eq!(err.kind(), clap::error::ErrorKind::ArgumentConflict, "{line}");
        }
    }

    /// Every `--help` page, of each command and subcommand.
    fn help_pages() -> Vec<String> {
        let mut pages = Vec::new();
        let mut todo = vec![(vec!["domino".to_string()], crate::Cli::command())];
        while let Some((path, mut cmd)) = todo.pop() {
            for sub in cmd.get_subcommands() {
                let mut sub_path = path.clone();
                sub_path.push(sub.get_name().to_string());
                todo.push((sub_path, sub.clone()));
            }
            pages.push(format!("{}\n{}", path.join(" "), cmd.render_long_help()));
        }
        pages
    }

    /// The first old name in `text`: an old flag (a whole word) or the word "proofstep".
    fn old_name(text: &str) -> Option<&'static str> {
        let lower = text.to_lowercase();
        for word in ["proofstep", "proof step"] {
            if lower.contains(word) {
                return Some(word);
            }
        }
        let flags = ["--proof", "--path", "--side-inv", "--pkg-inv", "--debug-timeout"];
        flags.into_iter().find(|flag| {
            text.match_indices(flag).any(|(at, _)| {
                let next = text[at + flag.len()..].chars().next();
                !next.is_some_and(|c| c.is_alphanumeric() || c == '-' || c == '_')
            })
        })
    }

    #[test]
    fn no_help_page_names_an_old_flag() {
        let pages = help_pages();
        assert!(pages.len() > 10, "{} pages", pages.len());
        for page in pages {
            assert_eq!(old_name(&page), None, "{page}");
        }
    }
}
