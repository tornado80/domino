// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino easycrypt debug --side-inv <C>` (symbolic-execution story 25, ADR 0014): one-sided
//! execution of each oracle of a composition, on the EasyCrypt listing.
//!
//! # The composition with free parameters
//!
//! No game instance fixes the parameters of `C`. [`free_theorem`] adds to the theorem a game
//! instance named `C` whose every parameter is a theorem constant that nothing constrains: the
//! theorem's own constant of that name and type when there is one, otherwise a new constant
//! `<C>_<param>`. So the package and game invariant claims are named for the composition
//! (`package-invariant!<name>!<C>-<PkgInst>!`, `game-invariant!<name>!<C>!`) by their one owners
//! ([`package_invariant_claim_name`], [`game_invariant_claim_name`]), and the definitions of the
//! invariants get the same names.
//!
//! The SMT vocabulary comes from an [`EquivalenceContext`] of `C` against a copy of it,
//! `C$side`. Only the left side (`C`) is executed and asserted about: the copy is in the base
//! frame as declarations and definitions only, and no claim or assumption reads it.
//!
//! # What a run writes
//!
//! `<theorem_out>/!debug!/SideInv_<C>/<O>/`: `trace.json` (the side tree, in the shape of a joint
//! tree, with its fingerprint), `summary.txt`, `index.html` (the joint-tree viewer with one
//! column), `models/`, and the result record `one-sided_result.json` for the debug index.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::time::Instant;

use crate::debug::claims::ClaimQuery;
use crate::debug::driver::{sites_view, ClaimInfo, DebugError, StopReason};
use crate::debug::fold::FoldedListing;
use crate::debug::index;
use crate::debug::ir::{count_terminals, InlinedOracle};
use crate::debug::layout::Layout;
use crate::debug::lockstep::{LockstepOutcome, LockstepSide};
use crate::debug::lockstep_fingerprint::Fingerprint;
use crate::debug::lockstep_report;
use crate::debug::lockstep_run::{
    summarize, GoalsView, LockstepDebugOptions, LockstepMeta, LockstepOptionsView, LockstepRun,
    LOCKSTEP_TRACE_SCHEMA,
};
use crate::debug::progress::{DebugEvent, DebugObserver};
use crate::debug::side::{run_side, SideOptions};
use crate::debug::sweep::{SweepEntry, Target};
use crate::gamehops::equivalence::Equivalence;
use crate::identifier::game_ident::{GameConstIdentifier, GameIdentifier};
use crate::identifier::theorem_ident::{TheoremConstIdentifier, TheoremIdentifier};
use crate::identifier::Identifier;
use crate::package::Composition;
use crate::project::Project;
use crate::theorem::{
    BuiltInFact, ClaimKind, GameInstance, InvariantSide, RandomnessType, ResolvedClaim,
    ResolvedDependency, Theorem,
};
use crate::transforms::samplify::SampleInfo;
use crate::transforms::theorem_transforms::{
    DebugTransform, EasyCryptTransform, EquivalenceTransform,
};
use crate::transforms::TheoremTransform;
use crate::types::{CountSpec, Type, TypeKind};
use crate::util::smtsolver::{SmtSolver, SmtSolverBackend};
use crate::writers::easycrypt::lower::inline_oracle_ec;
use crate::writers::smt::contexts::EquivalenceContext;
#[allow(unused_imports)] // named in the module documentation
use crate::writers::smt::contexts::{game_invariant_claim_name, package_invariant_claim_name};
use crate::writers::smt::exprs::SmtExpr;

/// The strategy name of one-sided execution: [`LockstepMeta::mode`] and the result record's.
pub const ONE_SIDED: &str = "one-sided";

/// The dependency of every side-invariant claim: the side invariant holds under `!abort`.
const NO_ABORT: BuiltInFact = BuiltInFact::LeftNoAbort;

/// `<theorem_out>/!debug!/SideInv_<C>/<O>/`.
pub fn side_debug_dir(theorem_out: &Path, composition: &str, oracle: &str) -> PathBuf {
    theorem_out
        .join("!debug!")
        .join(format!("SideInv_{composition}"))
        .join(oracle)
}

/// The exported oracles of composition `composition`, in declaration order.
pub fn side_oracles<P: Project>(project: &P, composition: &str) -> Result<Vec<String>, DebugError> {
    let comp = composition_of(project, composition)?;
    Ok(comp.exports.iter().map(|e| e.name().to_string()).collect())
}

fn composition_of<'p, P: Project>(
    project: &'p P,
    name: &str,
) -> Result<&'p Composition, DebugError> {
    project
        .get_game(name)
        .ok_or_else(|| DebugError::CompositionNotFound {
            name: name.to_string(),
        })
}

/// The name of the copy of `C` that completes the [`EquivalenceContext`].
fn copy_name(composition: &str) -> String {
    format!("{composition}$side")
}

/// `theorem` with two more game instances of `comp`, `C` and `C$side`, whose parameters are
/// free theorem constants, and the equivalence of the two that gives the SMT vocabulary.
pub(crate) fn free_theorem<'a>(
    theorem: &Theorem<'a>,
    comp: &Composition,
) -> Result<(Theorem<'a>, Equivalence), DebugError> {
    let name = comp.name.clone();
    let copy = copy_name(&name);
    for taken in [&name, &copy] {
        if theorem.find_game_instance(taken).is_some() {
            return Err(DebugError::SideInstanceNameTaken {
                name: taken.clone(),
                theorem: theorem.name.clone(),
            });
        }
    }
    let mut theorem = theorem.clone();
    let params = free_params(&mut theorem, comp);
    for inst_name in [&name, &copy] {
        let inst = GameInstance::new(
            inst_name.clone(),
            theorem.name.clone(),
            comp.clone(),
            Vec::new(),
            params
                .iter()
                .map(|(id, value)| {
                    let id = GameConstIdentifier {
                        game_inst_name: Some(inst_name.clone()),
                        ..id.clone()
                    };
                    (id, value.clone())
                })
                .collect(),
        );
        theorem.instances.push(inst);
    }
    let randomness = comp
        .exports
        .iter()
        .map(|e| (e.name().to_string(), RandomnessType::None))
        .collect();
    let eq = Equivalence::new(
        theorem.name.clone(),
        name,
        copy,
        Vec::new(),
        Vec::new(),
        randomness,
    );
    Ok((theorem, eq))
}

/// One free theorem constant for each parameter of `comp`, added to `theorem` where it has none
/// of that name and type. Integer parameters come first, so `Bits(<param>)` in the type of
/// another parameter is rewritten to `Bits(<constant>)`, as the theorem parser does.
fn free_params(
    theorem: &mut Theorem<'_>,
    comp: &Composition,
) -> Vec<(GameConstIdentifier, crate::expressions::Expression)> {
    let (ints, others): (Vec<_>, Vec<_>) = comp
        .consts
        .iter()
        .partition(|(_, ty)| matches!(ty.kind(), TypeKind::Integer));
    let mut rules = Vec::new();
    let mut params = Vec::new();
    for (param, ty) in ints.into_iter().chain(others) {
        let ty = ty.rewrite_type(&rules);
        let const_name = match theorem.consts.iter().find(|(n, _)| n == param) {
            Some((_, existing)) if *existing == ty => param.clone(),
            Some(_) => format!("{}_{param}", comp.name),
            None => param.clone(),
        };
        if !theorem.consts.iter().any(|(n, _)| *n == const_name) {
            theorem.consts.push((const_name.clone(), ty.clone()));
        }
        let ident =
            Identifier::TheoremIdentifier(TheoremIdentifier::Const(TheoremConstIdentifier {
                theorem_name: theorem.name.clone(),
                name: const_name,
                ty: ty.clone(),
                inst_info: None,
            }));
        if matches!(ty.kind(), TypeKind::Integer) {
            rules.push((
                Type::bits(CountSpec::Identifier(Box::new(Identifier::GameIdentifier(
                    GameIdentifier::Const(GameConstIdentifier {
                        game_name: comp.name.clone(),
                        name: param.clone(),
                        ty: Type::integer(),
                        game_inst_name: None,
                        theorem_name: None,
                        inst_info: None,
                        assigned_value: None,
                    }),
                )))),
                Type::bits(CountSpec::Identifier(Box::new(ident.clone()))),
            ));
        }
        let value: crate::expressions::Expression = ident.into();
        params.push((
            GameConstIdentifier {
                game_name: comp.name.clone(),
                name: param.clone(),
                ty,
                assigned_value: Some(Box::new(value.clone())),
                inst_info: None,
                game_inst_name: None,
                theorem_name: Some(theorem.name.clone()),
            },
            value,
        ));
    }
    params
}

/// The fingerprint of the side tree of `oracle` of composition `composition` (ADR 0008), as
/// [`run_side_command`] saves it in `trace.json`, without running one-sided execution: a job
/// that resumes an oracle from its saved side tree compares the two (story 69).
pub fn side_fingerprint<P: Project>(
    project: &P,
    theorem_name: &str,
    composition: &str,
    oracle: &str,
) -> Result<Fingerprint, DebugError> {
    let theorem = project
        .get_theorem(theorem_name)
        .ok_or_else(|| DebugError::TheoremNotFound {
            name: theorem_name.to_string(),
        })?;
    let comp = composition_of(project, composition)?;
    let (theorem, eq) = free_theorem(theorem, comp)?;
    let (theorem_eq, auxs_eq) = EquivalenceTransform.transform_theorem(&theorem)?;
    let mut eqctx = EquivalenceContext::new(&eq, &theorem_eq, &auxs_eq);
    eqctx.load_invariants(project)?;
    let (theorem_ec, _) = EasyCryptTransform.transform_theorem(&theorem)?;
    let inlined = inline_oracle_ec(
        theorem_ec
            .find_game_instance(composition)
            .expect("the free instance exists"),
        oracle,
    )?;
    Ok(fingerprint_of(&theorem, &eqctx, composition, &inlined))
}

/// The fingerprint of a side tree: the listing of the free instance of `composition`, its
/// constants, the invariants and the names of the claims.
fn fingerprint_of(
    theorem: &Theorem<'_>,
    eqctx: &EquivalenceContext<'_>,
    composition: &str,
    inlined: &crate::debug::ir::InlinedOracle,
) -> Fingerprint {
    let names: Vec<String> = side_claims(eqctx)
        .iter()
        .map(|c| c.name().to_string())
        .collect();
    Fingerprint::of_side(
        theorem
            .find_game_instance(composition)
            .expect("the free instance exists"),
        format!(
            "{composition} {:?} -> {:?}\n{}",
            inlined.args, inlined.return_type, inlined.listing.text
        ),
        &eqctx.emit_invariant(),
        &names,
    )
}

/// The claims of a side tree: each package invariant of `C`, then its game invariant, on the
/// new state, each under `left-no-abort`.
fn side_claims(eqctx: &EquivalenceContext<'_>) -> Vec<ResolvedClaim> {
    eqctx
        .generate_game_or_package_invariant_claims()
        .into_iter()
        .filter(|c| c.kind().invariant_side() == Some(InvariantSide::Left))
        .map(|c| ResolvedClaim {
            dependencies: vec![ResolvedDependency {
                name: NO_ABORT.name().to_string(),
                kind: ClaimKind::BuiltIn(NO_ABORT),
            }],
            ..c
        })
        .collect()
}

/// The base frame of a side tree: the declarations and definitions `prove` uses (both sides',
/// the copy's never read), and then each invariant of `C` on the old state.
fn side_base_frame(eqctx: &EquivalenceContext<'_>, oracle: &str) -> Vec<SmtExpr> {
    let mut base = vec![SmtExpr::Comment(
        " domino easycrypt debug --side-inv — base frame ".to_string(),
    )];
    base.extend(eqctx.emit_base_declarations());
    base.extend(eqctx.emit_theorem_paramfuncs());
    base.extend(eqctx.emit_game_definitions());
    base.extend(eqctx.emit_constant_declarations(Some(oracle)));
    base.extend(eqctx.emit_auto_randomness(oracle));
    base.extend(eqctx.emit_invariant());
    base.extend(eqctx.emit_return_value_helpers(oracle));
    base.push(SmtExpr::Comment(
        " the side invariants on the old state ".to_string(),
    ));
    base.extend(eqctx.emit_left_side_invariants_old(oracle));
    base
}

/// Run one-sided execution of `oracle` of composition `composition` (of theorem
/// `theorem_name`) on the EasyCrypt listing, and write its artifacts and result record into
/// `out` ([`side_debug_dir`]).
#[allow(clippy::too_many_arguments)]
pub fn run_side_command<P, B>(
    project: &P,
    theorem_name: &str,
    composition: &str,
    oracle: &str,
    opts: &LockstepDebugOptions,
    backend: &B,
    out: PathBuf,
    observer: &mut dyn DebugObserver,
    stop: Option<&AtomicBool>,
) -> Result<LockstepRun, DebugError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let started = Instant::now();
    let theorem = project
        .get_theorem(theorem_name)
        .ok_or_else(|| DebugError::TheoremNotFound {
            name: theorem_name.to_string(),
        })?;
    let comp = composition_of(project, composition)?;
    if !comp.exports.iter().any(|e| e.name() == oracle) {
        return Err(DebugError::OracleNotExported {
            oracle: oracle.to_string(),
            game_inst: composition.to_string(),
        });
    }
    let (theorem, eq) = free_theorem(theorem, comp)?;

    let (theorem_eq, auxs_eq) = EquivalenceTransform.transform_theorem(&theorem)?;
    let mut eqctx = EquivalenceContext::new(&eq, &theorem_eq, &auxs_eq);
    eqctx.load_invariants(project)?;

    let (theorem_dbg, auxs_dbg) = DebugTransform.transform_theorem(&theorem)?;
    let inst = theorem_dbg
        .find_game_instance(composition)
        .expect("the free instance exists");
    let sample_info = &auxs_dbg
        .iter()
        .find(|(n, _)| n == composition)
        .expect("aux for the free instance")
        .1
        .sample_info;
    let (theorem_ec, _) = EasyCryptTransform.transform_theorem(&theorem)?;
    let inlined = inline_oracle_ec(
        theorem_ec
            .find_game_instance(composition)
            .expect("the free instance exists"),
        oracle,
    )?;

    let claims = side_claims(&eqctx);
    let queries: Vec<ClaimQuery> = claims
        .iter()
        .map(|c| ClaimQuery::of(&eqctx, c, oracle))
        .collect();
    execute_one_sided(
        OneSidedInputs {
            theorem: theorem.name.clone(),
            owner: StateOwner::Composition(composition.to_string()),
            oracle,
            inlined: &inlined,
            game_inst: inst,
            sample_info,
            claims: claims
                .iter()
                .map(|c| ClaimInfo {
                    name: c.name().to_string(),
                    dependencies: c.dependency_names(),
                    admitted: false,
                })
                .collect(),
            queries,
            fingerprint: fingerprint_of(&theorem, &eqctx, composition, &inlined),
            base: side_base_frame(&eqctx, oracle),
        },
        opts,
        backend,
        out,
        observer,
        stop,
        started,
    )
}

/// The owner of the state that a one-sided run walks and checks: a composition (its side
/// tree, story 25) or a package (its package tree, story 29).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateOwner {
    Composition(String),
    Package(String),
}

impl StateOwner {
    pub fn name(&self) -> &str {
        match self {
            StateOwner::Composition(name) | StateOwner::Package(name) => name,
        }
    }

    /// What the tree checks, as the page header says it.
    fn subject(&self) -> String {
        match self {
            StateOwner::Composition(c) => format!("side invariants of {c}"),
            StateOwner::Package(p) => format!("package invariants of {p}"),
        }
    }
}

/// What the owner of the state prepares for one one-sided run of `oracle`.
pub(crate) struct OneSidedInputs<'r> {
    pub theorem: String,
    pub owner: StateOwner,
    pub oracle: &'r str,
    /// The EasyCrypt listing of the oracle.
    pub inlined: &'r InlinedOracle,
    /// The instance the executor names the state and the constants by ([`DebugTransform`]).
    pub game_inst: &'r GameInstance,
    pub sample_info: &'r SampleInfo,
    pub claims: Vec<ClaimInfo>,
    /// One for each of `claims`, in the same order.
    pub queries: Vec<ClaimQuery>,
    pub fingerprint: Fingerprint,
    /// Asserted once at solver level 0.
    pub base: Vec<SmtExpr>,
}

/// Run one-sided execution with `inputs`, and write its artifacts and its result record into
/// `out`.
pub(crate) fn execute_one_sided<B: SmtSolverBackend>(
    inputs: OneSidedInputs<'_>,
    opts: &LockstepDebugOptions,
    backend: &B,
    out: PathBuf,
    observer: &mut dyn DebugObserver,
    stop: Option<&AtomicBool>,
    started: Instant,
) -> Result<LockstepRun, DebugError> {
    let layout = Layout::Plain;
    let OneSidedInputs {
        theorem,
        owner,
        oracle,
        inlined,
        game_inst,
        sample_info,
        claims,
        queries,
        fingerprint,
        base,
    } = inputs;
    observer.on_event(&DebugEvent::Started {
        oracle,
        claim: "!all-claims!",
        admitted: false,
    });
    std::fs::create_dir_all(layout.path(&out, "models"))?;
    let meta = LockstepMeta {
        schema: LOCKSTEP_TRACE_SCHEMA,
        mode: ONE_SIDED,
        listing: "easycrypt",
        theorem,
        proofstep: 0,
        left_game: owner.name().to_string(),
        right_game: String::new(),
        oracle: oracle.to_string(),
        claim: "!all-claims!".to_string(),
        core: false,
        all_claims: true,
        claims,
        out_dir: out.display().to_string(),
        layout,
        smt_dir: layout.rel("smt"),
        options: LockstepOptionsView::from(opts),
        base_frame_smt: base
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n"),
        goals: GoalsView {
            claims: queries.iter().map(ClaimQuery::view).collect(),
        },
        left_listing: inlined.listing.text.clone(),
        right_listing: String::new(),
        left_folded: FoldedListing::of(inlined),
        right_folded: FoldedListing::default(),
        left_sites: sites_view(&inlined.listing),
        right_sites: BTreeMap::new(),
        left_lines: inlined.listing.lines.clone(),
        right_lines: Vec::new(),
        left_frames: inlined.listing.frames.clone(),
        right_frames: Vec::new(),
        left_syntactic: count_terminals(inlined),
        right_syntactic: 0,
        one_sided: true,
        subject: owner.subject(),
        fingerprint: std::iter::once(("all".to_string(), fingerprint.hex.clone()))
            .chain(fingerprint.parts.clone())
            .collect(),
    };

    let mut solver = if opts.transcript {
        let transcript = std::fs::File::create(layout.path(&out, "transcript.smt2"))?;
        backend.new_smtsolver_with_transcript(transcript)?
    } else {
        backend.new_smtsolver()?
    };
    if let Some(ms) = opts.timeout_ms {
        solver.set_option("tlimit-per", &ms.to_string())?;
    }
    for entry in &base {
        solver.write_smt(entry.clone())?;
    }
    let empty = LockstepOutcome {
        tree: Default::default(),
        pairs: Vec::new(),
        stuck: Vec::new(),
        stop_reason: StopReason::Completed,
    };
    lockstep_report::flush(&meta, &empty, &summarize(&empty, &meta.claims), &out, true)?;

    let outcome = run_side(
        &mut solver,
        LockstepSide {
            inlined,
            game_inst,
            sample_info,
        },
        &queries,
        &SideOptions {
            max_paths: opts.max_paths,
            stop,
            out_dir: &out,
            layout,
        },
    );
    solver.close();
    let outcome = outcome?;
    let summary = summarize(&outcome, &meta.claims);
    lockstep_report::flush(&meta, &outcome, &summary, &out, false)?;
    observer.on_event(&DebugEvent::LockstepFinished {
        pairs: outcome.pairs.len(),
        stuck: 0,
        stop_reason: outcome.stop_reason,
    });

    let run = LockstepRun {
        meta,
        outcome,
        summary,
        elapsed: started.elapsed(),
    };
    index::write_result(&one_sided_entry(&run, &owner))?;
    Ok(run)
}

/// The oracles of `owner` that one-sided execution walks: the exports of a composition, the
/// oracles of a package.
pub fn one_sided_oracles<P: Project>(
    project: &P,
    owner: &StateOwner,
) -> Result<Vec<String>, DebugError> {
    match owner {
        StateOwner::Composition(c) => side_oracles(project, c),
        StateOwner::Package(p) => crate::debug::pkg_run::pkg_oracles(project, p),
    }
}

/// The directory of the run of `oracle` of `owner`: [`side_debug_dir`] or
/// [`crate::debug::pkg_run::pkg_debug_dir`].
pub fn one_sided_debug_dir(theorem_out: &Path, owner: &StateOwner, oracle: &str) -> PathBuf {
    match owner {
        StateOwner::Composition(c) => side_debug_dir(theorem_out, c, oracle),
        StateOwner::Package(p) => crate::debug::pkg_run::pkg_debug_dir(theorem_out, p, oracle),
    }
}

/// One-sided execution of `oracle` of `owner`: a side tree ([`run_side_command`]) or a package
/// tree ([`crate::debug::pkg_run::run_pkg_command`]).
#[allow(clippy::too_many_arguments)]
pub fn run_one_sided_command<P, B>(
    project: &P,
    theorem_name: &str,
    owner: &StateOwner,
    oracle: &str,
    opts: &LockstepDebugOptions,
    backend: &B,
    out: PathBuf,
    observer: &mut dyn DebugObserver,
    stop: Option<&AtomicBool>,
) -> Result<LockstepRun, DebugError>
where
    P: Project,
    B: SmtSolverBackend,
{
    match owner {
        StateOwner::Composition(c) => run_side_command(
            project,
            theorem_name,
            c,
            oracle,
            opts,
            backend,
            out,
            observer,
            stop,
        ),
        StateOwner::Package(p) => crate::debug::pkg_run::run_pkg_command(
            project,
            theorem_name,
            p,
            oracle,
            opts,
            backend,
            out,
            observer,
            stop,
        ),
    }
}

/// The sweep entry of a one-sided run: the target names the owner as its left side, with no
/// right side, and the entry is marked with the owner.
pub fn one_sided_entry(run: &LockstepRun, owner: &StateOwner) -> SweepEntry {
    let target = Target {
        theorem: run.meta.theorem.clone(),
        proofstep: 0,
        left: run.meta.left_game.clone(),
        right: String::new(),
        oracle: run.meta.oracle.clone(),
    };
    let (composition, package) = match owner {
        StateOwner::Composition(c) => (Some(c.clone()), None),
        StateOwner::Package(p) => (None, Some(p.clone())),
    };
    SweepEntry {
        composition,
        package,
        unit: "terminals",
        ..SweepEntry::from_lockstep(target, run)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::debug::driver::Verdict;
    use crate::debug::lockstep::NodeKind;
    use crate::debug::progress::NopObserver;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::process::IncrementalCvc5Backend;

    fn project() -> DirectoryProject<'static> {
        project_in("testdata/debug/se25")
    }

    fn project_in(dir: &str) -> DirectoryProject<'static> {
        // the files are leaked: the project borrows them for the length of the test binary
        let dir = PathBuf::from(dir);
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(&dir).unwrap()));
        DirectoryProject::load(dir, files).unwrap()
    }

    fn side_run(out: &Path) -> LockstepRun {
        side_run_of(&project(), out)
    }

    fn side_run_of(project: &DirectoryProject<'_>, out: &Path) -> LockstepRun {
        run_side_command(
            project,
            "T",
            "S",
            "O",
            &LockstepDebugOptions::easycrypt(Some(10_000)),
            &IncrementalCvc5Backend,
            out.to_path_buf(),
            &mut NopObserver,
            None,
        )
        .unwrap()
    }

    const PKG: &str = "package-invariant!main!S-p!";
    const GAME: &str = "game-invariant!main!S!";

    #[test]
    fn claim_names_are_of_the_composition_from_the_one_owners() {
        assert_eq!(package_invariant_claim_name("main", Some("S"), "p"), PKG);
        assert_eq!(game_invariant_claim_name("main", "S"), GAME);
        // lockstep execution's names do not change: they are of the game instance
        assert_eq!(
            package_invariant_claim_name("main", Some("s"), "p"),
            "package-invariant!main!s-p!"
        );
        assert_eq!(
            game_invariant_claim_name("main", "s"),
            "game-invariant!main!s!"
        );
    }

    #[test]
    fn a_side_run_checks_the_composition_claims_and_fails_only_the_breaking_path() {
        let out = tempfile::tempdir().unwrap();
        let run = side_run(out.path());
        let names: Vec<&str> = run.meta.claims.iter().map(|c| c.name.as_str()).collect();
        assert_eq!(names, [PKG, GAME]);
        assert!(run.meta.one_sided);
        assert!(run.meta.fingerprint.contains_key("all"));

        // n > 0 is free: both arms; then x < 0 on each: four terminals
        assert_eq!(run.outcome.pairs.len(), 4);
        let root = &run.outcome.tree.nodes[0];
        assert_eq!(
            root.kind,
            NodeKind::Split,
            "the branch on the parameter splits"
        );
        assert_eq!(root.children.len(), 2);

        // the terminal under `x < 0` (then) breaks `k >= 0`; the others hold
        let failing: Vec<bool> = run
            .outcome
            .pairs
            .iter()
            .map(|p| matches!(p.verdict_of(PKG), Some(Verdict::GoalFails { .. })))
            .collect();
        assert_eq!(failing, [true, false, true, false]);
        for p in &run.outcome.pairs {
            if !matches!(p.verdict_of(PKG), Some(Verdict::GoalFails { .. })) {
                assert!(
                    matches!(p.verdict_of(PKG), Some(Verdict::Verified)),
                    "{}",
                    p.id
                );
            }
            assert!(
                matches!(p.verdict_of(GAME), Some(Verdict::Verified)),
                "{}",
                p.id
            );
        }
        assert!(!run.summary.claims.is_empty());

        for file in [
            "trace.json",
            "summary.txt",
            "index.html",
            "one-sided_result.json",
        ] {
            assert!(out.path().join(file).exists(), "{file}");
        }
        let trace = std::fs::read_to_string(out.path().join("trace.json")).unwrap();
        assert!(trace.contains("\"one_sided\": true"));
        assert!(trace.contains("\"absent\""));
    }

    /// Story 73: each named package invariant is a check of its own, named by the invariant;
    /// a path that breaks only `nonneg` fails only that check.
    #[test]
    fn a_path_that_breaks_one_named_invariant_fails_only_its_check() {
        const MAIN: &str = "package-invariant!main!S-p!";
        const NONNEG: &str = "package-invariant!nonneg!S-p!";
        let out = tempfile::tempdir().unwrap();
        let run = side_run_of(&project_in("testdata/debug/ec73"), out.path());
        let names: Vec<&str> = run.meta.claims.iter().map(|c| c.name.as_str()).collect();
        assert_eq!(names, [MAIN, NONNEG, GAME]);
        let failing: Vec<bool> = run
            .outcome
            .pairs
            .iter()
            .map(|p| matches!(p.verdict_of(NONNEG), Some(Verdict::GoalFails { .. })))
            .collect();
        assert_eq!(failing, [true, false, true, false]);
        for p in &run.outcome.pairs {
            assert!(
                matches!(p.verdict_of(MAIN), Some(Verdict::Verified)),
                "{}",
                p.id
            );
        }
        let summary = std::fs::read_to_string(out.path().join("summary.txt")).unwrap();
        assert!(
            summary.contains(NONNEG) && summary.contains(MAIN),
            "{summary}"
        );
    }

    #[test]
    fn the_theorem_index_lists_the_side_runs_and_links_their_index() {
        let root = tempfile::tempdir().unwrap();
        let theorem_out = root.path().join("T");
        let run = side_run(&side_debug_dir(&theorem_out, "S", "O"));
        assert!(!run.is_ok(), "a path breaks the package invariant");
        index::refresh_indexes(
            root.path(),
            &index::Level::Theorem {
                theorem: "T".into(),
            },
        )
        .unwrap();
        let theorem_index = std::fs::read_to_string(theorem_out.join("summary.txt")).unwrap();
        assert!(
            theorem_index.contains("side-inv  S  1  1"),
            "{theorem_index}"
        );
        assert!(
            theorem_index.contains("!debug!/SideInv_S/index.html"),
            "{theorem_index}"
        );
        let side_index =
            std::fs::read_to_string(theorem_out.join("!debug!/SideInv_S/summary.txt")).unwrap();
        assert!(side_index.contains("side invariants of S"), "{side_index}");
        assert!(side_index.contains("O/index.html"), "{side_index}");
    }

    #[test]
    fn the_side_debug_dir_is_under_side_inv() {
        assert_eq!(
            side_debug_dir(Path::new("o/T"), "H6", "Send1"),
            Path::new("o/T/!debug!/SideInv_H6/Send1")
        );
    }
}

#[cfg(test)]
mod full_4whs {
    use super::*;
    use crate::debug::progress::NopObserver;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::process::IncrementalCvc5Backend;

    /// Acceptance: a side tree for each oracle of `H6` on Full4WHS. Slow: run with `--ignored`.
    #[test]
    #[ignore]
    fn h6_on_full_4whs_writes_a_side_tree_for_each_oracle() {
        let dir = PathBuf::from("example-projects/4WHS");
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let out = tempfile::tempdir().unwrap();
        let theorem_out = out.path().join("Full4WHS");
        for oracle in side_oracles(&project, "H6").unwrap() {
            let dir = side_debug_dir(&theorem_out, "H6", &oracle);
            let run = run_side_command(
                &project,
                "Full4WHS",
                "H6",
                &oracle,
                &LockstepDebugOptions::easycrypt(Some(10_000)),
                &IncrementalCvc5Backend,
                dir.clone(),
                &mut NopObserver,
                None,
            )
            .unwrap();
            eprintln!(
                "{oracle}: {} terminals, ok {}",
                run.outcome.pairs.len(),
                run.is_ok()
            );
            for file in ["trace.json", "index.html"] {
                assert!(dir.join(file).exists(), "{oracle} {file}");
            }
        }
    }
}
