// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino easycrypt debug --package <P>` (symbolic-execution story 29, ADR 0016, ADR 0017):
//! the **package tree**, one-sided execution of one oracle of a package on the EasyCrypt listing.
//!
//! # The package alone, with open calls
//!
//! The listing is the oracle of the package's one-game theorem with its imports **open**
//! ([`PackageInvariantContext::open_theorem`]): the composition does not wire them, so the
//! EasyCrypt lowering inlines nothing across the import interface. Each import call is an
//! [`crate::debug::ir::InlStmt::OpenCall`], `ec_r<N> <@ O.<import>(…)` in the listing, which binds
//! a fresh value of the call's option type. The call-result guard after it is then a branch like
//! any other: the solver prunes an arm only when it is impossible. So the tree has the shape of
//! the code of the package-invariant lemma, which calls the abstract import module.
//!
//! The package parameters are free theorem constants, as in the package check of story 75. The
//! SMT vocabulary, the base frame and the claims come from the [`PackageInvariantContext`] of
//! that check, whose game has the same names: the base frame is its declarations and each
//! named invariant on the old state; the claims are each named invariant on the new state
//! (`package-invariant!<name>!<P>!`), each under `no-abort`, so a terminal that aborts has
//! nothing to check.
//!
//! # What a run writes
//!
//! `<theorem_out>/!debug!/PkgInv_<P>/<O>/`, as a side tree does (story 25).

use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::time::Instant;

use crate::debug::claims::ClaimQuery;
use crate::debug::driver::{ClaimInfo, DebugError};
use crate::debug::ir::{inline_oracle, InlinedOracle};
use crate::debug::lockstep_fingerprint::Fingerprint;
use crate::debug::lockstep_run::{ListingKind, LockstepDebugOptions, LockstepRun};
use crate::debug::progress::DebugObserver;
use crate::debug::side_run::{execute_one_sided, OneSidedInputs, StateOwner};
use crate::invariant_claim::select_exact;
use crate::package::Package;
use crate::package_invariant::PackageInvariantContext;
use crate::project::Project;
use crate::theorem::Theorem;
use crate::transforms::theorem_transforms::{DebugTransform, EasyCryptTransform};
use crate::transforms::TheoremTransform;
use crate::util::smtsolver::SmtSolverBackend;
use crate::writers::easycrypt::lower::package_oracle_ec;

/// `<theorem_out>/!debug!/PkgInv_<P>/<O>/`.
pub fn pkg_debug_dir(theorem_out: &Path, package: &str, oracle: &str) -> PathBuf {
    theorem_out
        .join("!debug!")
        .join(format!("PkgInv_{package}"))
        .join(oracle)
}

/// The oracles of package `package`, in declaration order.
pub fn pkg_oracles<P: Project>(project: &P, package: &str) -> Result<Vec<String>, DebugError> {
    Ok(package_of(project, package)?
        .oracles
        .iter()
        .map(|o| o.sig.name.clone())
        .collect())
}

fn package_of<'p, P: Project>(project: &'p P, name: &str) -> Result<&'p Package, DebugError> {
    project.get_package(name).ok_or_else(|| {
        DebugError::PackageInvariant(Box::new(
            crate::package_invariant::error::Error::UnknownPackage {
                pkg_name: name.to_string(),
                known_pkg_names: project.packages().map(str::to_string).collect(),
            },
        ))
    })
}

/// The EasyCrypt listing of `oracle` of package `package`, alone, with its import calls open:
/// what the package tree walks.
pub fn pkg_listing<P: Project>(
    project: &P,
    package: &str,
    oracle: &str,
) -> Result<InlinedOracle, DebugError> {
    let ctx = pkg_context(project, package)?;
    listing_of(&ctx.open_theorem(), oracle)
}

fn listing_of(open: &Theorem<'_>, oracle: &str) -> Result<InlinedOracle, DebugError> {
    let (theorem_ec, _) = EasyCryptTransform.transform_theorem(open)?;
    Ok(package_oracle_ec(&theorem_ec.instances[0], oracle)?)
}

/// Run the package tree of `oracle` of package `package`, a package that theorem
/// `theorem_name` uses, and write its artifacts and result record into `out`
/// ([`pkg_debug_dir`]).
///
/// Errors: [`DebugError::PackageNotInTheorem`]; the errors of the package check (no invariant,
/// an open call in a loop that is not unrolled, an unknown oracle).
#[allow(clippy::too_many_arguments)]
pub fn run_pkg_command<P, B>(
    project: &P,
    theorem_name: &str,
    package: &str,
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
    let uses_package = theorem
        .instances
        .iter()
        .any(|inst| inst.game().pkgs.iter().any(|p| p.pkg.name == package));
    if !uses_package {
        return Err(DebugError::PackageNotInTheorem {
            package: package.to_string(),
            theorem: theorem_name.to_string(),
        });
    }
    let ctx = pkg_context(project, package)?;
    check_oracle(&ctx, package, oracle)?;
    execute_pkg(
        PkgRun {
            ctx: &ctx,
            theorem: theorem_name.to_string(),
            package,
            oracle,
            listing: ListingKind::EasyCrypt,
            claim: None,
        },
        opts,
        backend,
        out,
        observer,
        stop,
        started,
    )
}

/// The package context of `package` for a run: [`DebugError::PackageInvariant`] with
/// `UnknownPackage`, `NoInvariant` or `OpenCallInLoop` when there is no run to make.
pub(crate) fn pkg_context<'p, P: Project>(
    project: &'p P,
    package: &str,
) -> Result<PackageInvariantContext<'p>, DebugError> {
    let pkg = package_of(project, package)?;
    Ok(PackageInvariantContext::new(pkg, project).map_err(Box::new)?)
}

/// [`DebugError::PackageInvariant`] with `UnknownOracle` when `package` has no oracle `oracle`.
pub(crate) fn check_oracle(
    ctx: &PackageInvariantContext<'_>,
    package: &str,
    oracle: &str,
) -> Result<(), DebugError> {
    let oracles = ctx.oracle_names();
    if oracles.iter().any(|o| o == oracle) {
        return Ok(());
    }
    Err(DebugError::PackageInvariant(Box::new(
        crate::package_invariant::error::Error::UnknownOracle {
            pkg_name: package.to_string(),
            oracle_name: oracle.to_string(),
            known_oracle_names: oracles,
        },
    )))
}

/// One package tree: what the EasyCrypt package tree (story 29) and `domino debug --package`
/// (story 33) give to [`execute_pkg`].
pub(crate) struct PkgRun<'r> {
    pub ctx: &'r PackageInvariantContext<'r>,
    /// The theorem name in the result record.
    pub theorem: String,
    pub package: &'r str,
    /// An oracle of `package` ([`check_oracle`]).
    pub oracle: &'r str,
    /// The listing that the engine walks. Only the inlined oracle depends on it.
    pub listing: ListingKind,
    /// The declared name of the one package invariant to check; `None` for all.
    pub claim: Option<&'r str>,
}

/// Run one-sided execution of `run.oracle` of the package alone, with its import calls open,
/// on `run.listing`, and write its artifacts and result record into `out`. The base frame and
/// the fingerprint do not depend on the listing or on the claim.
///
/// Errors: [`DebugError::NoInvariantMatches`] when no package invariant has the name
/// `run.claim` (its help lists the package invariants); it comes before any solver work.
#[allow(clippy::too_many_arguments)]
pub(crate) fn execute_pkg<B: SmtSolverBackend>(
    run: PkgRun<'_>,
    opts: &LockstepDebugOptions,
    backend: &B,
    out: PathBuf,
    observer: &mut dyn DebugObserver,
    stop: Option<&AtomicBool>,
    started: Instant,
) -> Result<LockstepRun, DebugError> {
    let PkgRun {
        ctx,
        theorem,
        package,
        oracle,
        listing,
        claim,
    } = run;
    let claims = select_exact(ctx.invariant_claims(), claim, package)?;
    let queries: Vec<ClaimQuery> = ctx
        .tree_claim_queries(oracle)
        .into_iter()
        .filter(|q| claims.iter().any(|c| c.name() == q.name))
        .collect();
    let open = ctx.open_theorem();
    let (theorem_dbg, auxs_dbg) = DebugTransform.transform_theorem(&open)?;
    let inlined = match listing {
        ListingKind::EasyCrypt => listing_of(&open, oracle)?,
        ListingKind::Domino => inline_oracle(&theorem_dbg.instances[0], oracle)?,
    };
    let fingerprint = fingerprint_of(ctx, package, &theorem_dbg, &inlined);

    execute_one_sided(
        OneSidedInputs {
            theorem,
            owner: StateOwner::Package(package.to_string()),
            listing,
            claim: claim.map(str::to_string),
            oracle,
            inlined: &inlined,
            game_inst: &theorem_dbg.instances[0],
            sample_info: &auxs_dbg[0].1.sample_info,
            claims: claims
                .iter()
                .map(|c| ClaimInfo {
                    name: c.name().to_string(),
                    dependencies: c.dependency_names(),
                    admitted: false,
                })
                .collect(),
            queries,
            fingerprint,
            base: ctx.emit_tree_base_frame(oracle),
        },
        opts,
        backend,
        out,
        observer,
        stop,
        started,
    )
}

/// The fingerprint of the package tree of `oracle` of package `package` (ADR 0008), as
/// [`run_pkg_command`] saves it in `trace.json`, without running one-sided execution: a job that
/// resumes an oracle from its saved package tree compares the two (story 76).
pub fn pkg_fingerprint<P: Project>(
    project: &P,
    package: &str,
    oracle: &str,
) -> Result<Fingerprint, DebugError> {
    let ctx = pkg_context(project, package)?;
    let open = ctx.open_theorem();
    let (theorem_dbg, _) = DebugTransform.transform_theorem(&open)?;
    let inlined = listing_of(&open, oracle)?;
    Ok(fingerprint_of(&ctx, package, &theorem_dbg, &inlined))
}

fn fingerprint_of(
    ctx: &PackageInvariantContext<'_>,
    package: &str,
    theorem_dbg: &Theorem<'_>,
    inlined: &InlinedOracle,
) -> Fingerprint {
    let names: Vec<String> = ctx
        .invariant_claims()
        .iter()
        .map(|c| c.name().to_string())
        .collect();
    Fingerprint::of_side(
        &theorem_dbg.instances[0],
        format!(
            "{package} {:?} -> {:?}\n{}",
            inlined.args, inlined.return_type, inlined.listing.text
        ),
        &ctx.emit_invariant(),
        &names,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::debug::driver::{Unreachability, Verdict};
    use crate::debug::index;
    use crate::debug::lockstep::{ChildOutcome, NodeKind};
    use crate::debug::progress::NopObserver;
    use crate::easycrypt::skeleton::{ir_skeleton, Node, NodeKind as SkKind};
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::process::IncrementalCvc5Backend;
    use crate::writers::easycrypt::ast::{EcItem, EcStmt};
    use crate::writers::easycrypt::package::compute_package_variants;
    use crate::writers::smt::contexts::package_invariant_claim_name;

    const NONNEG: &str = "package-invariant!nonneg!Ctr!";

    fn project() -> DirectoryProject<'static> {
        // the files are leaked: the project borrows them for the length of the test binary
        let dir = PathBuf::from("testdata/debug/se29");
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(&dir).unwrap()));
        DirectoryProject::load(dir, files).unwrap()
    }

    fn pkg_run(oracle: &str, out: &Path) -> LockstepRun {
        run_pkg_command(
            &project(),
            "T",
            "Ctr",
            oracle,
            &LockstepDebugOptions::easycrypt(Some(10_000)),
            &IncrementalCvc5Backend,
            out.to_path_buf(),
            &mut NopObserver,
            None,
        )
        .unwrap()
    }

    #[test]
    fn the_call_result_guard_splits_the_none_arm_aborts_and_the_some_arm_verifies() {
        let out = tempfile::tempdir().unwrap();
        let run = pkg_run("Step", out.path());
        assert!(run.meta.one_sided);
        assert_eq!(run.meta.subject, "package invariants of Ctr");
        assert!(run.meta.left_listing.contains("<@ O.d_Get(x);"));
        assert!(!run.meta.left_listing.contains("abort_flag"));

        let root = &run.outcome.tree.nodes[0];
        assert_eq!(root.kind, NodeKind::Split, "the import may return or abort");
        assert_eq!(root.children.len(), 2);
        assert!(root
            .children
            .iter()
            .all(|c| matches!(c.outcome, ChildOutcome::Explored { .. })));

        let [some, none] = &run.outcome.pairs[..] else {
            panic!("{:?}", run.outcome.pairs.len())
        };
        assert!(matches!(some.verdict_of(NONNEG), Some(Verdict::Verified)));
        assert!(
            matches!(
                none.verdict_of(NONNEG),
                Some(Verdict::Unreachable {
                    reason: Unreachability::DependencyFalse { .. }
                })
            ),
            "an abort has nothing to check"
        );
        assert!(run.is_ok());
        for file in ["trace.json", "index.html", "one-sided_result.json"] {
            assert!(out.path().join(file).exists(), "{file}");
        }
    }

    #[test]
    fn a_path_that_breaks_the_invariant_fails_and_the_claim_is_named_by_its_owner() {
        let out = tempfile::tempdir().unwrap();
        let run = pkg_run("Bad", out.path());
        let names: Vec<&str> = run.meta.claims.iter().map(|c| c.name.as_str()).collect();
        assert_eq!(names, [package_invariant_claim_name("nonneg", None, "Ctr")]);
        // Some and x < 0, Some and x >= 0, None
        let verdicts: Vec<&str> = run
            .outcome
            .pairs
            .iter()
            .map(|p| match p.verdict_of(NONNEG) {
                Some(Verdict::GoalFails { .. }) => "fails",
                Some(Verdict::Verified) => "verified",
                Some(Verdict::Unreachable { .. }) => "unreachable",
                other => panic!("{other:?}"),
            })
            .collect();
        assert_eq!(verdicts, ["fails", "verified", "unreachable"]);
        assert!(!run.is_ok());
    }

    /// The shape of a skeleton: decisions and unknown instructions, without the IR's ends.
    fn shape(skeleton: &[Node]) -> String {
        skeleton
            .iter()
            .filter_map(|n| match &n.kind {
                SkKind::Branch { then, els } => Some(format!("if[{}|{}]", shape(then), shape(els))),
                SkKind::Sampling => Some("rnd".to_string()),
                SkKind::Unknown => Some("call".to_string()),
                SkKind::End => None,
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn ec_shape(stmts: &[EcStmt]) -> String {
        stmts
            .iter()
            .filter_map(|s| match s {
                EcStmt::If {
                    then_block,
                    else_block,
                    ..
                } => Some(format!(
                    "if[{}|{}]",
                    ec_shape(&then_block.0),
                    else_block
                        .as_ref()
                        .map_or(String::new(), |b| ec_shape(&b.0))
                )),
                EcStmt::Sample { .. } => Some("rnd".to_string()),
                EcStmt::Call { .. } => Some("call".to_string()),
                EcStmt::Assign { .. } | EcStmt::Comment(_) => None,
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[test]
    fn the_tree_has_the_decision_skeleton_of_the_exported_package_procedure() {
        let project = project();
        let theorem = project.get_theorem("T").unwrap();
        let (theorem_ec, _) = EasyCryptTransform.transform_theorem(theorem).unwrap();
        let variants = compute_package_variants(&theorem_ec).unwrap();
        let module = variants
            .iter()
            .filter(|v| v.name.starts_with("Ctr"))
            .flat_map(|v| &v.file.items)
            .find_map(|item| match item {
                EcItem::Module(m) => Some(m),
                _ => None,
            })
            .expect("Pkg_Ctr has its module");
        for oracle in ["Step", "Bad", "Ping"] {
            let proc = module
                .procs
                .iter()
                .find(|p| p.name == format!("d_{oracle}"))
                .unwrap();
            let listing = pkg_listing(&project, "Ctr", oracle).unwrap();
            let tree = shape(&ir_skeleton(&listing));
            assert_eq!(tree, ec_shape(&proc.body.0), "{oracle}");
            assert!(tree.starts_with("call if["), "{oracle}: {tree}");
        }
    }

    #[test]
    fn the_theorem_index_lists_the_package_trees_and_links_their_index() {
        let root = tempfile::tempdir().unwrap();
        let theorem_out = root.path().join("T");
        pkg_run("Step", &pkg_debug_dir(&theorem_out, "Ctr", "Step"));
        index::refresh_indexes(
            root.path(),
            &index::Level::Theorem {
                theorem: "T".into(),
            },
        )
        .unwrap();
        let theorem_index = std::fs::read_to_string(theorem_out.join("summary.txt")).unwrap();
        assert!(
            theorem_index.contains("pkg-inv  Ctr  1  0"),
            "{theorem_index}"
        );
        assert!(
            theorem_index.contains("!debug!/PkgInv_Ctr/index.html"),
            "{theorem_index}"
        );
        let pkg_index =
            std::fs::read_to_string(theorem_out.join("!debug!/PkgInv_Ctr/summary.txt")).unwrap();
        assert!(
            pkg_index.contains("package invariants of Ctr"),
            "{pkg_index}"
        );
        assert!(pkg_index.contains("Step/index.html"), "{pkg_index}");
    }

    #[test]
    fn a_package_the_theorem_does_not_use_is_an_error() {
        let out = tempfile::tempdir().unwrap();
        let err = run_pkg_command(
            &project(),
            "T",
            "Nope",
            "Step",
            &LockstepDebugOptions::easycrypt(None),
            &IncrementalCvc5Backend,
            out.path().to_path_buf(),
            &mut NopObserver,
            None,
        )
        .unwrap_err();
        assert!(
            matches!(err, DebugError::PackageNotInTheorem { .. }),
            "{err}"
        );
    }

    #[test]
    fn the_package_debug_dir_is_under_pkg_inv() {
        assert_eq!(
            pkg_debug_dir(Path::new("o/T"), "Ctr", "Step"),
            Path::new("o/T/!debug!/PkgInv_Ctr/Step")
        );
    }
}
