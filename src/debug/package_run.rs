// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino debug --package P` (symbolic-execution story 33, ADR 0021): one-sided execution of
//! each oracle of package `P` on the **Domino listing**, with no theorem.
//!
//! The listing is the package template with free parameters
//! ([`crate::package_invariant::PackageInvariantContext::open_theorem`]). Each import call has
//! no edge, so the Domino inliner makes it an **open call** ([`crate::debug::ir::InlStmt::OpenCall`]):
//! the line is the call as written, and the bind gets a fresh value of the import's return type.
//! The call can also abort, but an abort ends the oracle, and every claim is under `no-abort`,
//! so an abort is not a path.
//!
//! The claims, the base frame and the fingerprint are those of the package tree of
//! `domino easycrypt debug --package P` ([`execute_pkg`]); only the listing is different.
//!
//! A run writes into [`package_run_dir`] the artifacts of a one-sided run and the result record
//! `one-sided_result.json`, whose owner is the package.

use std::path::Path;
use std::sync::atomic::AtomicBool;
use std::time::Instant;

use crate::debug::driver::DebugError;
use crate::debug::layout::{package_run_dir, Layout};
use crate::debug::lockstep_run::{ListingKind, LockstepDebugOptions, LockstepRun};
use crate::debug::pkg_run::{check_oracle, execute_pkg, pkg_context, PkgRun};
use crate::debug::progress::DebugObserver;
use crate::project::Project;
use crate::util::smtsolver::SmtSolverBackend;

/// The line that `summary.txt` of a package run has at its end.
pub const ABORT_LINE: &str =
    "An open call can also abort; an abort ends the oracle and has nothing to check.";

/// The oracles that `domino debug --package P [--oracle O]` runs: `O`, or every oracle of `P`
/// in declaration order.
///
/// Errors: as [`run_package_command`], except an unknown claim.
pub fn package_oracles<P: Project>(
    project: &P,
    package: &str,
    oracle: Option<&str>,
) -> Result<Vec<String>, DebugError> {
    let ctx = pkg_context(project, package)?;
    match oracle {
        Some(oracle) => {
            check_oracle(&ctx, package, oracle)?;
            Ok(vec![oracle.to_string()])
        }
        None => Ok(ctx.oracle_names()),
    }
}

/// Run one-sided execution of `oracle` of package `package` on the Domino listing, and write
/// its artifacts and result record into [`package_run_dir`] under `root`. With `claim`, the run
/// checks only the package invariant of that exact declared name.
///
/// Errors, all before any solver work: [`DebugError::PackageInvariant`] with `UnknownPackage`
/// (its help lists the packages), `NoInvariant`, `UnknownOracle` or `OpenCallInLoop`; and
/// [`DebugError::NoInvariantMatches`] when no package invariant has the name `claim` (its help
/// lists the package invariants).
#[allow(clippy::too_many_arguments)]
pub fn run_package_command<P, B>(
    project: &P,
    package: &str,
    oracle: &str,
    claim: Option<&str>,
    opts: &LockstepDebugOptions,
    backend: &B,
    root: &Path,
    observer: &mut dyn DebugObserver,
    stop: Option<&AtomicBool>,
) -> Result<LockstepRun, DebugError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let started = Instant::now();
    let ctx = pkg_context(project, package)?;
    check_oracle(&ctx, package, oracle)?;
    let out = package_run_dir(root, package, oracle, claim);
    let run = execute_pkg(
        PkgRun {
            ctx: &ctx,
            theorem: ctx.open_theorem().name.clone(),
            package,
            oracle,
            listing: ListingKind::Domino,
            claim,
        },
        opts,
        backend,
        out.clone(),
        observer,
        stop,
        started,
    )?;
    let summary = out.join(Layout::Plain.summary());
    let mut text = std::fs::read_to_string(&summary)?;
    text.push_str(&format!("\n{ABORT_LINE}\n"));
    std::fs::write(&summary, text)?;
    Ok(run)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;
    use crate::debug::driver::Verdict;
    use crate::debug::index;
    use crate::debug::ir::OPEN_CALL_MARK;
    use crate::debug::lockstep::NodeKind;
    use crate::debug::pkg_run::run_pkg_command;
    use crate::debug::progress::NopObserver;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::process::IncrementalCvc5Backend;

    const NONNEG: &str = "package-invariant!nonneg!Ctr!";

    fn project() -> DirectoryProject<'static> {
        // the files are leaked: the project borrows them for the length of the test binary
        let dir = PathBuf::from("testdata/debug/se29");
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(&dir).unwrap()));
        DirectoryProject::load(dir, files).unwrap()
    }

    fn opts() -> LockstepDebugOptions {
        LockstepDebugOptions::easycrypt(Some(10_000))
    }

    fn package_run(
        package: &str,
        oracle: &str,
        claim: Option<&str>,
        root: &Path,
    ) -> Result<LockstepRun, DebugError> {
        run_package_command(
            &project(),
            package,
            oracle,
            claim,
            &opts(),
            &IncrementalCvc5Backend,
            root,
            &mut NopObserver,
            None,
        )
    }

    fn verdicts(run: &LockstepRun) -> Vec<&'static str> {
        run.outcome
            .pairs
            .iter()
            .map(|p| match p.verdict_of(NONNEG) {
                Some(Verdict::GoalFails { .. }) => "fails",
                Some(Verdict::Verified) => "verified",
                Some(Verdict::Unreachable { .. }) => "unreachable",
                other => panic!("{other:?}"),
            })
            .collect()
    }

    #[test]
    fn the_open_call_does_not_split_and_the_tree_splits_on_the_branch() {
        let root = tempfile::tempdir().unwrap();
        let run = package_run("Ctr", "Bad", None, root.path()).unwrap();
        assert_eq!(run.meta.listing, "domino");
        assert_eq!(run.meta.subject, "package invariants of Ctr");
        assert_eq!(run.outcome.tree.nodes[0].kind, NodeKind::Split);
        // x < 0 breaks `nonneg`, x >= 0 keeps it; there is no abort path
        assert_eq!(verdicts(&run), ["fails", "verified"]);
        assert!(!run.is_ok());
    }

    #[test]
    fn the_listing_shows_the_call_as_written_with_no_guard() {
        let root = tempfile::tempdir().unwrap();
        let run = package_run("Ctr", "Bad", None, root.path()).unwrap();
        let listing = &run.meta.left_listing;
        assert!(
            listing.contains(&format!("y <- invoke Get(x)      // {OPEN_CALL_MARK}")),
            "{listing}"
        );
        assert!(!listing.contains("None"), "{listing}");
        assert!(!listing.contains("<@"), "{listing}");
        let summary = std::fs::read_to_string(
            root.path()
                .join("!package!/Ctr/Bad/!all-claims!")
                .join(Layout::Plain.summary()),
        )
        .unwrap();
        assert!(summary.contains(ABORT_LINE), "{summary}");
    }

    #[test]
    fn an_open_call_before_a_write_has_one_path_that_verifies() {
        let root = tempfile::tempdir().unwrap();
        let step = package_run("Ctr", "Step", None, root.path()).unwrap();
        assert_eq!(verdicts(&step), ["verified"]);
        assert!(step.is_ok());
    }

    #[test]
    fn a_bare_open_call_verifies() {
        let root = tempfile::tempdir().unwrap();
        let ping = package_run("Ctr", "Ping", None, root.path()).unwrap();
        assert!(
            ping.meta
                .left_listing
                .contains(&format!("invoke Put(Ctr.ctr)      // {OPEN_CALL_MARK}")),
            "{}",
            ping.meta.left_listing
        );
        assert_eq!(verdicts(&ping), ["verified"]);
    }

    #[test]
    fn the_failing_claims_agree_with_the_easycrypt_package_tree() {
        for oracle in ["Step", "Bad", "Ping"] {
            let root = tempfile::tempdir().unwrap();
            let domino = package_run("Ctr", oracle, None, root.path()).unwrap();
            let ec_out = tempfile::tempdir().unwrap();
            let ec = run_pkg_command(
                &project(),
                "T",
                "Ctr",
                oracle,
                &opts(),
                &IncrementalCvc5Backend,
                ec_out.path().to_path_buf(),
                &mut NopObserver,
                None,
            )
            .unwrap();
            let fails = |run: &LockstepRun| verdicts(run).contains(&"fails");
            assert_eq!(fails(&domino), fails(&ec), "{oracle}");
            assert_eq!(domino.is_ok(), ec.is_ok(), "{oracle}");
        }
    }

    #[test]
    fn an_open_call_into_a_table_cell_gets_a_fresh_value() {
        let dir = PathBuf::from("testdata/debug/se33-table");
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(&dir).unwrap()));
        let project = DirectoryProject::load(dir, files).unwrap();
        let root = tempfile::tempdir().unwrap();
        let run = run_package_command(
            &project,
            "Tbl",
            "Set",
            None,
            &opts(),
            &IncrementalCvc5Backend,
            root.path(),
            &mut NopObserver,
            None,
        )
        .unwrap();
        // the cell T[k] gets an unknown value: with k = 0 it breaks `zero-empty`
        let verdict = run.outcome.pairs[0].verdict_of("package-invariant!zero-empty!Tbl!");
        assert!(
            matches!(verdict, Some(Verdict::GoalFails { .. })),
            "{verdict:?}"
        );
        assert!(!run.is_ok());
    }

    #[test]
    fn the_run_directory_and_the_project_index() {
        let root = tempfile::tempdir().unwrap();
        let run = package_run("Ctr", "Bad", None, root.path()).unwrap();
        let dir = root.path().join("!package!/Ctr/Bad/!all-claims!");
        for file in ["trace.json", "index.html", "one-sided_result.json"] {
            assert!(dir.join(file).exists(), "{file}");
        }
        assert_eq!(run.meta.out_dir, dir.display().to_string());
        package_run("Ctr", "Bad", Some("nonneg"), root.path()).unwrap();
        assert!(root
            .path()
            .join("!package!/Ctr/Bad/nonneg/trace.json")
            .exists());

        index::refresh_indexes(root.path(), &index::Level::Project).unwrap();
        let project_index = std::fs::read_to_string(root.path().join("summary.txt")).unwrap();
        assert!(project_index.contains("package  Ctr"), "{project_index}");
        assert!(!project_index.contains("$Invariant"), "{project_index}");
        let html = std::fs::read_to_string(root.path().join("index.html")).unwrap();
        assert!(html.contains("!package!/Ctr/index.html"), "{html}");
        let package_index =
            std::fs::read_to_string(root.path().join("!package!/Ctr/summary.txt")).unwrap();
        assert!(package_index.contains("Bad"), "{package_index}");
    }

    #[test]
    fn an_unknown_claim_lists_the_package_invariants() {
        let root = tempfile::tempdir().unwrap();
        let err = package_run("Ctr", "Bad", Some("nope"), root.path()).unwrap_err();
        let DebugError::NoInvariantMatches(e) = err else {
            panic!("{err:?}")
        };
        assert_eq!(e.declared_names, ["nonneg"]);
    }

    #[test]
    fn the_errors_come_before_any_solver_work() {
        let root = tempfile::tempdir().unwrap();
        let unknown = format!("{:?}", package_oracles(&project(), "X", None).unwrap_err());
        assert!(unknown.contains("UnknownPackage"), "{unknown}");
        let none = format!(
            "{:?}",
            package_run("Src", "Get", None, root.path()).unwrap_err()
        );
        assert!(none.contains("NoInvariant"), "{none}");
        let oracle = format!(
            "{:?}",
            package_oracles(&project(), "Ctr", Some("Nope")).unwrap_err()
        );
        assert!(oracle.contains("UnknownOracle"), "{oracle}");
        assert_eq!(
            package_oracles(&project(), "Ctr", None).unwrap(),
            ["Step", "Bad", "Ping"]
        );
    }

    #[test]
    fn an_invoke_of_a_name_that_the_package_does_not_import_is_an_unresolved_edge() {
        use crate::debug::ir::{inline_oracle, InlineError};
        use crate::transforms::theorem_transforms::DebugTransform;
        use crate::transforms::TheoremTransform;

        let project = project();
        let ctx = pkg_context(&project, "Ctr").unwrap();
        let open = ctx.open_theorem();
        let (mut theorem, _) = DebugTransform.transform_theorem(&open).unwrap();
        theorem.instances[0].game.pkgs[0].pkg.imports.clear();
        let err = inline_oracle(&theorem.instances[0], "Bad").unwrap_err();
        assert!(
            matches!(err, InlineError::UnresolvedEdge { ref oracle, .. } if oracle == "Get"),
            "{err:?}"
        );
    }
}
