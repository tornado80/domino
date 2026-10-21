// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino debug --game C` (symbolic-execution story 32, ADR 0021): one-sided execution of each
//! oracle of composition `C` on the **Domino listing**, with no theorem.
//!
//! The free composition comes from `C` alone ([`crate::game_invariant`]), as for
//! `domino prove --game C`. Its parameters are free, so no branch on a parameter folds. The
//! claims, the base frame and the fingerprint are those of the side tree of
//! `domino easycrypt debug --side-inv C` ([`execute_free`]); only the listing is different.
//! The run checks the game invariants of `C` and assumes the package invariants of its
//! instances.
//!
//! A run writes into [`game_run_dir`] the artifacts of a one-sided run (`index.html`,
//! `trace.json`, `summary.txt`, `models/`, `smt/`) and the result record
//! `one-sided_result.json`, whose owner is the composition.

use std::path::Path;
use std::sync::atomic::AtomicBool;
use std::time::Instant;

use crate::debug::driver::DebugError;
use crate::debug::layout::{game_run_dir, Layout};
use crate::debug::lockstep_run::{ListingKind, LockstepDebugOptions, LockstepRun};
use crate::debug::progress::DebugObserver;
use crate::debug::side_run::{execute_free, FreeRun};
use crate::game_invariant::error::Error as GameError;
use crate::game_invariant::{
    assumption_note, check_export, claims, composition_of, composition_theorem,
};
use crate::invariant_claim::select_exact;
use crate::project::Project;
use crate::transforms::theorem_transforms::EquivalenceTransform;
use crate::transforms::TheoremTransform;
use crate::util::smtsolver::SmtSolverBackend;
use crate::writers::smt::contexts::EquivalenceContext;

/// The oracles that `domino debug --game C [--oracle O]` runs: `O`, or every export of `C` in
/// declaration order.
///
/// Errors: [`GameError::UnknownComposition`] and [`GameError::UnknownOracle`], as for
/// `domino prove --game C`.
pub fn game_oracles<P: Project>(
    project: &P,
    composition: &str,
    oracle: Option<&str>,
) -> Result<Vec<String>, DebugError> {
    let comp = composition_of(project, composition).map_err(Box::new)?;
    match oracle {
        Some(oracle) => {
            check_export(comp, oracle).map_err(Box::new)?;
            Ok(vec![oracle.to_string()])
        }
        None => Ok(crate::game_invariant::export_names(comp)),
    }
}

/// Run one-sided execution of `oracle` of composition `composition` on the Domino listing, and
/// write its artifacts and result record into [`game_run_dir`] under `root`. With `claim`, the
/// run checks only the game invariant of that exact declared name; the paths are the same.
///
/// Errors: [`GameError::UnknownComposition`], [`GameError::UnknownOracle`],
/// [`GameError::NoGameInvariant`] (the errors of `domino prove --game C`), and
/// [`DebugError::NoInvariantMatches`] when no game invariant has the name `claim` (its help
/// lists the game invariants of `C`). All come before any solver work.
#[allow(clippy::too_many_arguments)]
pub fn run_game_command<P, B>(
    project: &P,
    composition: &str,
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
    let comp = composition_of(project, composition).map_err(Box::new)?;
    check_export(comp, oracle).map_err(Box::new)?;
    let (theorem, eq) = composition_theorem(comp);
    let (theorem_eq, auxs_eq) = EquivalenceTransform.transform_theorem(&theorem)?;
    let mut eqctx = EquivalenceContext::new(&eq, &theorem_eq, &auxs_eq);
    eqctx.load_invariants(project)?;
    let all = claims(&eqctx);
    if all.is_empty() {
        return Err(Box::new(GameError::NoGameInvariant {
            composition: composition.to_string(),
        })
        .into());
    }
    let selected = select_exact(all, claim, composition)?;
    let out = game_run_dir(root, composition, oracle, claim);
    let run = execute_free(
        FreeRun {
            theorem: &theorem,
            eqctx: &eqctx,
            composition,
            oracle,
            listing: ListingKind::Domino,
            claim,
            claims: selected,
        },
        opts,
        backend,
        out.clone(),
        observer,
        stop,
        started,
    )?;
    if let Some(note) = assumption_note(comp) {
        let summary = out.join(Layout::Plain.summary());
        let mut text = std::fs::read_to_string(&summary)?;
        text.push_str(&format!("\n{note}\n"));
        std::fs::write(&summary, text)?;
    }
    Ok(run)
}

/// The line that names the package invariants which `domino debug --game C` assumes, as
/// `domino prove --game C` prints it; `None` when `C` is unknown or no instance of it has a
/// package invariant.
pub fn assumption_line<P: Project>(project: &P, composition: &str) -> Option<String> {
    assumption_note(composition_of(project, composition).ok()?)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;
    use crate::debug::driver::Verdict;
    use crate::debug::lockstep::NodeKind;
    use crate::debug::progress::NopObserver;
    use crate::debug::side_run::run_side_command;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::process::IncrementalCvc5Backend;

    const GAME: &str = "game-invariant!main!S!";

    fn project_in(dir: &str) -> DirectoryProject<'static> {
        // the files are leaked: the project borrows them for the length of the test binary
        let dir = PathBuf::from(dir);
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(&dir).unwrap()));
        DirectoryProject::load(dir, files).unwrap()
    }

    fn opts() -> LockstepDebugOptions {
        LockstepDebugOptions::easycrypt(Some(10_000))
    }

    fn game_run(project: &DirectoryProject<'_>, claim: Option<&str>, root: &Path) -> LockstepRun {
        run_game_command(
            project,
            "S",
            "O",
            claim,
            &opts(),
            &IncrementalCvc5Backend,
            root,
            &mut NopObserver,
            None,
        )
        .unwrap()
    }

    fn failing(run: &LockstepRun) -> Vec<bool> {
        run.outcome
            .pairs
            .iter()
            .map(|p| matches!(p.verdict_of(GAME), Some(Verdict::GoalFails { .. })))
            .collect()
    }

    #[test]
    fn the_free_composition_splits_on_its_parameter_on_the_domino_listing() {
        let root = tempfile::tempdir().unwrap();
        let run = game_run(&project_in("testdata/debug/se25"), None, root.path());
        assert_eq!(run.meta.listing, "domino");
        assert_eq!(run.meta.subject, "game invariants of S");
        assert_eq!(run.outcome.tree.nodes[0].kind, NodeKind::Split);
        assert_eq!(run.outcome.pairs.len(), 4);
        // the two terminals with x < 0 fail `main`, the other two verify
        assert_eq!(failing(&run), [true, false, true, false]);
        for p in &run.outcome.pairs {
            if !matches!(p.verdict_of(GAME), Some(Verdict::GoalFails { .. })) {
                assert!(matches!(p.verdict_of(GAME), Some(Verdict::Verified)));
            }
        }
        // the labels are lines of the Domino listing, not of the EasyCrypt one
        let ec_out = tempfile::tempdir().unwrap();
        let ec = run_side_command(
            &project_in("testdata/debug/se25"),
            "T",
            "S",
            "O",
            &opts(),
            &IncrementalCvc5Backend,
            ec_out.path().to_path_buf(),
            &mut NopObserver,
            None,
        )
        .unwrap();
        assert_ne!(run.meta.left_listing, ec.meta.left_listing);
        assert!(
            run.meta.left_listing.contains("p.k <- n;"),
            "{}",
            run.meta.left_listing
        );
        // agreement: the same terminals fail on both listings
        assert_eq!(failing(&run), failing(&ec));
        assert_eq!(ec.meta.listing, "easycrypt");
        assert_eq!(ec.meta.subject, "side invariants of S");
    }

    #[test]
    fn the_free_instance_is_not_the_theorem_instance_of_the_same_name() {
        let root = tempfile::tempdir().unwrap();
        let run = game_run(
            &project_in("testdata/debug/se25-name-taken"),
            None,
            root.path(),
        );
        assert_eq!(run.outcome.tree.nodes[0].kind, NodeKind::Split);
    }

    #[test]
    fn the_run_writes_into_the_game_directory_by_its_claim() {
        let root = tempfile::tempdir().unwrap();
        let project = project_in("testdata/debug/se25");
        game_run(&project, None, root.path());
        let all = root.path().join("!game!/S/O/!all-claims!");
        for file in [
            "index.html",
            "trace.json",
            "summary.txt",
            "one-sided_result.json",
        ] {
            assert!(all.join(file).exists(), "{file}");
        }
        let summary = std::fs::read_to_string(all.join("summary.txt")).unwrap();
        assert!(
            summary.contains(
                "assumes the package invariants of P; prove them with domino prove --package P"
            ),
            "{summary}"
        );
        let record = std::fs::read_to_string(all.join("one-sided_result.json")).unwrap();
        assert!(record.contains("\"composition\": \"S\""), "{record}");
        assert!(record.contains("\"listing\": \"domino\""), "{record}");

        let run = game_run(&project, Some("main"), root.path());
        assert!(root.path().join("!game!/S/O/main/index.html").exists());
        assert_eq!(run.meta.claim, "main");
        assert!(!run.meta.all_claims);
    }

    #[test]
    fn an_unknown_claim_lists_the_game_invariants() {
        let root = tempfile::tempdir().unwrap();
        let err = run_game_command(
            &project_in("testdata/debug/se25"),
            "S",
            "O",
            Some("nope"),
            &opts(),
            &IncrementalCvc5Backend,
            root.path(),
            &mut NopObserver,
            None,
        )
        .unwrap_err();
        let DebugError::NoInvariantMatches(err) = err else {
            panic!("{err}");
        };
        assert_eq!(err.declared_names, ["main"]);
    }

    #[test]
    fn the_errors_of_prove_game_come_before_any_solver_work() {
        let project = project_in("testdata/debug/se25");
        let unknown = game_oracles(&project, "Nope", None).unwrap_err();
        assert!(matches!(
            unknown,
            DebugError::GameInvariant(ref e) if matches!(**e, GameError::UnknownComposition { .. })
        ));
        let oracle = game_oracles(&project, "S", Some("Nope")).unwrap_err();
        assert!(matches!(
            oracle,
            DebugError::GameInvariant(ref e) if matches!(**e, GameError::UnknownOracle { .. })
        ));
        assert_eq!(game_oracles(&project, "S", None).unwrap(), ["O"]);
    }

    #[test]
    fn the_project_index_lists_the_composition_after_the_theorems() {
        use crate::debug::index::{refresh_indexes, Level};
        let root = tempfile::tempdir().unwrap();
        game_run(&project_in("testdata/debug/se25"), None, root.path());
        let game = Level::Game {
            composition: "S".to_string(),
        };
        refresh_indexes(root.path(), &game).unwrap();
        refresh_indexes(root.path(), &Level::Project).unwrap();

        let project = std::fs::read_to_string(root.path().join("summary.txt")).unwrap();
        assert!(project.contains("game  S  1  1"), "{project}");
        assert!(project.contains("!game!/S/index.html"), "{project}");
        assert!(!project.contains("$Invariant"), "{project}");
        let html = std::fs::read_to_string(root.path().join("index.html")).unwrap();
        assert!(html.contains("href=\"!game!/S/index.html\""), "{html}");

        let index = std::fs::read_to_string(root.path().join("!game!/S/summary.txt")).unwrap();
        assert!(index.contains("game invariants of S"), "{index}");
        assert!(index.contains("O  !all-claims!  one-sided"), "{index}");
        assert!(index.contains("game S O [!all-claims!]"), "{index}");
        assert!(!index.contains("$Invariant"), "{index}");
    }
}
