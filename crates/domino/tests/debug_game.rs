// SPDX-License-Identifier: MIT OR Apache-2.0

//! Symbolic-execution story 32: `domino debug --game C` runs one-sided execution of each oracle
//! of composition `C` on the Domino listing, with no theorem. The runs need the `cvc5-lib`
//! build; the clap checks do not.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn se25() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/debug/se25")
}

fn debug_in(project: &Path, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["debug", "--progress", "none", "--path"])
        .arg(project)
        .args(extra)
        .output()
        .unwrap()
}

fn text(out: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

#[test]
fn clap_refuses_game_with_each_two_sided_flag() {
    for extra in [
        &["--proof", "T"][..],
        &["--proofstep", "0"],
        &["--claim-set", "core"],
        &["--lockstep"],
        &["--no-check-left"],
        &["--no-check-right"],
        &["--first-failure-per-claim"],
    ] {
        let mut args = vec!["--game", "S"];
        args.extend_from_slice(extra);
        let out = debug_in(&se25(), &args);
        let text = text(&out);
        assert!(!out.status.success(), "{extra:?}: {text}");
        assert!(text.contains("cannot be used with"), "{extra:?}: {text}");
    }
}

#[cfg(feature = "cvc5-lib")]
mod runs {
    use super::*;

    /// A copy of `testdata/debug/se25` in a temporary directory, so that `_build/` is not
    /// written into the source tree.
    fn copy_of(src: &Path) -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        copy_dir(src, dir.path());
        dir
    }

    fn copy_dir(src: &Path, dst: &Path) {
        std::fs::create_dir_all(dst).unwrap();
        for entry in std::fs::read_dir(src).unwrap().flatten() {
            let to = dst.join(entry.file_name());
            if entry.path().is_dir() {
                copy_dir(&entry.path(), &to);
            } else {
                std::fs::copy(entry.path(), to).unwrap();
            }
        }
    }

    #[test]
    fn a_failing_game_invariant_fails_the_run_and_writes_the_game_directory() {
        let project = copy_of(&se25());
        let out = debug_in(project.path(), &["--game", "S"]);
        assert!(!out.status.success(), "{}", text(&out));
        let run = project.path().join("_build/debug/!game!/S/O/!all-claims!");
        for file in [
            "index.html",
            "trace.json",
            "summary.txt",
            "one-sided_result.json",
        ] {
            assert!(run.join(file).exists(), "{file}: {}", text(&out));
        }
        let index =
            std::fs::read_to_string(project.path().join("_build/debug/!game!/S/summary.txt"))
                .unwrap();
        assert!(index.contains("O  !all-claims!  one-sided"), "{index}");
        assert!(
            text(&out).contains("assumes the package invariants of P"),
            "{}",
            text(&out)
        );
    }

    #[test]
    fn claim_selects_the_run_directory_and_out_moves_the_root() {
        let project = copy_of(&se25());
        let out = debug_in(project.path(), &["--game", "S", "--claim", "main"]);
        assert!(!out.status.success(), "main fails on x < 0");
        assert!(project
            .path()
            .join("_build/debug/!game!/S/O/main/index.html")
            .exists());

        let root = tempfile::tempdir().unwrap();
        let out_arg = root.path().to_str().unwrap();
        debug_in(project.path(), &["--game", "S", "--out", out_arg]);
        assert!(root
            .path()
            .join("!game!/S/O/!all-claims!/index.html")
            .exists());
    }

    #[test]
    fn an_unknown_claim_lists_the_game_invariants() {
        let project = copy_of(&se25());
        let out = debug_in(project.path(), &["--game", "S", "--claim", "nope"]);
        assert!(!out.status.success());
        assert!(
            text(&out).contains("the invariants of S are: main"),
            "{}",
            text(&out)
        );
    }

    #[test]
    fn the_project_index_lists_the_composition() {
        let project = copy_of(&se25());
        // the project index exists first, so the game run updates it
        let theorem = debug_in(project.path(), &["--oracle", "O"]);
        assert!(!theorem.status.success());
        debug_in(project.path(), &["--game", "S"]);
        let summary =
            std::fs::read_to_string(project.path().join("_build/debug/summary.txt")).unwrap();
        assert!(summary.contains("game  S"), "{summary}");
        assert!(summary.contains("!game!/S/index.html"), "{summary}");
    }

    #[test]
    fn unknown_composition_and_oracle_give_the_errors_of_prove_game() {
        let project = copy_of(&se25());
        let out = debug_in(project.path(), &["--game", "Nope"]);
        assert!(
            text(&out).contains("known compositions: S"),
            "{}",
            text(&out)
        );
        let out = debug_in(project.path(), &["--game", "S", "--oracle", "Nope"]);
        assert!(text(&out).contains("exports of S: O"), "{}", text(&out));
    }
}
