// SPDX-License-Identifier: MIT OR Apache-2.0

//! Symbolic-execution story 33: `domino debug --package P` runs one-sided execution of each
//! oracle of package `P` on the Domino listing, with each import call an open call and no
//! theorem. The runs need the `cvc5-lib` build; the clap checks do not.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn se29() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/debug/se29")
}

fn domino_in(project: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(args)
        .arg("--project")
        .arg(project)
        .output()
        .unwrap()
}

fn debug_in(project: &Path, extra: &[&str]) -> Output {
    let mut args = vec!["debug", "--progress", "none"];
    args.extend_from_slice(extra);
    domino_in(project, &args)
}

fn text(out: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

#[test]
fn clap_refuses_package_with_game_and_each_two_sided_flag() {
    for extra in [
        &["--game", "G"][..],
        &["--theorem", "T"],
        &["--gamehop", "0"],
        &["--claim-set", "core"],
        &["--lockstep"],
        &["--no-check-left"],
        &["--no-check-right"],
        &["--first-failure-per-claim"],
    ] {
        let mut args = vec!["--package", "Ctr"];
        args.extend_from_slice(extra);
        let out = debug_in(&se29(), &args);
        let text = text(&out);
        assert!(!out.status.success(), "{extra:?}: {text}");
        assert!(text.contains("cannot be used with"), "{extra:?}: {text}");
    }
}

#[cfg(feature = "cvc5-lib")]
mod runs {
    use super::*;

    /// A copy of `src` in a temporary directory, so that `_build/` is not written into the
    /// source tree.
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
    fn bad_fails_as_in_prove_package_and_writes_the_package_directory() {
        let project = copy_of(&se29());
        let out = debug_in(project.path(), &["--package", "Ctr"]);
        let printed = text(&out);
        assert!(!out.status.success(), "{printed}");
        assert!(
            printed.contains("package Ctr Step: 1 terminals, ok"),
            "{printed}"
        );
        assert!(
            printed.contains("package Ctr Bad: 2 terminals, FAILS"),
            "{printed}"
        );
        assert!(
            printed.contains("package Ctr Ping: 1 terminals, ok"),
            "{printed}"
        );
        let run = project
            .path()
            .join("_build/debug/!package!/Ctr/Bad/!all-claims!");
        for file in [
            "index.html",
            "trace.json",
            "summary.txt",
            "one-sided_result.json",
        ] {
            assert!(run.join(file).exists(), "{file}: {printed}");
        }
        let summary = std::fs::read_to_string(run.join("summary.txt")).unwrap();
        assert!(summary.contains("an abort ends the oracle"), "{summary}");

        // agreement: `prove --package` fails on `Bad` only
        let prove = domino_in(project.path(), &["prove", "--package", "Ctr"]);
        let proved = text(&prove);
        assert!(!prove.status.success(), "{proved}");
        assert!(proved.contains("could not"), "{proved}");
        assert!(proved.contains("be proved for Bad"), "{proved}");
    }

    #[test]
    fn the_project_index_lists_the_package() {
        let project = copy_of(&se29());
        debug_in(project.path(), &["--package", "Ctr", "--claim", "nonneg"]);
        assert!(project
            .path()
            .join("_build/debug/!package!/Ctr/Bad/nonneg/index.html")
            .exists());
        // a plain run writes the project index, with the package rows after the theorems
        debug_in(project.path(), &[]);
        let summary =
            std::fs::read_to_string(project.path().join("_build/debug/summary.txt")).unwrap();
        assert!(summary.contains("package  Ctr"), "{summary}");
        assert!(summary.contains("!package!/Ctr/index.html"), "{summary}");
    }

    #[test]
    fn the_errors_name_the_invariants_and_the_packages() {
        let project = copy_of(&se29());
        let out = debug_in(project.path(), &["--package", "Ctr", "--claim", "nope"]);
        assert!(!out.status.success());
        assert!(
            text(&out).contains("the invariants of Ctr are: nonneg"),
            "{}",
            text(&out)
        );
        let out = debug_in(project.path(), &["--package", "Src"]);
        assert!(
            text(&out).contains("does not declare an invariant"),
            "{}",
            text(&out)
        );
        let out = debug_in(project.path(), &["--package", "X"]);
        assert!(text(&out).contains("known packages"), "{}", text(&out));
        let out = debug_in(project.path(), &["--package", "Ctr", "--oracle", "Nope"]);
        assert!(!out.status.success(), "{}", text(&out));
    }
}
