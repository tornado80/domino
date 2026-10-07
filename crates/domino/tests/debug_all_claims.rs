// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 19: `domino debug` runs all claims by default and sweeps every oracle.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn deps_project() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/story19/deps")
}

fn debug(extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["debug", "--progress", "none", "--path"])
        .arg(deps_project())
        .args(extra)
        .output()
        .unwrap()
}

#[test]
fn easycrypt_flag_is_gone_from_debug() {
    let out = debug(&["--easycrypt"]);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("--easycrypt"));
}

#[test]
fn proofstep_without_proof_is_rejected() {
    let out = debug(&["--proofstep", "0"]);
    assert!(!out.status.success());
}

#[cfg(feature = "cvc5-lib")]
#[test]
fn sweep_prints_a_line_per_oracle_and_fails_on_a_failing_claim() {
    let out = debug(&["--lockstep"]);
    assert!(!out.status.success(), "AbortDiff fails, so the sweep must exit non-zero");
    let stdout = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    for oracle in ["Branch", "AbortDiff", "AbortBoth", "Admitted"] {
        assert!(stdout.contains(oracle), "missing {oracle}:\n{stdout}");
    }
    assert!(deps_project()
        .join("_build/debug/index.html")
        .exists());
}

#[test]
fn easycrypt_debug_has_no_claim_flag() {
    let out = Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "debug", "--theorem", "x", "--claim", "x", "--project"])
        .arg(deps_project())
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("--claim"));
}

/// Story 22: `domino debug` with `--out <root>` on the deps project, in a new directory.
#[cfg(feature = "cvc5-lib")]
fn debug_into(root: &Path, extra: &[&str]) -> String {
    let mut args = vec!["--out", root.to_str().unwrap()];
    args.extend_from_slice(extra);
    let out = debug(&args);
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[cfg(feature = "cvc5-lib")]
#[test]
fn out_is_the_root_of_a_run_of_one_oracle() {
    let root = tempfile::tempdir().unwrap();
    let stdout = debug_into(
        root.path(),
        &["--proof", "T", "--proofstep", "0", "--oracle", "Branch"],
    );
    let run = root.path().join("T/gl-gr/Branch/!all-claims!");
    assert!(run.join("sequential_viewer.html").exists(), "{stdout}");
    assert!(run.join("sequential_result.json").exists(), "{stdout}");
    assert!(!root.path().join("T/gl-gr/index.html").exists());
    assert!(!stdout.contains("index "), "{stdout}");
}

#[cfg(feature = "cvc5-lib")]
#[test]
fn a_theorem_run_with_out_writes_its_index_and_one_for_each_proofstep() {
    let root = tempfile::tempdir().unwrap();
    let stdout = debug_into(root.path(), &["--proof", "T"]);
    assert!(root.path().join("T/index.html").exists(), "{stdout}");
    assert!(root.path().join("T/gl-gr/index.html").exists(), "{stdout}");
    assert!(!root.path().join("index.html").exists(), "{stdout}");
    assert!(stdout.contains("index    "), "{stdout}");
}

#[cfg(feature = "cvc5-lib")]
#[test]
fn a_proofstep_run_writes_no_project_index_and_updates_the_theorem_index() {
    let root = tempfile::tempdir().unwrap();
    let stdout = debug_into(root.path(), &["--proof", "T", "--proofstep", "0"]);
    assert!(root.path().join("T/gl-gr/index.html").exists(), "{stdout}");
    assert!(!root.path().join("T/index.html").exists(), "{stdout}");
    assert!(!root.path().join("index.html").exists(), "{stdout}");

    debug_into(root.path(), &["--proof", "T"]);
    let before = std::fs::read_to_string(root.path().join("T/summary.txt")).unwrap();
    let stdout = debug_into(root.path(), &["--proof", "T", "--proofstep", "0", "--lockstep"]);
    assert!(stdout.contains("T/index.html      (updated)"), "{stdout}");
    let after = std::fs::read_to_string(root.path().join("T/summary.txt")).unwrap();
    assert_ne!(before, after, "the run count of step 0 grows");

    let step = std::fs::read_to_string(root.path().join("T/gl-gr/summary.txt")).unwrap();
    assert!(step.contains("Branch  !all-claims!  sequential"), "{step}");
    assert!(step.contains("Branch  !all-claims!  lockstep"), "{step}");
}

#[cfg(feature = "cvc5-lib")]
#[test]
fn a_single_claim_run_and_an_all_claim_run_of_one_oracle_both_show() {
    let root = tempfile::tempdir().unwrap();
    debug_into(root.path(), &["--proof", "T", "--proofstep", "0", "--oracle", "Branch"]);
    debug_into(
        root.path(),
        &["--proof", "T", "--proofstep", "0", "--claim", "invariant"],
    );
    let step = std::fs::read_to_string(root.path().join("T/gl-gr/summary.txt")).unwrap();
    assert!(step.contains("Branch  !all-claims!  sequential"), "{step}");
    assert!(step.contains("Branch  invariant  sequential"), "{step}");
}
