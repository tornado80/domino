// SPDX-License-Identifier: MIT OR Apache-2.0

//! Symbolic-execution story 31: with `domino prove --package P` or `--game C`, `--claim` is a
//! wildcard on the declared names of the owner's invariants. Each test runs cvc5 on a small
//! fixture.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(dir: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(dir)
}

fn command(dir: &str, extra: &[&str]) -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_domino"));
    cmd.args(["prove", "--path"]).arg(fixture(dir)).args(extra);
    cmd
}

fn prove(dir: &str, extra: &[&str]) -> Output {
    command(dir, extra).output().unwrap()
}

fn text(out: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

/// Package `P` with the invariants `main` (true) and `bad` (false).
const PKG: &str = "testdata/prove-claim/pkg";
/// Composition `C` with the game invariants `main` (proved only with `other` assumed),
/// `other` (true) and `bad` (false).
const GAME: &str = "testdata/prove-claim/game";
const SE25: &str = "testdata/debug/se25";

#[test]
fn package_claim_selects_one_invariant() {
    let main = prove(PKG, &["--package", "P", "--claim", "main"]);
    assert!(main.status.success(), "{}", text(&main));
    let bad = prove(PKG, &["--package", "P", "--claim", "bad"]);
    assert!(!bad.status.success());
    assert!(
        text(&bad).contains("package-invariant!bad!P!"),
        "{}",
        text(&bad)
    );
    let all = prove(PKG, &["--package", "P"]);
    assert!(!all.status.success(), "{}", text(&all));
}

#[test]
fn package_claim_is_a_wildcard() {
    let out = prove(PKG, &["--package", "P", "--claim", "ma*"]);
    assert!(out.status.success(), "{}", text(&out));
}

#[test]
fn no_match_lists_the_names_before_any_solver_runs() {
    // with an empty PATH a solver cannot start: the error must come before
    let out = command(PKG, &["--package", "P", "--claim", "nope"])
        .env("PATH", "")
        .output()
        .unwrap();
    let text = text(&out);
    assert!(!out.status.success());
    assert!(
        text.contains("no invariant of `P` matches `nope`"),
        "{text}"
    );
    assert!(
        text.contains("the invariants of P are: main, bad"),
        "{text}"
    );

    let out = command(SE25, &["--game", "S", "--claim", "nope"])
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        crate::text(&out).contains("the invariants of S are: main"),
        "{}",
        crate::text(&out)
    );
}

#[test]
fn game_claim_proves_one_invariant_and_assumes_the_others() {
    // `main` is preserved by `O` only when `other` is assumed on the old state
    let main = prove(GAME, &["--game", "C", "--claim", "main"]);
    assert!(main.status.success(), "{}", text(&main));
    let all = prove(GAME, &["--game", "C"]);
    assert!(!all.status.success());
    assert!(
        text(&all).contains("game-invariant!bad!C!"),
        "{}",
        text(&all)
    );
}

#[test]
fn game_claim_applies_to_the_start() {
    let main = prove(
        GAME,
        &["--game", "C", "--invariant-start", "--claim", "main"],
    );
    assert!(main.status.success(), "{}", text(&main));
    let all = prove(GAME, &["--game", "C", "--invariant-start"]);
    assert!(!all.status.success(), "{}", text(&all));
}

#[test]
fn clap_refuses_package_with_injective_randmap() {
    let out = prove(PKG, &["--package", "P", "--injective-randmap"]);
    assert!(!out.status.success());
    assert!(text(&out).contains("cannot be used with"), "{}", text(&out));
}

#[test]
fn proof_claim_still_matches_the_equivalence_claims() {
    // no equivalence claim matches, as before that is no error; the package section of the
    // theorem is not filtered and its invariant fails
    let out = prove(SE25, &["--proof", "T", "--claim", "nope*"]);
    let text = text(&out);
    assert!(!text.contains("no invariant of"), "{text}");
    assert!(text.contains("package-invariant!main!P!"), "{text}");
}
