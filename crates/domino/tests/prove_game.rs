// SPDX-License-Identifier: MIT OR Apache-2.0

//! Symbolic-execution story 30: `domino prove --game C` proves the game invariants of a
//! composition on their own. Each test runs cvc5 on a small fixture.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(dir: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(dir)
}

fn prove(dir: &str, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["prove", "--project"])
        .arg(fixture(dir))
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

const SE25: &str = "testdata/debug/se25";
const SAME_NAME: &str = "testdata/prove-game/same-name";

#[test]
fn the_oracle_group_of_se25_fails_and_the_run_exits_non_zero() {
    let out = prove(SE25, &["--game", "S"]);
    let text = text(&out);
    assert!(!out.status.success(), "{text}");
    assert!(
        text.contains("game-invariant!main!S!") && text.contains("for O"),
        "{text}"
    );
}

#[test]
fn the_start_group_of_se25_verifies() {
    let out = prove(SE25, &["--game", "S", "--invariant-start"]);
    assert!(out.status.success(), "{}", text(&out));
}

#[test]
fn oracle_selects_only_its_group() {
    // only the group of `O` runs, and it fails
    let out = prove(SE25, &["--game", "S", "--oracle", "O"]);
    let text = text(&out);
    assert!(!out.status.success(), "{text}");
    assert!(!text.contains("invariant-start ("), "{text}");
}

#[test]
fn the_free_parameters_are_read_by_the_game_invariant() {
    let out = prove("test-projects/test-game-invariant-params", &["--game", "C"]);
    assert!(out.status.success(), "{}", text(&out));
}

#[test]
fn the_report_names_the_assumed_package_invariants() {
    let out = prove(SE25, &["--game", "S", "--invariant-start"]);
    assert!(
        text(&out).contains(
            "assumes the package invariants of P; prove them with domino prove --package P"
        ),
        "{}",
        text(&out)
    );
}

#[test]
fn a_composition_with_no_game_invariant_gives_the_hint() {
    let out = prove(SAME_NAME, &["--game", "Bare"]);
    let text = text(&out);
    assert!(!out.status.success());
    assert!(
        text.contains("composition `Bare` has no game invariant") && text.contains("--package"),
        "{text}"
    );
}

#[test]
fn an_unknown_composition_lists_the_compositions() {
    let out = prove(SAME_NAME, &["--game", "Nope"]);
    let text = text(&out);
    assert!(!out.status.success());
    assert!(text.contains("Bare, X"), "{text}");
}

#[test]
fn an_unknown_oracle_lists_the_exports() {
    let out = prove(SE25, &["--game", "S", "--oracle", "Nope"]);
    let text = text(&out);
    assert!(!out.status.success());
    assert!(text.contains("exports of S: O"), "{text}");
}

#[test]
fn clap_refuses_game_with_the_other_targets() {
    for extra in [
        &["--theorem", "T"][..],
        &["--gamehop", "0"],
        &["--package", "P"],
        &["--injective-randmap"],
    ] {
        let mut args = vec!["--game", "S"];
        args.extend_from_slice(extra);
        let out = prove(SE25, &args);
        let text = text(&out);
        assert!(!out.status.success(), "{extra:?}: {text}");
        assert!(text.contains("cannot be used with"), "{extra:?}: {text}");
        if extra[0].starts_with("--theorem") {
            assert!(text.contains("ADR"), "{extra:?}: {text}");
            assert!(
                text.contains("--game cannot be used with --theorem or --gamehop"),
                "{extra:?}: {text}"
            );
        }
    }
}

#[test]
fn package_and_game_select_by_kind_when_the_names_are_the_same() {
    let pkg = prove(SAME_NAME, &["--package", "X"]);
    assert!(pkg.status.success(), "{}", text(&pkg));
    let game = prove(SAME_NAME, &["--game", "X"]);
    assert!(game.status.success(), "{}", text(&game));
    // the error of an unknown oracle names the kind that the flag selects
    let pkg = prove(SAME_NAME, &["--package", "X", "--oracle", "Nope"]);
    assert!(text(&pkg).contains("package X"), "{}", text(&pkg));
    let game = prove(SAME_NAME, &["--game", "X", "--oracle", "Nope"]);
    assert!(text(&game).contains("composition X"), "{}", text(&game));
}

/// Story EC 95: `domino gamehops` prints each theorem's game hops with their index.
#[test]
fn gamehops_lists_the_game_hops_of_each_theorem() {
    let out = Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["gamehops", "--project"])
        .arg(fixture(SE25))
        .output()
        .unwrap();
    let text = text(&out);
    assert!(out.status.success(), "{text}");
    assert!(text.starts_with("T:\n0: Equivalence "), "{text}");
}
