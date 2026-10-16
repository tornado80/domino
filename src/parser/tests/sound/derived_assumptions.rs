// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 20: a `derived` assumption is a proof obligation. It is established by a
//! least fixpoint over the theorem's hops, and a reduction is an edge only when the
//! assumption it cites is already established.
//!
//! The games `Derived1` .. `Derived6` are structurally the same, so a reduction
//! between any two of them passes the structural checks. Each test writes its own
//! hop graph over the instances `g1` .. `g6`.

use std::collections::HashMap;

use crate::{
    package::{Composition, Package},
    parser::{
        error::UnestablishedClaimsError,
        tests::{games, packages, theorems},
        theorem::ParseTheoremError,
    },
    theorem::Theorem,
};

fn fixtures() -> (HashMap<String, Package>, HashMap<String, Composition>) {
    let pkgs = packages::parse_files(&["KeyRealMoreParams.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "Derived1.ssp",
            "Derived2.ssp",
            "Derived3.ssp",
            "Derived4.ssp",
            "Derived5.ssp",
            "Derived6.ssp",
        ],
        &pkgs,
    );
    (pkgs, games)
}

/// A theorem with the instances `g1` .. `g6` (game `DerivedN`, `k: 0`), then `body`.
fn theorem_source(body: &str) -> String {
    let instances: String = (1..=6)
        .map(|i| format!("  instance g{i} = Derived{i} {{ params {{ m: o, z: zo, k: 0, }} }}\n"))
        .collect();
    format!(
        "theorem T {{\n  const o: Integer;\n  const zo: Bits(o);\n  const b: Integer;\n{instances}{body}\n}}\n"
    )
}

/// A reduction from `left` to `right` that cites `cited`, whose games are `cited_left`
/// and `cited_right`.
pub(super) fn reduction(
    left: &str,
    right: &str,
    cited: &str,
    cited_left: &str,
    cited_right: &str,
) -> String {
    format!(
        "    reduction {left} {right} {{\n      assumption {cited}\n      \
         map {cited_left} {left} {{ key: key }}\n      \
         map {cited_right} {right} {{ key: key }}\n    }}\n"
    )
}

/// Loads a theorem that must be accepted. The inputs are leaked: a `Theorem` borrows them.
pub(super) fn load(body: &str) -> Theorem<'static> {
    let (pkgs, games) = Box::leak(Box::new(fixtures()));
    let source: &'static str = Box::leak(theorem_source(body).into_boxed_str());
    theorems::parse(source, "T.ssp", pkgs, games)
}

fn load_fails(body: &str) -> UnestablishedClaimsError {
    let (pkgs, games) = fixtures();
    let source = theorem_source(body);
    match theorems::parse_fails(&source, "T.ssp", &pkgs, &games) {
        ParseTheoremError::UnestablishedClaims(err) => err,
        other => panic!(
            "expected UnestablishedClaims, got {:?}",
            miette::Report::new(other)
        ),
    }
}

/// One line per failed claim, as `<name>: <reason>`, sorted by name.
fn failures(err: &UnestablishedClaimsError) -> Vec<String> {
    let mut lines: Vec<_> = err
        .related
        .iter()
        .map(|claim| format!("{}: {}", claim.claim_name, claim.reason))
        .collect();
    lines.sort();
    lines
}

#[test]
fn self_cycle_is_rejected() {
    let err = load_fails(&format!(
        "  assumptions {{\n    derived A: g1 ~ g2\n  }}\n  gamehops {{\n{}  }}\n",
        reduction("g3", "g4", "A", "g1", "g2") + "    conjecture g1 g3\n    conjecture g4 g2\n"
    ));

    assert_eq!(
        failures(&err),
        ["A: cycle A -> A via reduction g3 ~ g4 (A)"]
    );
}

#[test]
fn two_cycle_is_rejected_and_both_are_reported() {
    let err = load_fails(&format!(
        "  assumptions {{\n    derived A: g1 ~ g2\n    derived B: g3 ~ g4\n  }}\n  gamehops {{\n{}{}  }}\n",
        reduction("g1", "g2", "B", "g3", "g4"),
        reduction("g3", "g4", "A", "g1", "g2"),
    ));

    assert_eq!(
        failures(&err),
        [
            "A: cycle A -> B -> A via reduction g1 ~ g2 (B), reduction g3 ~ g4 (A)",
            "B: cycle B -> A -> B via reduction g3 ~ g4 (A), reduction g1 ~ g2 (B)",
        ]
    );
}

#[test]
fn chain_is_accepted_in_any_order() {
    let theorem = load(&format!(
        "  assumptions {{\n    derived A: g1 ~ g2\n    derived B: g3 ~ g4\n    P: g5 ~ g6\n  }}\n  gamehops {{\n{}{}  }}\n",
        reduction("g1", "g2", "B", "g3", "g4"),
        reduction("g3", "g4", "P", "g5", "g6"),
    ));

    let derivation = &theorem.derivation;
    assert_eq!(derivation.depth("A"), Some(2));
    assert_eq!(derivation.depth("B"), Some(1));
    assert_eq!(derivation.depth("P"), Some(0));
    assert_eq!(derivation.base_assumptions(), ["P"]);
}

#[test]
fn missing_path_is_not_a_cycle() {
    let err = load_fails("  assumptions {\n    derived A: g1 ~ g2\n  }\n");

    assert_eq!(failures(&err), ["A: no path between g1 and g2"]);
}

#[test]
fn all_failures_are_reported_together() {
    let err = load_fails(
        "  assumptions {\n    derived A: g1 ~ g2\n    derived B: g3 ~ g4\n  }\n  \
         propositions {\n    Goal: g5 ~ g6\n  }\n",
    );

    assert_eq!(
        failures(&err),
        [
            "A: no path between g1 and g2",
            "B: no path between g3 and g4",
            "Goal: no path between g5 and g6",
        ]
    );
}

#[test]
fn proposition_through_unestablished_reduction_is_rejected() {
    let err = load_fails(&format!(
        "  assumptions {{\n    derived A: g3 ~ g4\n  }}\n  gamehops {{\n{}  }}\n  \
         propositions {{\n    Goal: g1 ~ g2\n  }}\n",
        reduction("g1", "g2", "A", "g3", "g4"),
    ));

    assert_eq!(
        failures(&err),
        [
            "A: no path between g3 and g4",
            "Goal: the path needs the unestablished assumption A",
        ]
    );
}

#[test]
fn unmarked_assumptions_are_base_as_before() {
    let theorem = load(&format!(
        "  assumptions {{\n    P: g3 ~ g4\n    Q: g5 ~ g6\n  }}\n  gamehops {{\n{}  }}\n  \
         propositions {{\n    Goal: g1 ~ g2\n  }}\n",
        reduction("g1", "g2", "P", "g3", "g4"),
    ));

    assert_eq!(theorem.derivation.base_assumptions(), ["P", "Q"]);
    assert_eq!(theorem.proofs.len(), 1);
    assert_eq!(
        theorem.derivation.summary(&theorem.name),
        "T: proven relative to 2 base assumptions: P, Q; \
         0 derived assumptions established (max depth 0); modulo conjectures: none"
    );
}

#[test]
fn specialized_hop_does_not_establish_the_general_claim() {
    let err = load_fails(
        "  instance x0 = Derived1 { params { m: o, z: zo, k: 0, } }\n  \
         instance xb = Derived2 { params { m: o, z: zo, k: b, } }\n  \
         assumptions {\n    derived A: x0 ~ xb\n  }\n  \
         gamehops {\n    conjecture x0 g2\n  }\n",
    );

    assert_eq!(failures(&err), ["A: no path between x0 and xb"]);
}

#[test]
fn propositions_may_come_before_gamehops() {
    let theorem = load(&format!(
        "  assumptions {{\n    P: g3 ~ g4\n  }}\n  propositions {{\n    Goal: g1 ~ g2\n  }}\n  \
         gamehops {{\n{}  }}\n",
        reduction("g1", "g2", "P", "g3", "g4"),
    ));

    assert_eq!(theorem.proofs.len(), 1);
}

#[test]
fn conjecture_establishes_modulo_conjecture() {
    let theorem = load(
        "  assumptions {\n    derived A: g1 ~ g2\n  }\n  gamehops {\n    conjecture g1 g2\n  }\n",
    );

    assert_eq!(theorem.derivation.depth("A"), Some(1));
    assert_eq!(theorem.derivation.conjectures(), ["g1 ~ g2"]);
    assert_eq!(
        theorem.derivation.summary(&theorem.name),
        "T: proven relative to 0 base assumptions: none; \
         1 derived assumptions established (max depth 1); modulo conjectures: g1 ~ g2"
    );
}
