// SPDX-License-Identifier: MIT OR Apache-2.0

//! The proof tree of `domino html`: which claims a path cites, which of them are
//! proved, and the bound at the root. Uses the theorems of `derived_assumptions`.

use std::collections::BTreeMap;

use super::derived_assumptions::{load, reduction};
use crate::{
    proof::Proof,
    theorem::Theorem,
    writers::proof_tree::{bound, claim_graph, ClaimGraph, ClaimKind},
};

fn derived_proofs<'a>(theorem: &Theorem<'a>) -> BTreeMap<String, Proof<'a>> {
    theorem
        .assumptions
        .iter()
        .filter_map(|a| {
            let proof = theorem
                .derivation
                .proof_of(&theorem.instances, &theorem.game_hops, a)?;
            Some((a.name.clone(), proof))
        })
        .collect()
}

fn graph(theorem: &Theorem) -> ClaimGraph {
    claim_graph(theorem, &derived_proofs(theorem))
}

fn claim<'g>(graph: &'g ClaimGraph, name: &str) -> (usize, &'g crate::writers::proof_tree::Claim) {
    graph
        .claims
        .iter()
        .enumerate()
        .find(|(_, c)| c.name == name)
        .unwrap_or_else(|| panic!("no claim {name}"))
}

fn names(graph: &ClaimGraph, ids: impl IntoIterator<Item = usize>) -> Vec<String> {
    ids.into_iter()
        .map(|id| graph.claims[id].name.clone())
        .collect()
}

/// `(leaf, count)` with plain counts (no hybrids in these theorems).
fn leaves(graph: &ClaimGraph, root: usize) -> (Vec<(String, u64)>, bool) {
    let (leaves, cycle) = bound(graph, root);
    let leaves = leaves
        .into_iter()
        .map(|(leaf, coefficient)| (graph.claims[leaf].name.clone(), coefficient[&Vec::new()]))
        .collect();
    (leaves, cycle)
}

#[test]
fn derived_chain_expands_to_its_base_assumption() {
    let theorem = load(&format!(
        "  assumptions {{\n    derived A: g3 ~ g4\n    derived B: g5 ~ g6\n    P: g1 ~ g3\n  }}\n  \
         gamehops {{\n{}{}{}  }}\n  propositions {{\n    Goal: g1 ~ g2\n  }}\n",
        reduction("g1", "g2", "A", "g3", "g4"),
        reduction("g3", "g4", "B", "g5", "g6"),
        reduction("g5", "g6", "P", "g1", "g3"),
    ));
    let proof_of_a = derived_proofs(&theorem).remove("A").expect("A is derived");
    assert_eq!(
        proof_of_a
            .reductions()
            .map(|r| r.assumption_name())
            .collect::<Vec<_>>(),
        ["B"]
    );

    let graph = graph(&theorem);
    assert_eq!(names(&graph, graph.roots.clone()), ["Goal"]);
    let (_, a) = claim(&graph, "A");
    assert_eq!(a.kind, ClaimKind::Derived);
    assert_eq!(a.view.as_deref(), Some("a:A"));
    assert_eq!(a.depth, Some(2));
    assert_eq!(names(&graph, a.cites.iter().map(|c| c.claim)), ["B"]);
    let (_, p) = claim(&graph, "P");
    assert_eq!(p.kind, ClaimKind::Base);
    assert_eq!(p.view, None);

    let (leaves, cycle) = leaves(&graph, graph.roots[0]);
    assert_eq!(leaves, [("P".to_string(), 1)]);
    assert!(!cycle);
}

#[test]
fn an_assumption_cited_twice_counts_twice() {
    let theorem = load(&format!(
        "  assumptions {{\n    A: g5 ~ g6\n  }}\n  gamehops {{\n{}{}  }}\n  \
         propositions {{\n    Goal: g1 ~ g3\n  }}\n",
        reduction("g1", "g2", "A", "g5", "g6"),
        reduction("g2", "g3", "A", "g5", "g6"),
    ));
    let graph = graph(&theorem);
    let (_, goal) = claim(&graph, "Goal");
    assert_eq!(
        names(&graph, goal.cites.iter().map(|c| c.claim)),
        ["A", "A"]
    );
    assert_eq!(leaves(&graph, graph.roots[0]).0, [("A".to_string(), 2)]);
}

#[test]
fn a_base_assumption_that_a_proposition_proves_is_expanded() {
    let theorem = load(&format!(
        "  assumptions {{\n    A: g3 ~ g4\n    B: g5 ~ g6\n  }}\n  gamehops {{\n{}{}  }}\n  \
         propositions {{\n    Top: g1 ~ g2\n    Lemma: g4 ~ g3\n  }}\n",
        reduction("g1", "g2", "A", "g3", "g4"),
        reduction("g3", "g4", "B", "g5", "g6"),
    ));
    let graph = graph(&theorem);
    // Lemma is drawn under A, the assumption it proves.
    assert_eq!(names(&graph, graph.roots.clone()), ["Top"]);
    let (_, a) = claim(&graph, "A");
    assert_eq!(a.kind, ClaimKind::ProvedByProposition);
    assert_eq!(a.proved_by.as_deref(), Some("Lemma"));
    assert_eq!(a.view.as_deref(), Some("p:Lemma"));
    assert_eq!(
        leaves(&graph, graph.roots[0]),
        (vec![("B".to_string(), 1)], false)
    );
}

#[test]
fn a_proposition_that_cites_its_own_assumption_is_a_cycle() {
    // A is a base assumption, so the theorem loads; the tree shows the circularity.
    let theorem = load(&format!(
        "  assumptions {{\n    A: g1 ~ g2\n  }}\n  gamehops {{\n{}    conjecture g1 g3\n    \
         conjecture g4 g2\n  }}\n  propositions {{\n    A: g1 ~ g2\n  }}\n",
        reduction("g3", "g4", "A", "g1", "g2"),
    ));
    let graph = graph(&theorem);
    // Only the cycle reaches the proposition, so it is a root anyway.
    assert_eq!(names(&graph, graph.roots.clone()), ["A"]);
    assert_eq!(graph.claims[graph.roots[0]].kind, ClaimKind::Proposition);
    let assumption = graph
        .claims
        .iter()
        .position(|c| c.name == "A" && c.kind == ClaimKind::ProvedByProposition)
        .expect("the assumption node");
    assert!(graph.claims[assumption]
        .cites
        .iter()
        .any(|c| c.claim == assumption));
    let (_, cycle) = leaves(&graph, graph.roots[0]);
    assert!(cycle);
}
