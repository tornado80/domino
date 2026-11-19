---
title: Formal verification of the reduction check
label: wayfinder:map
---

## Destination

A written soundness theorem for Domino's reduction check (graph level, with a staged plan to SSP
semantics), plus the chosen verification approach: tool chain, the Rust code in scope, and how the
Lean model connects to that code. The result is ready to hand off for implementation.

## Notes

- Domain: SSP (state-separating proofs). The check is in `src/parser/reduction.rs`
  (`handle_reduction_body`, `compare_reduction`, `handle_mapspec_assumption`,
  `package_instances_diff`), and it is mixed with the pest parser and miette diagnostics.
- Lean is **fixed** as the home of the soundness theorem. A Rust-native verifier (Verus, Creusot)
  is permitted only to prove the Rust code against a copy of the Lean spec, and the copy is
  linked to the Lean spec by review.
- The theorem is staged: (1) graph level — if the check passes, there is a reduction composition
  R so that each construction game equals R composed with its assumption game, up to the mapping.
  Packages stay opaque. (2) Semantic level — a plan for how stage 1 connects to an SSP semantics.
- Validation: a bug corpus of known unsound reductions. The theorem's definitions must reject each
  item in the corpus.
- Hybrid reductions (`is_hybrid`) are in scope.
- Plan, do not do: tickets produce decisions, not proofs or refactors.
- Skills: `/grilling`, `/domain-modeling`, `/research`, `/prototype`, `/domino` (for SSP
  projects and the theorem file syntax).
- Writing style: ASD-STE100 Simplified Technical English.

## Decisions so far

<!-- one line per closed ticket -->

- [Bug corpus of unsound reductions](tickets/01-bug-corpus.md) — the current check accepts 7 unsound hops and panics on 3; 9 defect classes (W1, M1–M2, R1, X1–X2, E1–E3) are the obligations of the theorem ([corpus](assets/bug-corpus/README.md))

## Not yet specified

- **Stage 2 connection.** How the graph-level theorem connects to the semantic theory that the
  SSP formalization survey selects (import, re-prove, or paper argument). This depends on
  the survey result.
- **Lean project home and build.** Where the Lean project lives (in this repo, or a separate
  repo), Lake/Mathlib version, Nix flake integration, and CI. This depends on the connection
  strategy (Aeneas output must be checked in CI).
- **Spec synchronization.** If a Rust-native verifier is selected, how the copy of the spec stays
  equal to the Lean spec over time.
- **Hand-off plan.** The order of the implementation work (refactor, model, proofs), and the effort
  estimate. This is only possible after the connection strategy is selected.

## Out of scope

- Certificate checking (Rust emits a witness, a verified checker validates it): not selected for
  evaluation.
- Kani and differential or property tests: not selected for evaluation.
- A framework shared with the SMT translation: the SMT translation is a separate effort.
- Correctness of game instantiation (`InstantiationContext`, parameter resolution): it is a
  trusted input to the check.
- Writing the proofs or doing the refactor: this map plans them, it does not do them.
