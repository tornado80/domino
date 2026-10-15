# Story 20 — Derived assumptions: implementation report

## What was done

- **Grammar** (`src/parser/ssp.pest`): `assumption_entry` takes an optional `kw_derived`.
  The keyword matches only when another identifier follows, so an assumption can still
  have the name `derived`.
- **`Assumption`** (`src/gamehops/reduction.rs`): new field `kind: AssumptionKind`
  (`Base` / `Derived`). `handle_assumptions` reads the keyword before the name triplet.
- **Path search** (`src/proof.rs`): `Proof::try_new` takes `edge_allowed: impl Fn(&GameHop) -> bool`.
  It keeps the original hop slice and indices, so `Proof::game_hops()` and the HTML writer
  are not changed.
- **Fixpoint** (`src/derivation.rs`, new): `derivation::derive` owns the established set.
  `establish` is the least fixpoint (base = depth 0, derived = 1 + max cited depth).
  After it, the propositions are checked with the same edge rule. For each failure,
  `FailedAssumptions` builds the citation graph between unestablished assumptions (path
  search with all reductions allowed) and reports "no path", a cycle with its reductions,
  or "needs unestablished X".
- **Propositions** (`src/parser/theorem.rs`): `handle_propositions` only records name, games
  and span. `handle_theorem` calls `derive_claims` once, after all blocks. `propositions`
  before `gamehops` now works.
- **Errors** (`src/parser/error.rs`): `UnestablishedClaimsError` holds one
  `UnestablishedClaimError` per failed claim (miette `related`), each with a span on the
  assumption or proposition entry. `UnprovenTheoremError` is removed; the new error
  replaces it.
- **Summary**: `Theorem::derivation` gives `Derivation::summary`. `Project::prove` prints it
  for every theorem, before the `--theorem` selection check and before SMT work.
- **UI fix** (found on sight, `crates/domino/src/ui.rs`): `IndicatifUI::println` lost every
  line when stdout was not a terminal (indicatif's `MultiProgress::println` prints nothing
  when the bars are hidden). It now falls back to `println!`. Without this fix, the summary
  did not appear in piped output.

## Tests

`src/parser/tests/sound/derived_assumptions.rs`: the 10 tests of §5, over six structurally
identical games `testdata/ssp-code/games/Derived1..6.ssp`. Each test writes its hop graph inline.
Mutation check: when every reduction is allowed, 4 tests fail (self cycle, two-cycle, chain
depths, proposition through an unestablished reduction).

## Deviations

- The tests are in one new file under `sound/` and not split across `theorems.rs` and
  `sound/theorems.rs`. One graph fixture serves all 10 tests.
- Spans are on the claim entries only. Reductions have no source span in the model, so a
  cycle prints its reductions as text: `cycle A -> B -> A via reduction g1 ~ g2 (B), reduction g3 ~ g4 (A)`.
- A third reason exists in addition to "no path" and "cycle": `the path needs the unestablished
  assumption X`. It is for a claim that depends on a failed claim without a cycle, and for a
  proposition.
- The summary prints when `prove` starts each theorem (after load, before SMT), and not inside
  the parser.
- Base assumptions are listed sorted by name.

## Result for simple-binding `Main`

The 17 entries under "Modular assumptions" in `theorem/Main.ssp` were marked `derived` in a
scratch copy (the line numbers moved since the story was written). The project was loaded with
`domino prove --theorem NoSuchTheorem`, which loads all theorems and skips all SMT work:

```
Main: proven relative to 13 base assumptions: CR_Mon_Assumption_DPRF, CR_Mon_Assumption_PRF, CR_Mon_Assumption_PRF_Check, KEM_Mon, PRF_Mon_Assumption_PRF_Check, PRF_Mon_Theorem_KSEarly_Assumption_DPRF, PRF_Mon_Theorem_KSEarly_Assumption_PRF, PRF_Mon_Theorem_KSLate_Assumption_DPRF, PRF_Mon_Theorem_KSLate_Assumption_PRF, Sample_HH_HD_DH, Sample_HH_HD_Mon, Sample_HH_HD_Mon_Assumption_DPRF_Ideal_Output_Given_Ideal_Left_Input, Swap_PRF_Mon; 17 derived assumptions established (max depth 4); modulo conjectures: none
```

The 13 base assumptions are exactly the "Monolithic primitives" block. The marks were not
committed to simple-binding-example; that needs the owner's approval.

## Quality gates

- `cargo clippy --workspace --all-targets`: no warnings.
- `cargo test --workspace`: all pass except `parser::tests::sound::packages::illegal_sample_type`.
  That test also fails on the baseline. Upstream commit `29e7e392` ("silence some errors",
  on `keks/ty-params`) commented out the sample-type check on purpose. To restore the check is
  the upstream author's decision, so it is not changed here.
- Complexity: the `sdlc` gate does not cover this Rust repo, and `lizard` cannot be installed
  here (no pip), so **CC is UNMEASURED**. Proxy: clippy `cognitive_complexity` for every
  changed function is ≤ 10 (`Proof::try_new` 10, unchanged except one parameter; `derive` 5;
  `establish` 3, `walk` 5, all others in `derivation.rs` ≤ 3; `handle_theorem` 6).
