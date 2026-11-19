# Bug corpus of unsound reductions

Asset of the ticket "Bug corpus of unsound reductions". Each item is a small Domino project.
The verdicts are from `domino proofsteps` (this runs the reduction check) on commit `7bf2632b`
(branch `amir/lean-verification`), debug build, on 2026-11-01.

The projects are here and not in `test-projects/`, because CI (`scripts/test-known-examples.sh`)
runs every project in `test-projects/`. These projects must move there together with the fixes.

## Words

- **Construction games** `C_L`, `C_R`: the two games of the reduction hop.
- **Assumption games** `A_L`, `A_R`: the two games of the assumption.
- **Mapping** `m_L`, `m_R`: the `map` blocks. Each one maps every package instance of the assumption
  game to a package instance of the construction game.
- **Mapped part**: the image of the mapping in a construction game.
- **Context** (also "reduction part", `R`): the package instances of a construction game that are
  not in the mapped part. PR #2 of `grittygrease/domino` uses the word "context".
- **Cross edge**: an edge from the context into the mapped part.

## Verdicts

"Unsound" means that the check accepts a hop, but no single context `R` gives
`C_L = R ∘ A_L` and `C_R = R ∘ A_R`. The PR #2 cases also give a semantic counterexample: the
assumption relates a game to itself (so it is true), but the construction games return different
values for one query.

| Item | Source | Defect class | Verdict now | Correct verdict |
|---|---|---|---|---|
| `test-projects/err-reduction-export-into-assumption` | PR #442 (domino-lang) | E3 | reject | reject |
| [pr2/err-reduction-context-oracle](pr2/err-reduction-context-oracle) | PR #2 case 1 | X1 | **accept (unsound)** | reject |
| [probes/err-context-enters-different-assumption-instance](probes/err-context-enters-different-assumption-instance) | probe, this ticket | X2 | **accept (unsound)** | reject |
| [pr2/err-reduction-context-instances](pr2/err-reduction-context-instances) | PR #2 case 2 | R1 | **accept (unsound)** | reject |
| [pr2/err-reduction-mapped-wiring](pr2/err-reduction-mapped-wiring) | PR #2 case 3 | M2 | **accept (unsound)** | reject |
| [user/err-mapped-destination-oracle](user/err-mapped-destination-oracle) | user (`Soundness.ssp`) | M2 | **accept (unsound)** | reject |
| [pr2/err-reduction-exports](pr2/err-reduction-exports) | PR #2 case 4 | E1 | **accept (unsound)** | reject |
| [pr2/err-repeated-import-across-blocks](pr2/err-repeated-import-across-blocks) | PR #2 case 5 | W1 | **accept (unsound)** | reject |
| [probes/crash-left-only-export](probes/crash-left-only-export) | probe, this ticket | E1 | panic `reduction.rs:342` | reject with error |
| [probes/crash-mapped-edge-into-context](probes/crash-mapped-edge-into-context) | probe, this ticket | M1 | panic `reduction.rs:893` | reject with error |
| [user/crash-mapped-edge-to-other-instance](user/crash-mapped-edge-to-other-instance) | user (`Panic.ssp`) | M2 | panic `reduction.rs:928` (`assumption wires 1`) | reject with error |
| [pr2/test-reduction-context-oracle](pr2/test-reduction-context-oracle) | PR #2 control 1 | X1 | accept | accept |
| [pr2/test-reduction-context-instances](pr2/test-reduction-context-instances) | PR #2 control 2 | R1 | accept | accept |
| [pr2/test-reduction-mapped-wiring](pr2/test-reduction-mapped-wiring) | PR #2 control 3 | M2 | accept | accept |
| [pr2/test-reduction-exports](pr2/test-reduction-exports) | PR #2 control 4 | E1 | accept | accept |
| [pr2/test-repeated-import-across-blocks](pr2/test-repeated-import-across-blocks) | PR #2 control 5 | W1 | accept | accept |
| [pr2/test-reduction-context-export-alias](pr2/test-reduction-context-export-alias) | PR #2 extra control | X2 | accept | accept |

The probes for "separate stores vs one shared store" (R1), "swapped imports in the mapped part" (M2)
and "export only on the right" (E1) were also made in a PRF/Enc setting. They are not kept, because
they are duplicates of the PR #2 cases. The PR #2 cases are smaller and also semantic
counterexamples.

The user's original project `test-projects/test-new-reduction-soundness-test-project` contains both
`user/*` items in one project. It is still in `test-projects/` and is not tracked by git. It makes CI
fail ("expected success"), because `Panic.ssp` panics.

## Suspects that are not bugs

- `zip` over the unmapped package instances of the assumption games (`handle_reduction_body`): this is
  dead code. `handle_mapspec_assumption` rejects a mapping that does not map every assumption package
  instance, so both lists are always empty.
- The two `panic!()` calls for "both mappings use the same assumption game" or "the same construction
  game": with the probe that I made, the package comparison rejects the mapping first. These panics are
  crashes, not acceptances.
- `debug_assert!` on oracle signatures of cross edges: a release build does not do this check. But the
  destination packages and parameters must be equal, so the signatures are also equal. This is not a
  defect, but the theorem must not depend on the assertion.

## Not examined

- The hybrid path (`is_hybrid`, construction names `inst$bit$`, redaction of loop variables in
  `package_instances_diff`).
- Recursion of `compare_reduction` on a composition with a cycle. This is not possible if compositions
  must be acyclic. The theorem must state whether that is a hypothesis.
- PR #2's fixed branch against this corpus. I did not build or run the external code (the session's
  permission policy blocked it). It is not known if the PR's fix 1 also rejects
  `probes/err-context-enters-different-assumption-instance`.

## Obligations that the corpus shows

Each defect class is a condition that the soundness theorem must contain. If the check passes, then
there exists a context `R` so that `C_L ≅ R ∘ A_L` through `m_L` and `C_R ≅ R ∘ A_R` through
`m_R`. The isomorphism `≅` keeps packages, parameters, edges (with import name and destination oracle
name) and exports (with export name and signature). These conditions are what the existential
statement means for the graph:

- **W1, well-formed composition (hypothesis).** Each import of each package instance has exactly one
  edge. A second `compose` block must not wire the same import again. Today, the reduction check uses the
  first edge and oracle resolution uses the last edge.
- **M1, the mapped part is closed downwards.** No edge goes from the mapped part into the context.
- **M2, the mapped part is the assumption game.** For every edge of `A`, the image under `m` has the same
  edge with the same import name and the same destination oracle name, and there are no other edges.
  Endpoints and types are not enough.
- **R1, one context.** There is a bijection between the context instances of `C_L` and of `C_R`. It
  keeps package and parameters. Pairs of instances are not enough: sharing of state must be the same.
- **X1, context edges keep the destination oracle.** Each pair of corresponding context edges has the
  same import and the same destination oracle name.
- **X2, cross edges enter the same assumption export.** A cross edge on the left and its partner on the
  right must enter the same export of the assumption interface. That is the same export name, so the same
  assumption instance. The internal oracle names of the real and ideal packages may differ (see the alias
  control).
- **E1, the same adversary interface.** `C_L` and `C_R` have the same set of export names with matching
  signatures. Each export goes either to corresponding context instances, or into the mapped part.
- **E2, cross edges use only the assumption interface.** A cross edge must go to an oracle that the
  assumption game exports (the existing check).
- **E3, direct exports from the mapped part.** An export of the construction game into the mapped part
  must be an export of the assumption game (PR #442).

Hypotheses that the corpus does not show, but the theorem must state: `A_L` and `A_R` have the same
export interface, and game instantiation (resolved parameters) is a trusted input.
