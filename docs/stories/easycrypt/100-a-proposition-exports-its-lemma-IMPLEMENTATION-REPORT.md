# Story 100 — Implementation report: a proposition exports its lemma

Branch `amir/easycrypt-export`. The implementation is in commit `9e9b7d47`, and the review fixes are in `cbc3f7ce`. ADR 0022 (decisions 6–8).

## What was built

### `src/writers/easycrypt/proposition.rs` (new)

`compute_proposition_files(theorem, interfaces, equivalence_files, reduction_files)` returns one `PropositionOutcome` for each `theorem.proofs` entry. The outcome is either `File(PropositionFile)` or `Skipped(SkippedProposition)`.

- **Hybrid hop on the path:** the proposition gets no file. It is `Skipped`, with the hop's game instances and the reason `hybrid game hops are not translated`.
- **Otherwise:** the proposition gets `Prop_<Name>.ec`:
  - It does `require` (without import) of `Interfaces` and every `Eq_*`/`Red_*`/`Comp_*` theory that it names.
  - It has a section with `declare module A <: <first lemma file's adversary type> { union of the restrictions }`. A file's own modules are qualified with that file's theory. Any name that does not start with `Comp_` counts as file-local.
  - It has one lemma, `` <Name> &m (<free consts>) : `|Pr[Exp_<first>] - Pr[Exp_<last>]| <= terms ``.
- **Reduction step:** the term is the right side of its bound lemma, taken from the `Red_*` file's AST. Binders are replaced by the step's values, and `RedExp_*` is qualified. The term stays in the hop's direction.
- **Equivalence step:** gives no term.
- **Open hop** (a conjecture, or an equivalence without a file): the term is `` `|Pr[Exp_a] - Pr[Exp_b]| `` over the two neighbouring path instances, in path order.
- **No term at all:** the right side is `0%r`.
- **Step values:** each lemma binder (a theorem constant) gets the literal that the step's specializations fix, through `proof::assignments` against the hop's generic instances.
  - If the step does not fix the constant, the value is the proposition lemma's own binder, and the constant becomes one of the lemma's binders, in theorem order.
  - The path neighbour's name decides the direction. When neither neighbour has a hop-side name (the ends of the path are theorem instances with their own names), `game_is_compatible` decides.
- **Proof:** one `have hN := <Theory>.<lemma> A &m <args>.` for each equivalence and bound lemma, then `smt().`. There is no `admit`.

### Other changes

- `export.rs`:
  - `ExportedTheorem` gains `propositions: Vec<PropositionReport>` (name, file, `reduction_terms`, `open_hops`) and `skipped_propositions`.
  - `assert_tree_compiles` compiles every `Prop_*.ec` last and asserts that none contains `admit`.
- `crates/domino/src/main.rs`:
  - `proposition Prop_Main.ec (Main, 3 reduction terms[, open conjecture hop a ~ b])`.
  - `proposition main skipped (hybrid hop h$false$ ~ h$true$): hybrid game hops are not translated`.
- `reduction.rs`: `push_unique` is now `pub(super)`, shared with `proposition.rs`.
- `docs/easycrypt-export.md`: a new section, "Translating propositions".
- Epic §5 boxes are ticked.
- New fixture `testdata/easycrypt/proposition-open-hop/`:
  - It has `small`/`medium`/`other_small` (SmallComposition with `n: m`), the equivalence `medium ~ small` and the conjecture `small ~ other_small`.
  - Its propositions are `Main: medium ~ other_small` (one open hop) and `EqOnly: small ~ medium` (the equivalence used in reverse, right side `0%r`).

## Deviations

1. **`have` instead of `rewrite` for equivalences.** The story's proof rewrites with the equivalence lemmas. A `rewrite` only works when the lemma's left side occurs in the goal, and an equivalence in the middle of a path does not occur there. Every lemma is therefore a `have`, and `smt()` uses each one in either direction, so no symmetric form is written. This compiles on kem-dem and on the fixture.
2. **The fixture's conjecture term is trivially 0.** Two instances of `SmallComposition` that differ only in a type-level parameter export to the same `Exp_SmallComposition` (an existing limitation of the exporter). The term still has the shape the story asks for. Two compositions with different exports cannot be used, because one adversary type must cover the whole path.
3. **The skipped proposition goes in its own list.** It is in `ExportedTheorem.skipped_propositions`, not in `skipped`, because `SkipNote` has no proposition name.

## Tests

Unit tests (`cargo test --lib proposition -- --test-threads=1`, 7 tests, green, run with EasyCrypt on PATH):
- `kem_dem_main_has_three_reduction_terms_in_path_order` (the third term is in its hop's direction)
- `kem_dem_main_uses_the_equivalence_lemma_with_false_and_true`
- `kem_dem_main_takes_no_constant`
- `a_conjecture_is_an_open_hop_with_its_own_term`
- `a_path_of_equivalences_only_is_bounded_by_zero`
- `a_path_with_a_hybrid_hop_is_skipped`
- `proposition_open_hop_full_tree_compiles` (live)

Live compile: `kem_dem_cca_ssp_full_tree_compiles_in_dependency_order` is green, about 80 s. It compiles `Prop_Main.ec` with no `admit`.

Broader run: `cargo test --lib writers::easycrypt -- --skip 4whs --skip 4WHS --test-threads=1`, without EasyCrypt on PATH, passed 338 tests. `cargo clippy --workspace --all-targets` is clean. All runs were under `systemd-run --user --scope -p MemoryMax=6G timeout 1800`.

**Not run (owner's rule against big projects):**
- `simple_4whs_reports_the_reduction_hop_and_the_composition_names` now asserts that `Prop_KXSecurity.ec` exists with `lemma KXSecurity &m` and no `admit`. Command: `cargo test --lib simple_4whs_reports -- --test-threads=1`.
- The 4WHS compile is not checked.
- `crates/domino` CLI tests were not run.

**Not done:** the CRAP gate and `crap_scope`.

## Review findings left open

- No test has a free constant: none of the small fixtures has a proposition that leaves a `run`-read constant unfixed. The binder path is written but unexercised.
- `const_binders` mangles the theorem constants again, as the other writers do, instead of reading their binders. The equivalence lemma name is also re-derived (mangled `<L>_<R>_equiv`, the rule in `proof.rs`). If the rules diverge, `section_lemma` panics.
- `qualify` relies on the `Comp_` prefix. `OpenHop.kind` and `reason` are `&'static str`, not enums. The tactic-line helper is duplicated a fourth time.
- The adversary type comes from the first file, and nothing checks it against the other files.
- A missing reduction file is an `expect`, not an `EcExportError`.
