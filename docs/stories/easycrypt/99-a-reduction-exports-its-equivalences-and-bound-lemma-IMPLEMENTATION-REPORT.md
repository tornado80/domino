# Story 99 — Implementation report: a reduction exports its equivalences and its bound lemma

Branch `amir/easycrypt-export`. The implementation is in commit `06989b65`, and the review fixes are in `58506cb3`. ADR 0022 (decisions 4–6).

## What was built

### `src/writers/easycrypt/reduction_lemmas.rs` (new)

`build_reduction_file` calls `reduction_lemmas(theorem, interfaces, red, &LemmaInput, &mut items)`. After the modules of story 98, it adds the following to `Red_<hop>.ec`:

- **Invariant op(s)** `inv_<hop>`, or `inv_<hop>_L`/`_R`. The arguments are values: the three abort flags, one pair for each constant that `B` stores (C3), and one `glob` pair for each package pair (C4). C4 covers reduction packages against their router clone, then mapped packages against the assumption game's partner. Each `glob` names the unapplied clone. The body is C1 /\ C2 /\ the equalities.
- **A section** with `declare module A <: Interfaces.Adv_<G> {..}`. It excludes the following, without duplicates:
  - every `Game_` and every `Cloned_Pkg_` of the four compositions;
  - `Red_<hop>` and `B_<hop>`;
  - the router clones.
- **Oracle lemmas** `<hop>[_L|_R]_<proc>`, one for each export of the router's interface, in `comp.exports` order. Each states `equiv[Game_<G>.<o> ~ Red_<hop>(Game_<Assm>).<o> : ={arg} /\ INV ==> ={res} /\ INV]`. The two sides **share** them when their whole `SideSpec` is equal: games, invariant arguments, exclusion list and MEQ.
- **Two reduction equivalences** `<hop>_equiv_L`/`_R`, proved by `byequiv`, `proc; inline *; wp`, `call (: INV)`, one `+ by conseq <oracle lemma> => /#` for each oracle, and `by auto => /#`.
- **The bound lemma** `<hop>_bound`, stated as an equality of absolute differences in the hop's direction (side 0 of the map first) and proved by rewriting with both equivalences.
- **Lemma binders:** all three lemmas take `&m` and then every theorem constant that any `run` reads, in theorem order. The `run`s counted are the two game experiments, B's stored constants, and the two assumption argument lists.

`ReductionFile.lemmas: ReductionLemmas { equivs, bound, consts }`.

### Other changes

- `ast.rs`/`render.rs`: two new expression forms, `EcExpr::GlobAt { module, mem }` (renders as `(glob M){i}`) and `EcExpr::Abs` (renders as `` `|e| ``).
- `reduction.rs`: `StoredConst` is now a struct and also records the theorem constant. There is a new test that a reduction inside a hybrid hop is not translated, which addresses a story 98 review note.
- `export.rs`: `ReductionReport` gains `equiv_lemmas: [String; 2]`, `bound_lemma` and `lemma_consts`. `assert_tree_compiles` now asserts that no `Red_*.ec` contains `admit`. The 4WHS test asserts the presence of `Hybrid2_Hybrid3_bound` and the absence of `admit`.
- `crates/domino/src/main.rs`: the report line is now `reduction Red_..ec (assumption X, bound lemma <hop>_bound)`.
- `docs/easycrypt-export.md` now describes the lemmas.

## Deviations from story 97's script (found on kem-dem's 2nd reduction, never hand-proved)

1. **`try (elim* => *)` after each `sp`.** Once reduction code writes a state that the invariant reads (`KEM.c` before the mapped `Key.d_SET`), `sp` leaves the invariant under an `exists`. `smt` cannot carry that over a call. `elim*` turns the existentials into logical variables.
2. **A mapped call whose `sim` fails gets its body walked.** `DEM.d_ENC` reads `c_` on a path where `c_` was never written, so `sim` gives up. The rung closer is now: `(call (: MEQ); [by sim | by auto => /#]) || (call (: MEQ); [by inline *; <walk with if and sampling rungs>; auto => /# | by auto => /#]) || (auto => /#)`.
3. **The ladder has 8 rungs** (`ec_fwd6` … `ec_fwd`).

An observation from debugging: a failing `smt` inside a rung's `first by` is not caught by the surrounding `||`. When every alternative of a rung fails, the error stops the whole proof. It does not just end the `do ?`.

Loops: `easycryptify` unrolls or rejects every `for` loop, so no `while` reaches a reduction file. No loop check was needed.

## Tests

Unit tests in `reduction.rs`, all green with `cargo test --lib writers::easycrypt::reduction -- --test-threads=1` (10 tests):

- `hello_world_lemma_statements_are_the_prototypes`: the statements are the same as the prototype's after whitespace normalization, and there is no `admit`.
- `hello_world_has_an_invariant_for_each_side`
- `the_first_kem_dem_reduction_shares_its_oracle_lemmas`
- `reduction_consts_quantifies_the_constant_and_relates_the_stored_copy`
- `the_third_kem_dem_bound_lemma_follows_the_hop_direction`
- `a_reduction_inside_a_hybrid_hop_is_not_translated`

Live compile tests, with EasyCrypt r2026.09 on PATH under `systemd-run --user --scope -p MemoryMax=6G timeout 1800`, all green:

- `hello_world_full_tree_compiles`
- `kem_dem_cca_ssp_full_tree_compiles_in_dependency_order`: all three `Red_*.ec`, about 20 s each.
- `reduction_consts_full_tree_compiles`
- `reduction_prototypes_compile`
- `reductions_are_reported_in_hop_order_and_not_skipped`

Broader run, `cargo test --lib writers::easycrypt -- --skip 4whs --skip 4WHS --test-threads=1` with EasyCrypt removed from PATH (so the live tests skip): 331 passed. `cargo clippy --workspace --all-targets` is clean.

**Not run (owner's rule against big projects):** `simple_4whs_reports_the_reduction_hop_and_the_composition_names`. It translates 4WHS, and its new assertions are written but have not been run. Command: `cargo test --lib simple_4whs_reports -- --test-threads=1`. Whether `Red_Hybrid2_Hybrid3.ec` compiles in EasyCrypt is unchecked.

**Not done:** the CRAP gate and `crap_scope`. `reduction_lemmas()` is still long, roughly 150 lines; the restrictions were pulled out into their own function.

## Review findings left open

- `SideSpec`/`push_pair` use tuples, and the side is a `usize` index rather than a `Side` enum.
- `reduction_lemmas()` could be split further.
- `tactic` and `bullet` duplicate `pkginv.rs`.
- Some `expect`s rely on parser invariants, as story 98 noted. C3 is now an `expect` rather than a silently dropped conjunct.

## For story 100

- Lemma names: `<hop>_equiv_L`, `<hop>_equiv_R` and `<hop>_bound`, with `<hop>` = `<L>_<R>`. Read them from `ReductionReport.{equiv_lemmas, bound_lemma}`.
- Shape: `lemma <hop>_bound &m (<c> : <ty>) ... : `|Pr[Comp_<GL>.Exp_<GL>(A).run(..) @ &m : res] - Pr[Comp_<GR>.Exp_<GR>(A).run(..) @ &m : res]| = `|Pr[RedExp..(A).run(..) @ &m : res] - Pr[RedExp..(A).run(..) @ &m : res]|`.
  - The binders are `ReductionReport.lemma_consts` (theorem constant names, in theorem order), each mangled with `NameKind::Var`. They are the same for all three lemmas.
  - The lemmas sit inside the section of `Red_<hop>.ec`, over that file's own `declare module A`, so a user outside the file applies them to a concrete or declared `A` that meets the same restrictions.
- Every entry in `ExportedTheorem.reductions` carries a complete proof (no `admit`). A reduction that cannot be proved fails EasyCrypt, which is a translation bug, and is not reported as partial. A reduction inside a hybrid hop has no entry and appears in `skipped`.
