# Story 47 `inv-guards-only-the-invariant` — implementation report

## What changed

- **`src/writers/easycrypt/invariant.rs`**
  - `build_invariant_file`: the guarded part of `op inv` is now the single application
    `Domino_invariant l r`. The old fold of every `define-state-relation` is removed.
  - New method `InvariantParserState::invariant_op`. It looks up the raw name `invariant` in the
    op registry and gives the mangled name only when that op is a `define-state-relation`. A
    `define-fun invariant` does not count. The mangled name is not hard-coded.
  - New error `InvariantError::MissingInvariant { equivalence, files }`. The message names the
    equivalence (`<left> ~ <right>`) and its invariant files, and says that the invariant must be
    a `define-state-relation` named `invariant`. This error also replaces the old `!abort => true`
    for an equivalence with no relations.
  - `state_relations` stays. It keeps the file order, and `invariant_op` reads it to tell a state
    relation from a `define-fun`. Its comment and the module comment are updated.
  - New tests: `inv_guards_only_the_invariant` (the exact `inv` text, and every relation op in
    file order) and `an_equivalence_without_an_invariant_relation_is_a_hard_error`.
- **`testdata/easycrypt/story42/params/theorem/`**
  - `invariant.smt2`, `invariant-trivial.smt2`, `invariant-different-packages.smt2`: each gets a
    `define-state-relation invariant` that is the conjunction of the file's relations.
  - New `ParamsNoInvariant.ssp` and `invariant-missing.smt2`: a theorem whose invariant file has
    a relation but no `invariant`. The new error test uses it.
- **`testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec`**: `inv` no longer lists
  the five relations. `Domino_invariant` is unchanged.
- **`docs/stories/easycrypt/00-overview.md`**: the **Invariants** row has an
  "**Amended by story 47:**" note.

## Verification

- Tests were written first. They failed (red): `MissingInvariant` did not exist. Then they
  passed (green). The story-06 golden test failed as expected until the golden file was updated.
- `cargo test --workspace`: 598 passed, 4 failed, 5 ignored. The 4 failures are timing tests in
  `easycrypt::session::tests`. They fail only under the load of the full parallel run. One of them
  also failed in the baseline before any change. `cargo test --lib easycrypt::session` alone
  passes 16 of 16, two times. All other tests pass.
- `cargo clippy --workspace --all-targets`: 0 warnings.
- `domino easycrypt export` of `example-projects/4WHS` (Full4WHS, Simple4WHS) and
  `example-projects/kem-dem/kem-dem-cca-ssp`: all succeed. `Eq_H2_1_H3_0_Invariants.ec` has one
  guarded conjunct and 10 `op Domino_relation…`. All 13 generated `Eq_*_Invariants.ec` files
  compile with `easycrypt compile`.
- **Not done**: `--features cvc5-lib`. The `cvc5-sys` build script needs `cmake`, and `cmake` is
  not installed on this machine.
- **Not done**: the tactics run on `kem-dem-cca-ssp`. `domino easycrypt prove` needs the
  `cvc5-lib` feature, which does not build here (see above). This acceptance criterion is open.

## Deviations and notes

- The story says to drop `state_relations` if nothing reads it. `invariant_op` reads it, so it
  stays. Rejected shape: a separate `invariant: Option<String>` field set in
  `handle_define_state_relation`. It duplicates what the registry and the list already hold.
- Implement-skill steps not done, because they apply only to the dotnet Sdlc repository: the
  `sdlc` index and CRAP gate, `/update-live-backlog`, the merge and push to main. `invariant_op`
  has CC 2. `build_invariant_file` loses one fold and gains one `ok_or_else`. The CRAP score is
  UNMEASURED.
- The flaky `easycrypt::session` timing tests are not fixed. They are outside this story's code,
  and the cause (timing under load) needs its own investigation.
- ADRs, earlier stories and earlier reports are not changed.

## State handed to the next story

- `op inv` is `params_inv l r /\ l.abort = r.abort /\ (!l.abort => Domino_invariant l r)` for
  every equivalence that translates.
- An equivalence without a `define-state-relation invariant` fails translation with
  `MissingInvariant`.
