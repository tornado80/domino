# Story 70 — Implementation report: a table write with an unknown value is a branch

Rust only. **The exported `.ec` files change.** ADR 0015 is implemented.

## What changed

### Translation (`src/transforms/easycryptify.rs`)

- New `branch_table_write`: in `UnwrapGuards::block`, a write `T[k] <- e` whose value is not
  `Some(_)` or `None` becomes `T[k] <- Some(Unwrap(e))` when a fact covers `e`, else
  `if (not (e == None)) { T[k] <- Some(Unwrap(e)) } else { T[k] <- None }` (the write's span,
  condition from `is_some`). It is applied in the general arm and in the unwrap arm (a
  `T[k] <- Unwrap(m)` after story 17 inlines a temporary). The write then kills the facts
  that read `T`, as before.
- New `none_test`: `if (e == None)` gives the fact `e` in its else-branch (`with_fact`).
  `some_test` now delegates to it. `every_unwrap_is_guarded` accepts an `Unwrap(e)` in the
  else-branch of `if (e == None)` (`walk_guarded`).

### Writer (`src/writers/easycrypt/package.rs`)

- `translate_table_write`'s general arm is `unreachable!(... (story 70))`. `EcExpr::If` stays
  (`invariant.rs` uses it).

### Hints (`src/easycrypt/tactics/driver.rs`)

- `BASE_SMT_LEMMAS = ["get_setE", "mem_set", "remE", "mem_rem", "emptyE"]`. The tactics tests
  that spell the sentence are updated.

### Exported files

- `NewKey` (KX, KX_nochecks, KX_nokey, PRF): `d_LTK.[kid_] <- oget ltk;`.
- `NewSession` (KX, KX_nochecks, KX_nokey):
  `if (!(d_H.[kid] = None)) { d_Fresh.[ctr_] <- oget d_H.[kid]; } else { d_Fresh <- rem d_Fresh ctr_; }`.
- Goldens: `testdata/easycrypt/story03/4WHS/Pkg_{KX,KX_NoKeys,PRF}.ec` regenerated;
  `testdata/easycrypt/story04/4WHS/Pkg_*.ec` (compile fixtures) edited to the same lines.

## Tests

- New unit tests in `easycryptify`: `a_table_write_with_an_unknown_value_is_a_branch`,
  `a_table_write_with_a_known_value_is_a_plain_write` (then-branch, after `assert`, else of
  `if (x == None)`), `a_write_after_the_guard_keeps_the_table_write_branch`,
  `a_none_test_covers_unwraps_in_its_else_branch`,
  `some_none_and_sampled_table_writes_do_not_change` (`Some`/`None`; a sample has an
  `AssignmentRhs::Sample`, which `branch_table_write` does not match).
- `cargo test --lib -- writers::easycrypt transforms debug::easycryptify`: 372 passed (includes
  the differential test and the EasyCrypt compile tests of the Full4WHS tree).
- `cargo test --lib` (full): 754 passed, 0 failed, 6 ignored; `cargo clippy --workspace`: clean;
  `cargo build --release --workspace`: ok. `--features cvc5-lib` cannot build here (no cmake).

## §5 numbers

1. Conditional table writes in the Full4WHS export: before 7, after 0 (`grep -c 'then rem'`).
   4 became a plain write (`NewKey`), 3 a branch (`NewSession`).
2. Terminals and lockstep classification: **not measured**. `domino easycrypt debug` needs
   `cvc5-lib`, which cannot build here.
3. Tactics runs: **not run** (the owner asked for no EasyCrypt proofs on Full4WHS in this session).
4. Admitted parts with `rem`: **not measured** (needs item 3). Story 66 must still wait.

`domino easycrypt check-alignment --theorem Full4WHS` (EasyCrypt domino-json/3 from
`easycrypt/_build`): 108 oracles checked, 0 mismatches.

## Complexity

`gate_cognitive_complexity` reports NotApplicable (it does not score Rust): UNMEASURED by the
tool. By hand: `branch_table_write` CC 4, `none_test` 2, `with_fact` 3, `walk_guarded` 2;
`UnwrapGuards::block` lost one nested `if` (the then-fact code moved to `with_fact`).
