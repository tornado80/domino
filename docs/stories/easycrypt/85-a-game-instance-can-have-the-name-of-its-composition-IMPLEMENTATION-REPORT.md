# Story 85 — Implementation report: a game instance can have the name of its composition

Rust only. The §7 questions use the recommended answers. No ADR.

## What changed

### The free theorem (`src/debug/side_run.rs`)

- `free_theorem` returns a theorem with only the two free instances `C` and `C$side`. It keeps
  the name, the constants (`free_params` adds to them), the packages and the assumptions. It
  drops the theorem's game instances, game hops and proofs. One-sided execution reads none of
  them.
- A theorem instance named `C` is not in the free theorem, so the names cannot clash.
  `free_theorem` cannot fail now: it returns `(Theorem, Equivalence)`, not a `Result`.
- The module documentation tells the new behaviour.
- The three transforms and `side_fingerprint` now process 2 instances, not all instances of the
  theorem.

### The error (`src/debug/driver.rs`)

- `DebugError::SideInstanceNameTaken` is deleted. No reference is left.

### The error prefix (`src/easycrypt/tactics/mod.rs`)

- New `JobKind::run_failed`: `lockstep execution failed` for a proofstep job,
  `one-sided execution failed` for a side-invariant job and a package-invariant job. `lockstep`
  uses it for an oracle without tactics.

### Other

- `src/debug/fold.rs`: the call has no `unwrap`; the comment that said "Full4WHS has no
  instance named `Hybrid2`" is replaced (it was not correct after the change).
- `src/easycrypt/tactics/tests.rs`: `cargo fmt` changed the format of two older hunks (no change
  of behaviour). `cargo fmt --check` is clean.
- New fixture `testdata/debug/se25-name-taken`: `se25` with instance `s` renamed to `S` and
  `equivalence S s2`.

## Tests

Ran, one filtered test at a time, `--test-threads=1` (cvc5 only, no EasyCrypt). All passed:

- `side_run::tests::a_theorem_instance_named_as_the_composition_does_not_clash` (new). Red
  before the change: `SideInstanceNameTaken { name: "S", theorem: "T" }`. Green after: root is a
  `Split` on `n > 0`, four terminals, claims `[game-invariant!main!S!]`.
- `side_run::tests::the_free_theorem_holds_only_the_free_instances` (new). Red before (the
  theorem's instances were in the copy).
- `side_run::tests::the_side_inputs_do_not_depend_on_the_theorem_instances` (new): the claim
  names, the base frame and the fingerprint of `se25` and `se25-name-taken` are equal.
- Before and after the change, a temporary test wrote the claim names, the base frame and the
  fingerprint of `se25` to a file. The two files are byte-identical (`cmp`). The temporary test
  is deleted.
- `tactics::tests::a_failed_run_names_the_execution_of_its_job` (new, no EasyCrypt).
- Old tests, still green: `a_side_run_checks_the_composition_claims_and_fails_only_the_breaking_path`,
  `the_theorem_index_lists_the_side_runs_and_links_their_index`,
  `a_path_that_breaks_one_named_invariant_fails_only_its_check`,
  `fold::tests::a_side_tree_with_free_parameters_folds_only_literal_conditions` (it reads
  `example-projects/4WHS` and makes the EasyCrypt listing of `Hybrid2.Send2`; it does not start
  EasyCrypt; 2.7 s).

Written, not run: none. The §3.2 prefix test is a unit test of `JobKind::run_failed` and needs
no EasyCrypt. No test sends a failed one-sided run through `lockstep` (that needs an EasyCrypt
session).

Also:

- `cargo build --workspace`: clean.
- `cargo clippy --workspace --all-targets`: clean.
- `cargo test --no-run`: compiles.
- `--features cvc5-lib`: NOT RUN. `cmake` is not on PATH (environment gap).
- Full `cargo test --workspace`: not run (owner's rule).

## Complexity gate

`sdlc code index .` ran (1029 symbols). `sdlc crap . --since-ref fae950ec --threshold 15`
failed: "does not resolve to a commit ... (not a git repo, or an unknown ref)" (sdlc sandbox,
as in stories 82–84). **CRAP: UNMEASURED.** The CC numbers are a decision-point count.

| symbol | file | CC | CRAP |
|---|---|---|---|
| `free_theorem` | debug/side_run.rs | 2 (was 3) | UNMEASURED |
| `side_fingerprint`, `run_side_command` | debug/side_run.rs | unchanged (`?` removed) | UNMEASURED |
| `JobKind::run_failed` (new) | easycrypt/tactics/mod.rs | 2 | UNMEASURED |
| `lockstep` | easycrypt/tactics/mod.rs | unchanged (one string changed) | UNMEASURED |
| new tests and `side_inputs` | side_run.rs, tests.rs | 1 | UNMEASURED |

No touched function has CC ≥ 15.

## Code review

Fixed point `fae950ec`. Deterministic scan: UNMEASURED (the same sandbox failure to resolve
the ref). Complexity: UNMEASURED (see above). Spec and Standards (sub-agent):

- Spec: no missing work, no wrong behaviour. `load_invariants` reads only the left and right
  instances, so the dropped game hops are not needed. The before/after point is met by the
  `cmp` above.
- Fixed: one line of the module documentation was longer than 100 columns.
- Not changed (judgement calls): the name `run_failed`; `side_inputs` returns a 3-tuple; the
  `cargo fmt` hunks in `tests.rs` stay in this commit, as the formatter requires them.

## Not done

- The owner's check on `4WHS` / `ec4whs` with `instance H4 = H4 { … }` (owner's rule: it runs
  EasyCrypt).
- `--features cvc5-lib` build and test (no `cmake`).
- CRAP gate and deterministic scan: UNMEASURED, not a pass.
- The owner decides if `H4_b`/`H5_b` in `Full4WHS` go back to `H4`/`H5` (§7 question 6).
