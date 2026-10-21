# Story 87 — Implementation report: the EasyCrypt `invariant` check assumes `no-abort`

Rust only. The §7 questions use the recommended answers: `no-abort` (not the literal `inv`
shape), `same-output` unchanged, and `ClaimSet::NoDependencies` is renamed `ClaimSet::EasyCrypt`.
No ADR.

## What changed

### `invariant` gets `no-abort` (`src/debug/lockstep_run.rs`, `src/debug/claims.rs`)

- `easycrypt_invariant_query` builds the `invariant` claim with the one built-in dependency
  `no-abort` (`ClaimKind::BuiltIn(BuiltInFact::NoAbort)`) and makes the query with
  `ClaimQuery::of`. The parts stay the state relations but `invariant`, named by
  `state_relation_op_name`. `check_claim` does the rest: on a pair where a side aborts, the
  verdict is `unreachable (dependency-false: no-abort)`, and the parts are not checked.
- `ClaimSet::NoDependencies` is now `ClaimSet::EasyCrypt`, with the new documentation of §3.1.
  No `NoDependencies` is left in `src/`.
- `ClaimSet::resolve` gives the infos of the EasyCrypt set the dependencies of each query, so
  `trace.json` and the pages show `invariant` with `["no-abort"]` and `equal-output` with `[]`.
- The module documentation of `lockstep_run.rs` and the comment of `easycrypt_queries` are
  updated.

### The tactics drop the workaround (`src/easycrypt/tactics/driver.rs`)

- `pair_view` no longer turns an `invariant` failure on an aborting pair into `Inconclusive`.
  The branch, its doc sentence and the helper `pair_aborts` (no caller was left) are removed.
  An `Unreachable` verdict maps to `DominoView::Verified` through `view_of_verdict`.

### The fingerprint sees the dependency (`src/debug/lockstep_fingerprint.rs`)

- `easycrypt_check_names` is replaced by `easycrypt_checks(eqctx, oracle)`. It makes one line
  for each check from the real queries: `equal-output []`, `invariant [no-abort]`, then the part
  names. The `claims` part hashes these lines. Every saved EasyCrypt joint tree is stale once,
  with the warning "the claims checked".
- The pinned hash of `the_fingerprint_is_stable_and_ignores_where_code_stands` changes from
  `e81558bf…` to `32c75f1e…`. This is the intended effect of §3.3.

### Story 23 report

- The section "Invariant vs abort (open difference, `prove` untouched)" has the line "Closed
  by story 87".

## Tests

Ran, filtered, `--test-threads=1`, with `MemoryMax=6G`, on small fixtures only
(`testdata/lockstep/rules`, `testdata/story19/deps`, `test-projects/test-oracle-rename`) and
scripted EasyCrypt sessions. All passed:

- `lockstep_run::tests::the_invariant_is_not_asked_of_a_pair_that_aborts` (renamed from
  `the_invariant_is_checked_on_the_state_at_the_abort`): `[(false, false, 0, 2), (true, true, 0, 1)]`,
  the reason `DependencyFalse { dependency: "no-abort" }` on the second pair, and no part
  verdicts on it.
- `lockstep_run::tests::the_invariant_is_unreachable_where_exactly_one_side_aborts` (new,
  `AbortDiff`): `equal-output` rank 2, `invariant` unreachable by `no-abort`.
- `lockstep_run::tests::the_invariant_is_unreachable_where_both_sides_abort` (new, `AbortBoth`).
- `lockstep_run::tests::the_easycrypt_listing_checks_invariant_under_no_abort_with_plain_names`
  (was `…keeps_its_two_dependency_free_claims_and_plain_names`): the dependencies are `[]` and
  `["no-abort"]`, `trace.json` has `"dependencies":["no-abort"]`, and the goal view of
  `invariant` has one dependency assertion.
- `lockstep_run::tests::a_joint_path_smt_file_reproduces_the_recorded_verdicts`: an
  `Unreachable (dependency-false)` verdict now replays as `unsat` (the file asserts the false
  `no-abort` before the goal).
- `lockstep_fingerprint::tests::the_claims_part_hashes_each_check_with_its_dependencies` (new):
  the `claims` part differs from the hash of the names alone, and a tree saved with the names
  alone is stale in `claims` only, described as "the claims checked".
- `tactics::tests::an_aborting_pair_with_an_unreachable_invariant_is_domino_verified` (was
  `an_invariant_failure_where_a_side_aborts_is_not_held_against_easycrypt`), and
  `a_one_sided_invariant_part_has_the_view_of_its_own_part_verdict` (an aborting failure now
  reads `fails`).
- Red check: not run on the old code as a separate step. The expected values contradict the
  old behaviour, which the old tests pinned (rank 2 on the aborting pair, no dependencies, the
  names-only `claims` hash). The pinned fingerprint hash did fail before it was updated.
- Regression: `cargo test --features cvc5-lib --lib debug::` (236 passed, 3 ignored for 4WHS),
  `easycrypt::tactics::` (153 passed), `easycrypt::transcript` (13 passed). The `Obligations`
  and `Core` claim sets and the side-tree claims are unchanged, and their tests stay green.
- `cargo clippy --workspace --all-targets` (with and without `cvc5-lib`): clean.
  `cargo fmt --check`: clean.

Written, not run: none.

## Complexity

`sdlc code index .` and `sdlc crap . --since-ref f44337f6 --threshold 15` failed in the bwrap
sandbox (`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`), as for the earlier
stories. **CRAP: UNMEASURED.** CC of each symbol edited or added (decision points counted by
hand):

| Symbol | CC |
|---|---|
| `lockstep_run::easycrypt_invariant_query` | 1 |
| `lockstep_run::easycrypt_checks` (new) | 1 |
| `lockstep_run::easycrypt_queries` (doc only) | 1 |
| `claims::ClaimSet::resolve` | 4 |
| `claims::ClaimSet::only` | 2 |
| `lockstep_fingerprint::Fingerprint::of` | 4 |
| `tactics::driver::pair_view` | 8 (was 10) |

All are below 15.

## Owner's checks (deferred to the lead's 4WHS run)

- `domino-ec easycrypt debug --theorem Full4WHS --out autogenerated --proofstep 8 --oracle NewSession`
  in `ec4whs`. Expected: no `debug_not_verified`, and J2 reads `invariant: unreachable
  (dependency-false: no-abort)`.
- `domino-ec easycrypt debug --theorem Full4WHS --out autogenerated` over all proofsteps.
  Expected: no failure that is not also a failure of `domino debug --lockstep --claim-set core`
  on the same pair.

## Deviations from the spec

- §3.3: the `claims` lines come from the real queries (`easycrypt_checks`), not from a fixed
  list of names with a second list of dependencies. Thus the fingerprint follows the claims the
  run checks with no second source of truth. The line format is `invariant [no-abort]`, and
  `equal-output []`.
- The story 23 report still names the old test in its text; only the "closed" line is added.
