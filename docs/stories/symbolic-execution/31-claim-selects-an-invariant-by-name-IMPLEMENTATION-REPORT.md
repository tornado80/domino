# Story 31 — Implementation report: `--claim` selects an invariant by name

With `domino prove --package P` or `--game C`, `--claim <pattern>` is a wildcard on the declared
names of the owner's invariants (`--claim main`, `--claim 'ma*'`). The full claim name
(`package-invariant!<name>!<P>!`) is not part of the interface. `--package` refuses
`--injective-randmap`. Plain `domino prove` and `--proof/--proofstep` do not change.

## What changed

### One owner of the selection (`src/invariant_claim.rs`, new)

- `select(claims, pattern, owner)`: the claims whose declared name matches the wildcard, in
  their order. With no pattern, all claims. A pattern that is not a valid wildcard matches
  nothing.
- `NoInvariantMatches`: "no invariant of `<owner>` matches `<pattern>`", with the help
  "the invariants of `<owner>` are: main, bad". Both drivers call `select` at the start of
  `verify`, before any solver work. Thus a run that checks zero claims cannot say "verified".
- The declared name is the part between the first two `!` of the claim name. The format of
  the claim name stays in `package_invariant_claim_name` / `game_invariant_claim_name`.

### The drivers

- `PackageInvariantSmtDriver` has a new `req_claim`. `verify` selects the claims one time and
  gives them to `verify_claim_group` (each oracle and the start). Each query still assumes all
  invariants of the package (`emit_invariant`), selected or not.
- `GameInvariantSmtDriver` has a new `req_claim`, and `GameRequest` a new `claim`. The
  selection applies to each oracle group and to the start group. The frame (`oracle_frame`,
  `start_frame`) still assumes all package and game invariants on the old state.
- Both error enums wrap `NoInvariantMatches` (transparent).
- `Project::prove_package` and `prove_package_invariants` have a new `req_claim`. Plain
  `prove` gives `None`: its package-invariant section is not filtered.

### The CLI (`crates/domino/src/cli.rs`, `main.rs`)

- `--package` has `conflicts_with = "injective_randmap"`.
- `--game` no longer conflicts with `--claim` (the refusal of story 30 is removed).
- The help of `--claim` is the text of the spec.
- `main.rs` passes `p.claim` to `prove_package` and to `GameRequest`.

### Fixtures (`testdata/prove-claim/`, new)

- `pkg`: a copy of `test-projects/test-package-invariant-params` with a second, false package
  invariant `bad` on `P`.
- `game`: composition `C` with one package `Q` (state `a`, `b`, `c`; oracle `O` does
  `a <- b`) and three game invariants: `main` (`a >= 0`), `other` (`b >= 0`), `bad` (`c < 0`).
  `main` is preserved by `O` only with `other` as an assumption. The three do not contradict
  each other, so the assumptions are not vacuous. Check: with `other` removed from the file,
  `--game C --claim main` fails for `O` (done by hand, file restored).

## Tests run (all green)

Each command ran alone, filtered, with `--test-threads=1`. Only small fixtures.

| Command | Result |
|---|---|
| `cargo test -p domino --test prove_claim` (new, 7 tests) | 7 passed |
| `cargo test -p domino --test prove_game` (one entry removed from the clap test) | 10 passed |
| `cargo test --lib invariant_claim` (3 new unit tests) | 4 passed |
| `cargo test --lib package_invariant` | 20 passed |
| `cargo test --lib game_invariant` | 5 passed |
| `cargo test --lib side_run` (memory cap 6G) | 11 passed, 1 ignored (full 4WHS) |
| `cargo test -p domino --bin domino` | 1 passed |
| `cargo clippy --workspace --all-targets` | clean |
| `cargo fmt --check` | clean |

The new tests, by §5 of the spec:

- `package_claim_selects_one_invariant`: `--claim main` verifies, `--claim bad` fails, no flag
  fails.
- `package_claim_is_a_wildcard`: `--claim 'ma*'`.
- `no_match_lists_the_names_before_any_solver_runs`: `--package P --claim nope` lists
  `main, bad`; `--game S --claim nope` (se25) lists `main`. Both run with an empty `PATH`, so
  no solver can start.
- `game_claim_proves_one_invariant_and_assumes_the_others`: `--game C --claim main` verifies
  (it needs `other` as an assumption); no flag fails on `bad`.
- `game_claim_applies_to_the_start`: `--invariant-start --claim main` verifies; with no flag
  the start fails on `bad`.
- `clap_refuses_package_with_injective_randmap`.
- `proof_claim_still_matches_the_equivalence_claims`: `--proof T --claim 'nope*'` on se25 gives
  no "no invariant" error, and the package section still fails on `package-invariant!main!P!`.
- Unit tests in `invariant_claim.rs`: the wildcard matches the declared name only (the full
  claim name does not match), no pattern selects all, no match lists the names.

Test-first: the unit tests and the fixture were written with the code in the same slice, so a
red run was not seen for each test. The integration tests fail on the code of story 30 by
construction (it ignores `--claim` with `--package` and refuses it with `--game`).

## Tests written, not run

None. Not built: `--features cvc5-lib` (the `cvc5-sys` build script fails on this machine,
as in story 30). The new code has no `cvc5-lib` gate.

## Complexity

The gate did not run: `sdlc code index .` fails in the bubblewrap sandbox
(`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`). **CRAP: UNMEASURED.** CC by
hand (decision points + 1):

| Symbol | CC |
|---|---|
| `invariant_claim::select` | 3 |
| `invariant_claim::declared_name` | 1 |
| `PackageInvariantSmtDriver::new` | 1 |
| `PackageInvariantSmtDriver::verify` | 4 |
| `PackageInvariantSmtDriver::verify_claim_group` | 4 |
| `GameInvariantSmtDriver::new` | 1 |
| `GameInvariantSmtDriver::verify` | 4 |
| `game_invariant::prove::prove_game` (one field added) | 8 |
| `Project::prove_package_invariants` | 5 |
| `Project::prove_package` | 2 |
| `Project::prove` (one argument added at a call) | unchanged |
| `domino::prove` (one field and one argument added) | 11 |

Every edited function has CC < 15.

## Deviations from the spec

- A pattern that is not a valid wildcard gives `NoInvariantMatches` (it matches nothing). On
  an equivalence, the same pattern panics (`Wildcard::new(..).unwrap()` in `verify_fn.rs`);
  that path is not changed.
- The fixture of the game test is new (`testdata/prove-claim/game`), not se25: se25 has only
  one game invariant. The se25 check of §7 (`--claim nope` lists `main`) is in the tests.
- `--features cvc5-lib` not built (see above).
