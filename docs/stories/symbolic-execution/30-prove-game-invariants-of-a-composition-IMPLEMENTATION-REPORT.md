# Story 30 — Implementation report: `domino prove --game C`

`domino prove --game C [--oracle O] [--invariant-start]` proves each game invariant of the
composition `C`, for every value of its parameters, with no theorem (ADR 0021). It assumes the
package invariants of the instances of `C`. Plain `domino prove` does not change.

## What changed

### One owner of the free composition (`src/game_invariant/`, new)

- `free.rs`: `copy_name`, `free_theorem` and `free_params` moved here from
  `src/debug/side_run.rs` with no change. `side_claims` and `side_base_frame` moved here as
  `claims` and `base_frame`, with no change to their output.
- `composition_theorem(C)` (new): the entry point from `C` alone. It is `free_theorem` of an empty
  theorem named `<C>$Invariant` that has only the packages of `C`.
- `oracle_frame` (new): the base frame of the side tree, but with the return constraint of the
  oracle. One-sided execution walks the paths, so the side tree leaves this constraint out; a
  single solver query needs it. `base_frame` and `oracle_frame` share one private `frame`.
- `side_run.rs` calls the module (`free_theorem`, `claims`, `base_frame`). `fold.rs` calls
  `crate::game_invariant::free_theorem`. `side_run.rs` is 118 lines smaller (969 to 851, with two
  new tests).

### The driver (`src/game_invariant/verify.rs`, `prove.rs`, `error.rs`, new)

- `GameInvariantSmtDriver`: one claim group for `!invariant-start!` and one for each exported
  oracle of `C`. `--oracle` selects one group, `--invariant-start` the start group.
- Oracle group: `oracle_frame` (all package and game invariants of `C` on the old state), then
  the dependency `left-no-abort` and the negated game invariant on the new state, from
  `ClaimQuery::of` — the same claims (`game-invariant!<N>!<C>!`) that the side tree checks.
- Start group: declarations, definitions, constants, invariants, initial state values, then
  `emit_game_or_package_invariant_start_assert` for each game invariant.
- `--parallel`, `--transcript` (files in `_build/code_game/<C>/`, new
  `Project::get_game_invariant_smt_file`) and `--smtsolver` work as for `--package`.
- The UI has one section, `Game Invariants`, with one row for `C`.
- When an instance of `C` has a package invariant, `prove_game` prints one line:
  `assumes the package invariants of <P1>, <P2>; prove them with domino prove --package <P1>`.
- Errors (`game_invariant::error::Error`): `UnknownComposition` (help lists the compositions),
  `NoGameInvariant` (help names `--package`), `UnknownOracle` (help lists the exports of `C`).

### The CLI (`crates/domino/src/cli.rs`, `main.rs`)

- `Prove` has `--game <C>` with the help text of the spec. clap refuses it with `--package`,
  `--injective-randmap` and `--claim`.
- `--game` with `--proof` or `--proofstep` gives `GameWithProof`, with a help that says why (as
  `PackageWithProof` does).
- The argument checks of `prove` moved to `check_prove_args`, to keep the CC of `prove` low.

## Tests run (all green)

Each command ran alone, filtered, with `--test-threads=1`. Only small fixtures.

| Command | Result |
|---|---|
| `cargo test -p domino --test prove_game` (new, 10 tests) | 10 passed |
| `cargo test --lib side_run` | 11 passed, 1 ignored (full 4WHS) |
| `cargo test --lib game_invariant` | 5 passed |
| `cargo test --lib fold` | 12 passed |
| `cargo test --lib package_invariant` | 20 passed |
| `cargo test -p domino --bin domino` | 1 passed |
| `cargo clippy --workspace --all-targets` | clean |
| `cargo fmt --check` | clean |
| `domino prove` (plain) on `test-projects/test-game-invariant-params` | exit 0 |
| `domino prove` (plain) on `testdata/debug/se25` | exit 1: the package invariant of `P` fails, as the fixture intends (the code path of plain `prove` did not change) |

The new tests, by §5 of the spec:

- `the_oracle_group_of_se25_fails_and_the_run_exits_non_zero`, `the_start_group_of_se25_verifies`.
- `the_free_parameters_are_read_by_the_game_invariant` (`test-game-invariant-params`, `--game C`).
- `oracle_selects_only_its_group`.
- `the_report_names_the_assumed_package_invariants`; unit test
  `the_assumption_line_names_each_package_and_the_command`.
- `a_composition_with_no_game_invariant_gives_the_hint`,
  `an_unknown_composition_lists_the_compositions`, `an_unknown_oracle_lists_the_exports`.
- `clap_refuses_game_with_the_other_targets`.
- `package_and_game_select_by_kind_when_the_names_are_the_same` (new fixture
  `testdata/prove-game/same-name`: package `X`, composition `X`, composition `Bare` with no game
  invariant).
- `the_side_inputs_match_the_golden_from_before_the_move` (`side_run.rs`): the claim names, the
  base frame and the fingerprint of `S.O` for `se25` and `se25-name-taken`. The golden files
  (`testdata/debug/se25*/side_inputs.golden`) were written from the code before the move, and the
  test passes after it: byte-identical.
- `prove_game_fails_the_oracles_whose_side_tree_fails` (`side_run.rs`): agreement for `se25`.

## Tests written, not run

None. Not run: the acceptance check "plain `domino prove` on `example-projects/4WHS`" (a big
project; the safety rules forbid it). The code path of plain `prove` has no change except the
order of the argument checks.

## Complexity

The gate did not run: `sdlc code index .` and `sdlc crap` fail in the bubblewrap sandbox
(`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`). **CRAP: UNMEASURED.** CC by
hand (decision points + 1; `?` counted as a branch):

| Symbol | CC |
|---|---|
| `game_invariant::free::composition_theorem` | 3 |
| `game_invariant::free::base_frame`, `oracle_frame`, `frame` | 1 each |
| `game_invariant::free::free_theorem`, `free_params`, `claims` (moved, unchanged) | 2, 7, 1 |
| `game_invariant::verify::assumed_packages` | 1 |
| `game_invariant::verify::assumption_line` | 2 |
| `GameInvariantSmtDriver::claim_groups` | 5 |
| `GameInvariantSmtDriver::verify` | 3 |
| `GameInvariantSmtDriver::query` | 2 |
| `GameInvariantSmtDriver::start_frame` | 1 |
| `GameInvariantSmtDriver::verify_claim_group` | 3 |
| `GameInvariantSmtDriver::verify_with_solver` | 8 |
| `game_invariant::prove::prove_game` | 8 |
| `game_invariant::error::Error::prover_process`, `format_modelfile` | 1, 2 |
| `Project::get_game_invariant_smt_file` | 4 |
| `domino::check_prove_args` (new) | 11 |
| `domino::prove` | 11 |
| `side_run::side_fingerprint`, `fingerprint_of`, `run_side_command` (calls renamed only) | 4, 1, 8 |

Every edited function has CC < 15.

## Deviations from the spec

- `--game` with `--proof`/`--proofstep` is refused by `check_prove_args` (`GameWithProof`), not by
  clap. clap cannot give a help that says why, and the spec asks for one.
- The assumption line names the first assumed package after `--package`
  (`prove them with domino prove --package <P1>`); the spec has a placeholder `<P>`.
- The section test checks the kind through the error of an unknown oracle (`package X` against
  `composition X`): the progress UI writes nothing when the output is not a terminal.
- `oracle_frame` is new: the side tree's base frame leaves out the return constraint of the
  oracle, which a single query needs. The rest of the encoding is the side tree's.
- `--features cvc5-lib`: not built. The `cvc5-sys` build script fails on this machine (no static
  cvc5). The new code has no `cvc5-lib` gate.
- `--claim` with `--game` is refused by clap until story 31.
