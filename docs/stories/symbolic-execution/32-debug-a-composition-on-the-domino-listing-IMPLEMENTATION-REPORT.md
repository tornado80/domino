# Story 32 — Implementation report: `domino debug --game C` on the Domino listing

`domino debug --game C [--oracle O] [--claim <name>]` runs one-sided execution of each oracle
of the composition `C` on the **Domino listing**, with its parameters free and with no theorem
(ADR 0021). It checks the game invariants of `C` and assumes the package invariants of its
instances. The EasyCrypt side tree (`domino easycrypt debug --side-inv C`) does not change.

## Fix before the story (separate commit)

"Fix: an invalid --claim pattern is an error on the equivalence path". `EquivalenceSmtDriver`
keeps the raw pattern. `verify` checks it before any solver work and returns the new
`gamehops::equivalence::error::Error::InvalidClaimPattern`. Before, `new` did
`Wildcard::new(..).unwrap()` and panicked. Only a bad escape is invalid for the `wildcard`
crate (for example `foo\`). Test: `prove_claim::invalid_claim_pattern_on_an_equivalence_is_an_error`
(`test-projects/test-empty-tuple`, which has an equivalence and no package invariant; empty
`PATH`, so no solver can start).

## What changed

### One engine for both listings (`src/debug/side_run.rs`)

- New `FreeRun` and `execute_free`: the part of `run_side_command` after the free theorem and
  the claims. `FreeRun.listing` selects the inlined oracle: `inline_oracle_ec` for
  `ListingKind::EasyCrypt`, `inline_oracle` on the `DebugTransform` instance for
  `ListingKind::Domino`. The claims, the base frame and the fingerprint are the same for both.
- `run_side_command` builds the free theorem, the context and the claims, then calls
  `execute_free` with `ListingKind::EasyCrypt`. Its output does not change.
- `OneSidedInputs` has two new fields: `listing` and `claim` (the declared name of the one
  invariant to check). `execute_one_sided` writes `meta.listing`, `meta.claim`
  (`claim_dir(claim, false)`) and `meta.all_claims` from them. `pkg_run` gives
  `EasyCrypt` and `None`, so it does not change.
- `StateOwner::subject` takes the listing. A composition on the Domino listing says
  "game invariants of `C`"; on the EasyCrypt listing it still says "side invariants of `C`".
- `ListingKind::as_str` is now `pub(crate)`.

### The run (`src/debug/game_run.rs`, new)

- `run_game_command(project, C, O, claim, opts, backend, root, observer, stop)`: the free
  composition from `C` alone (`composition_theorem`, as `prove --game`), then `execute_free`
  on the Domino listing, into `game_run_dir(root, C, O, claim)`. When an instance of `C` has a
  package invariant, it adds the assumption line of story 30 to `summary.txt`.
- `game_oracles(project, C, oracle)`: `O`, or every export of `C`.
- `assumption_line(project, C)`: the line that the CLI prints.
- Errors, all before any solver work: `UnknownComposition`, `UnknownOracle`, `NoGameInvariant`
  (the errors of story 30, through the new `DebugError::GameInvariant`), and
  `NoInvariantMatches` for an unknown `--claim` name (new `DebugError::NoInvariantMatches`; its
  help lists the game invariants of `C`).

### Shared checks (`src/game_invariant/lookup.rs`, new; `src/invariant_claim.rs`)

- `composition_of`, `export_names`, `check_export`: the checks that `prove --game` and
  `debug --game` share. `prove_game` and `GameInvariantSmtDriver::claim_groups` use them, so
  the error texts are the same in both commands.
- `game_invariant::assumption_note(comp)`.
- `invariant_claim::select_exact`: as `select`, but an exact declared name (two-sided
  `debug` takes an exact name, and the name is the run directory). `select` and
  `select_exact` share a private `select_by`.

### Layout and index (`src/debug/layout.rs`, `src/debug/index.rs`, `src/debug/sweep.rs`)

- `GAME_DIR = "!game!"`, `game_dir(root, C)`, `game_run_dir(root, C, O, claim)`.
- `Level::Game { composition }`, directory `<root>/!game!/<C>/`, parent `Level::Project`,
  title "domino debug — game invariants of `C`". Its rows are the runs (as a proofstep index).
- A record is a game run when it has a composition and its listing is `domino`
  (`ResultRecord::game`). The project index lists one row `game  <C>` for each such
  composition, after the theorems, with a link to `!game!/<C>/index.html`. The synthetic
  theorem name `<C>$Invariant` is not shown: the failure label is `game C O [claim]`, and
  `SweepEntry::label` (the line that the CLI prints) is `game C O`.

### The CLI (`crates/domino/src/cli.rs`, `main.rs`)

- `Debug` has `--game <C>` with the help text of the spec. clap refuses it with `--proof`,
  `--proofstep`, `--claim-set`, `--lockstep`, `--no-check-left`, `--no-check-right` and
  `--first-failure-per-claim`. The help of `--claim` tells the meaning with `--game`.
- `debug` calls the new `debug_game` when `--game` is given. `debug_game` runs each oracle one
  after another, prints one line for each, writes the `Level::Game` index (with `--oracle`:
  updates the indexes that exist), and exits non-zero when a check fails or a run stops early.
- The `SmtOutArg` to `SmtOut` map moved to `smt_out_of`, which both functions use.

## Tests run (all green)

Each command ran alone, filtered, with `--test-threads=1`, and the commands that start cvc5
had `systemd-run --user --scope -p MemoryMax=6G` and `timeout`. Only small fixtures.

| Command | Result |
|---|---|
| `cargo test --lib game_run` (new, 6 tests + 1 layout test that the filter also selects) | 7 passed |
| `cargo test --lib side_run` | 11 passed, 1 ignored (full 4WHS) |
| `cargo test --lib pkg_run` | 6 passed |
| `cargo test --lib debug::index` | 10 passed |
| `cargo test --lib debug::layout` (1 new) | 4 passed |
| `cargo test --lib debug::sweep` | 2 passed |
| `cargo test --lib game_invariant` | 6 passed |
| `cargo test --lib invariant_claim` (1 new) | 5 passed |
| `cargo test -p domino --test debug_game` (new; the clap test, the others need `cvc5-lib`) | 1 passed |
| `cargo test -p domino --test prove_claim` (1 new, the fix) | 8 passed |
| `cargo test -p domino --test prove_game` | 10 passed |
| `cargo test -p domino --bin domino` | 1 passed |
| `cargo clippy --workspace --all-targets` | clean |
| `DOCS_RS=1 cargo clippy --workspace --all-targets --features cvc5-lib` (see below) | clean |
| `cargo fmt --check` | clean |

The new library tests, by §5 of the spec:

- `the_free_composition_splits_on_its_parameter_on_the_domino_listing`: se25, `S.O`: the root
  is a `Split`, four terminals, the two with `x < 0` fail `main`, the other two verify. The
  listing is the Domino listing (`p.k <- n;`, not the EasyCrypt text). Agreement: the failing
  terminals are the same as in the side tree of `run_side_command`. The subjects are
  "game invariants of S" and "side invariants of S".
- `the_free_instance_is_not_the_theorem_instance_of_the_same_name`: se25-name-taken, the root is
  still a `Split`.
- `the_run_writes_into_the_game_directory_by_its_claim`: `!game!/S/O/!all-claims!/` with the
  four artifacts, a record with `composition: S` and `listing: domino`, the assumption line in
  `summary.txt`; with `claim = main`, `!game!/S/O/main/`.
- `an_unknown_claim_lists_the_game_invariants`: `nope` gives the list `main`.
- `the_errors_of_prove_game_come_before_any_solver_work`: unknown composition, unknown oracle.
- `the_project_index_lists_the_composition_after_the_theorems`: the project index has
  `game  S` and links `!game!/S/index.html`; the game index lists `O`; no `$Invariant`.
- The EasyCrypt side is byte-identical: `the_side_inputs_match_the_golden_from_before_the_move`
  (claim names, base frame, fingerprint of story 30's golden files) passes after the change.
- A two-sided `domino debug` run: the code path does not change except the place where `root`
  is computed and `smt_out_of`. Its tests need `cvc5-lib` (see below).

## Tests written, not run

`crates/domino/tests/debug_game.rs`, module `runs` (`#[cfg(feature = "cvc5-lib")]`):
`a_failing_game_invariant_fails_the_run_and_writes_the_game_directory`,
`claim_selects_the_run_directory_and_out_moves_the_root`,
`an_unknown_claim_lists_the_game_invariants`, `the_project_index_lists_the_composition`,
`unknown_composition_and_oracle_give_the_errors_of_prove_game`. Reason: `domino debug` needs the
`cvc5-lib` build, and the `cvc5-sys` build script fails on this machine (no `cmake`, no static
cvc5), as in stories 30 and 31. The same is true of the existing two-sided `debug` tests
(`debug_all_claims.rs`, `lockstep_run` unit tests). The library tests above cover the same
behaviour through `run_game_command` with the process cvc5 backend.

The `cvc5-lib` code was type-checked and linted with `DOCS_RS=1` (the `cvc5-sys` build script
then uses its pre-generated bindings and does not build cvc5) in a separate target directory.
It was not linked or run.

## Complexity

`sdlc code index .` ran (1157 symbols). `sdlc crap . --since-ref f005e66a --threshold 15`
failed in the bubblewrap sandbox (`bwrap: loopback: Failed RTM_NEWADDR: Operation not
permitted`; it then cannot resolve the ref). **CRAP: UNMEASURED.** CC by hand (decision points
+ 1; `?` counted as a branch):

| Symbol | CC |
|---|---|
| `EquivalenceSmtDriver::new` | 1 |
| `EquivalenceSmtDriver::verify` | 4 |
| `EquivalenceSmtDriver::is_claim_requested` | 2 |
| `invariant_claim::select`, `select_exact` | 2 each |
| `invariant_claim::select_by` | 2 |
| `game_invariant::lookup::composition_of`, `export_names`, `check_export` | 1, 1, 2 |
| `game_invariant::assumption_note` | 1 |
| `GameInvariantSmtDriver::claim_groups` | 4 |
| `game_invariant::prove::prove_game` | 7 |
| `side_run::run_side_command` | 7 |
| `side_run::execute_free` (new) | 6 |
| `side_run::execute_one_sided` (fields only) | 9 |
| `StateOwner::subject` | 3 |
| `game_run::game_oracles` | 4 |
| `game_run::run_game_command` | 9 |
| `game_run::assumption_line` | 2 |
| `layout::game_dir`, `game_run_dir` | 1 each |
| `index::Level::dir`, `parent`, `title` | 6, 3, 6 |
| `index::levels_below` | 7 |
| `index::header` | 3 |
| `index::rows` (with its closures) | 10 |
| `ResultRecord::game`, `ResultRecord::label` | 1, 2 |
| `SweepEntry::label` | 2 |
| `domino::debug` (two lines moved out) | lower than before |
| `domino::debug_game` (new) | 11 |
| `domino::smt_out_of` (new) | 4 |

Every edited function has CC < 15.

## Deviations from the spec

- The project index row is `game  <C>` in `summary.txt` (one cell, as the spec writes it). The
  HTML shows the same cell.
- The summary names the assumed package invariants in two places: a line that the CLI prints
  before the runs, and a line at the end of `summary.txt` of each run.
- `domino debug --game C` without `--oracle` refreshes the `Level::Game` index and updates the
  project index only when it exists (ADR 0011, as a `--proof T` run does). A plain
  `domino debug` run creates the project index; it then lists the game rows.
- A game record is found by "it has a composition and its listing is `domino`". The EasyCrypt
  side-tree records are under `_build/easycrypt/`, not under the Domino debug root.
- `--features cvc5-lib`: type-checked and linted only (see above), not built or run.

## Addendum: the cvc5-lib tests ran

After the session, the lead session built with `--features cvc5-lib` (`source
~/.cache/domino/cvc5-lib-env.sh` sets `CVC5_LIB_DIR` and `CVC5_INCLUDE_DIR` to the cached static
cvc5; the build does not need cmake). With a 6G memory cap and `--test-threads=1`:

- `cargo test -p domino --features cvc5-lib --test debug_game`: 6 passed (the five `runs` tests
  that were "written, not run", and the clap test).
- `cargo test -p domino --features cvc5-lib --test debug_all_claims` (two-sided `debug`): 8 passed.
