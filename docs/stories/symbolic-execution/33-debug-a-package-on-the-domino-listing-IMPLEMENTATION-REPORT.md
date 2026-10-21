# Story 33 — Implementation report: `domino debug --package P` on the Domino listing

`domino debug --package P [--oracle O] [--claim <name>]` runs one-sided execution of each
oracle of package `P` on the **Domino listing**, with the parameters of `P` free, each import
call an **open call**, and no theorem (ADR 0021, ADR 0017). The EasyCrypt package tree
(`domino easycrypt debug --pkg-inv P`) does not change.

## What changed

### Open calls in the Domino inliner (`src/debug/ir.rs`)

- `Inliner::render_call`: an `invoke` with no edge goes to the new `render_open_call`. The
  inliner decides from the missing edge; no caller passes a flag.
- `render_open_call` finds the import in the import interface of the caller's package. An
  `invoke` of a name that the caller does not import is still `InlineError::UnresolvedEdge`.
  The line is the call as written, `y <- invoke Get(x)      // open call: …`. The bind gets
  the import's return type. There is no `Maybe` result and no call-result guard.
- New `pub const OPEN_CALL_MARK`: the mark on the line. It also tells the abort note: "open
  call: it can also abort; an abort ends the oracle and has nothing to check". So the viewer
  shows the note at each open call.
- The interface comment of `InlStmt::OpenCall` now tells both producers.

### The executor (`src/debug/exec.rs`)

- The open-call arm of `advance` moved to the new `bind_unknown`. It now also binds a fresh
  value to a **state field** (`ctr <- invoke Get(x)`), not only to a local. Before, the
  EasyCrypt lowering bound every import call to an `ec_r<N>` local, so only locals occurred.
  On the Domino listing a state bind can occur, and to ignore it is not sound.
- The `return`-in-a-call part of `advance` moved to the new `resume_caller` (no change in
  behaviour), so that `advance` has CC < 15.
- An open call is still not a decision point.

### One engine for the package tree (`src/debug/pkg_run.rs`)

- New `PkgRun` and `execute_pkg`: the part of `run_pkg_command` after the context. Only the
  inlined oracle depends on `ListingKind`: `listing_of` (EasyCrypt lowering) or
  `inline_oracle` on the `DebugTransform` instance (Domino). The base frame, the claims and the
  fingerprint are the same for both. `--claim` selects one claim with `select_exact`.
- New `pkg_context` (UnknownPackage, NoInvariant, OpenCallInLoop) and `check_oracle`
  (UnknownOracle). `run_pkg_command`, `pkg_listing` and `pkg_fingerprint` use them. The output
  of `run_pkg_command` does not change.

### The run (`src/debug/package_run.rs`, new)

- `run_package_command(project, P, O, claim, opts, backend, root, observer, stop)`: the open
  theorem of `P` (`open_game_theorem`, the package template with free parameters), then
  `execute_pkg` on the Domino listing, into `package_run_dir`. It adds `ABORT_LINE` to
  `summary.txt`: "An open call can also abort; an abort ends the oracle and has nothing to
  check."
- `package_oracles(project, P, oracle)`: `O`, or every oracle of `P`.

### Layout and index (`src/debug/layout.rs`, `src/debug/index.rs`, `src/debug/sweep.rs`)

- `PACKAGE_DIR = "!package!"`, `package_dir`, `package_run_dir`
  (`<root>/!package!/<P>/<O>/<claim-dir>/`).
- `Level::Package { package }`, directory `<root>/!package!/<P>/`, parent `Level::Project`,
  title "domino debug — package invariants of `P`".
- `ResultRecord::game` is now `ResultRecord::free_level`: a one-sided record on the Domino
  listing is a `Level::Game` (it has a composition) or a `Level::Package` (it has a package).
  The project index lists `game  <C>` rows and then `package  <P>` rows after the theorems.
  The failure label is `package P O [claim]`; `SweepEntry::label` is `package P O`.

### The CLI (`crates/domino/src/cli.rs`, `main.rs`)

- `Debug` has `--package <P>` with the help text of the spec. clap refuses it with `--game`
  and with each flag that `--game` refuses.
- `debug_game` and the new `debug_package` share the new `debug_free` (the loop over the
  oracles, the one-line output, the index and the exit code). There is one code path for
  both.
- `debug` had CC > 15. It is now split into `debug` (project, root and dispatch),
  `debug_proofsteps`, `TargetRunner::run` (lockstep or sequential run of one target),
  `finish_proofsteps`, `write_proofstep_indexes` and `print_written`. The behaviour does not
  change.

## Tests run (all green)

Each command ran alone, filtered, with `--test-threads=1`, after `source
~/.cache/domino/cvc5-lib-env.sh`, and under `systemd-run --user --scope -p MemoryMax=6G` with
`timeout`. Only small fixtures (`testdata/debug/se29`, `se25`).

| Command | Result |
|---|---|
| `cargo test --lib debug::` (all debug unit tests; 9 new in `package_run`, 1 in `layout`) | 151 passed, 2 ignored (full 4WHS) |
| `cargo test --lib package_invariant invariant_claim debug::exec` | 48 passed |
| `cargo test -p domino --features cvc5-lib --test debug_package` (new) | 4 passed |
| `cargo test -p domino --test debug_package` (no feature: the clap test) | 1 passed |
| `cargo test -p domino --features cvc5-lib --test debug_game` | 6 passed |
| `cargo test -p domino --features cvc5-lib --test debug_all_claims` (two-sided) | 8 passed |
| `cargo test -p domino --features cvc5-lib --test prove_claim`, `--test prove_game`, `--bin domino` | 8, 10, 1 passed |
| `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib` | clean |
| `cargo fmt --check` | clean |

The new tests, by §5 of the spec:

- `the_open_call_does_not_split_and_the_tree_splits_on_the_branch`: `Bad`, the root is a
  `Split` on `x < 0`, two terminals: `fails`, `verified`. No abort path.
- `an_open_call_before_a_write_has_one_path_that_verifies`: `Step`, one path, verified.
- `a_bare_open_call_verifies`: `Ping`, `invoke Put(Ctr.ctr)` with the mark, verified.
- `the_failing_claims_agree_with_the_easycrypt_package_tree`: for each oracle of `Ctr`, the
  same oracles fail as in `run_pkg_command`. The CLI test
  `bad_fails_as_in_prove_package_and_writes_the_package_directory` also runs
  `prove --package Ctr`: it fails for `Bad`.
- `the_listing_shows_the_call_as_written_with_no_guard`: the line with the mark, no `None`, no
  `<@`; `summary.txt` has the abort line.
- `an_invoke_of_a_name_that_the_package_does_not_import_is_an_unresolved_edge`: the imports of
  the instance are cleared, then `inline_oracle` gives `UnresolvedEdge` for `Get`.
- No open calls in a composition: `the_free_composition_splits_…` (`debug --game` on se25)
  now asserts that the listing has no open-call mark. The two-sided `debug_all_claims` tests
  pass with no change.
- `the_run_directory_and_the_project_index` and the CLI test
  `the_project_index_lists_the_package`: `_build/debug/!package!/Ctr/Bad/!all-claims!/`,
  `…/Bad/nonneg/` with `--claim nonneg`, the row `package  Ctr` and the link
  `!package!/Ctr/index.html`.
- `an_unknown_claim_lists_the_package_invariants`, `the_errors_come_before_any_solver_work`
  and the CLI test `the_errors_name_the_invariants_and_the_packages`: `--claim nope` lists
  `nonneg`; `--package Src` gives `NoInvariant`; `--package X` lists the packages; an unknown
  oracle is an error.
- `clap_refuses_package_with_game_and_each_two_sided_flag`.

## Tests written, not run

None.

## Complexity

`sdlc code index .` ran (839 symbols). `sdlc crap . --since-ref HEAD --threshold 15` failed in
the bubblewrap sandbox (`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`; it then
cannot resolve the ref). **CRAP: UNMEASURED.** CC by hand (decision points + 1; `?` counted as
a branch):

| Symbol | CC |
|---|---|
| `ir::Inliner::render_call` (let-else in place of `ok_or_else(..)?`) | 10 (no change) |
| `ir::Inliner::render_open_call` (new) | 4 |
| `exec::…::advance` (two arms moved out) | 13 (was about 18) |
| `exec::…::bind_unknown` (new) | 2 |
| `exec::…::resume_caller` (new, moved code) | 5 |
| `pkg_run::run_pkg_command` | 6 |
| `pkg_run::pkg_context`, `check_oracle` (new) | 2, 2 |
| `pkg_run::execute_pkg` (new) | 6 |
| `pkg_run::pkg_listing`, `pkg_fingerprint` | 3, 4 |
| `package_run::package_oracles`, `run_package_command` (new) | 4, 7 |
| `layout::package_dir`, `package_run_dir` (new) | 1, 1 |
| `index::ResultRecord::free_level` (was `game`) | 4 |
| `index::ResultRecord::label` | 2 |
| `index::Level::dir`, `parent`, `title`, `free_owner` | 7, 3, 7, 3 |
| `index::levels_below` | 7 |
| `index::header` | 3 |
| `index::rows` (with its closures) | 11 |
| `index::free_rows` (new) | 3 |
| `sweep::SweepEntry::label` | 4 |
| `domino::debug` (split) | 9 (was about 35) |
| `domino::debug_proofsteps` (new) | 12 |
| `domino::TargetRunner::run` (new) | 6 |
| `domino::finish_proofsteps`, `write_proofstep_indexes`, `print_written` (new) | 5, 5, 3 |
| `domino::debug_game` | 3 |
| `domino::debug_package` (new) | 2 |
| `domino::debug_free` (new) | 7 |

Every edited function has CC < 15.

## Deviations from the spec

- The executor changed a little (the spec says "the executor does not change"): an open call
  can bind a state field on the Domino listing, and that bind now gets a fresh value. An
  open call is still not a decision point. The fixture se29 binds only locals.
- The abort note at each open call is in the listing line (the mark), so the viewer shows it
  on the line of the call. There is no other viewer change.
- The theorem name in the result record is the synthetic `<P>$Invariant`. The index does not
  show it.
- As for `--game`, `domino debug --package P` writes the `Level::Package` index and updates
  the project index only when it exists. A plain `domino debug` run creates the project
  index; it then lists the package rows.
- `domino::debug` was refactored (split into six functions) because the story edits it and its
  CC was over 15.
- The no-open-call check on `test-projects/test-side-invariant-from-package-lemmas` was not
  added; the check is on `testdata/debug/se25` (`debug --game`) and the two-sided tests pass.
