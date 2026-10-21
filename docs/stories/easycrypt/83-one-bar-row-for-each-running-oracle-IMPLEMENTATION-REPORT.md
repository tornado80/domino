# Story 83 — Implementation report: one bar row for each running oracle

Rust only. Proving and the files it writes do not change. ADR 0020 points 3 and 5 are
implemented.

## What changed

### The board (`src/writers/easycrypt/progress.rs`)

- `BarProgressBoard` now has one `MultiProgress` for the whole command run. `new()` draws on
  stderr; `with_target` (crate only) draws on a given target (the tests use `InMemoryTerm`).
  Making the board registers its screen; dropping it clears the screen.
- `job(stem, oracles)` adds a header row: `<stem> tactics <bar> <d>/<n>  done <d>, running <r>`.
  The header counts the oracle rows that it made and that were dropped. It has no status
  method. Dropping the job progress removes the header.
- `JobProgress::oracle(name)` inserts an oracle row under the header and the rows of the job
  that are already there. The row has the template `  {wide_msg} {elapsed}` and a steady tick
  of 1 s.
  - `LockstepStarted`: `<oracle>  lockstep`, timer reset.
  - `lockstep_observer()` returns a `LockstepRow` that writes to the same row:
    `<oracle>  lockstep  node <i> <kind>  pairs <n> <tally>`. It does not register a screen.
    `⚠ GOAL FAILS at …` and stuck points print above the rows, as in `BarObserver`.
  - `NodeStarted` and `SentenceSent`: `proving_message(...)`, timer reset.
  - When the row is dropped, it leaves the screen, and one line prints above the live rows:
    the `lockstep_summary_line` and the oracle's end, for example
    `  PKENC  lockstep: 23 joint paths, 1 stuck point in 41.2s; done, 1 admit`, or
    `  DEC  interrupted at N7` when the goal of the last node is not closed or admitted.
- Removed: the temporary adapter of story 82 §2.4 (`BarJob` with `busy`, `ScreenRow`).
  `OneObserverJob` is now `#[cfg(test)]`: only the test board `FactoryBoard` of
  `src/easycrypt/tactics/tests.rs` uses it.
- `BarExportObserver` stays for the export phases.

### The one screen (`src/debug/progress.rs`)

- New `register_screen(mp)` and `clear_screen()`. `register_screen` has a `debug_assert!` that no
  other screen is active. `BarObserver` uses these two functions. `eprintln_above_bars` and the
  Ctrl-C handler do not change.
- `Tally` (`bump`, `render`) is `pub(crate)`, so that the oracle row shows the same tally.
- `SCREEN_TEST_LOCK` (test only): the tests that make a screen hold it, because there is one
  screen for each process.

### Build

- `Cargo.toml` `[dev-dependencies]`: `indicatif` with the feature `in_memory` (tests only).

## Tests

New, in `src/writers/easycrypt/progress.rs` (drawn on `InMemoryTerm`, timers taken out):

- `two_oracle_rows_under_one_header`
- `a_row_goes_from_lockstep_to_proving`
- `a_finished_row_leaves_and_its_summary_is_above`
- `a_line_above_the_rows_tears_no_row`
- `a_second_screen_fails_the_debug_assertion` (debug builds)

Removed: `the_bar_board_gives_the_screen_to_one_row_at_a_time` (the adapter is gone).

Runs:

- `cargo test -p sspverif --lib -- writers::easycrypt::progress debug::progress`: 18 passed,
  0 failed, five runs in sequence (no flaky result).
- `cargo build --workspace` and `cargo clippy --workspace --all-targets`: clean, without and with
  `--features cvc5-lib`. `cargo test --no-run --features cvc5-lib -p sspverif`: compiles.

Written before, not run (owner's rule: no test that translates or proves):

- Story 82's event tests in `src/easycrypt/tactics/tests.rs` (`progress_board` module). The diff
  does not change the code they use (`FactoryBoard`, `OneObserverJob`), except the
  `#[cfg(test)]` gate.
- Full `cargo test --workspace`, with and without `--features cvc5-lib`.

## Complexity gate

`sdlc code index .` ran (299 symbols). `sdlc crap . --since-ref 43625f75 --threshold 15` failed:
"does not resolve to a commit ... (not a git repo, or an unknown ref)" (sdlc sandbox).
**CRAP: UNMEASURED.** The CC numbers are a decision-point count of each function body.

| symbol | file | CC | CRAP |
|---|---|---|---|
| `register_screen` (new) | debug/progress.rs | 2 | UNMEASURED |
| `clear_screen` (new) | debug/progress.rs | 1 | UNMEASURED |
| `BarObserver::new`, `BarObserver::clear` | debug/progress.rs | 1, 1 | UNMEASURED |
| `BarProgressBoard::new`, `with_target`, `drop`, `job` | writers/easycrypt/progress.rs | 1 each | UNMEASURED |
| `BarJobState::show_counts`, `add_row`, `remove_row` | writers/easycrypt/progress.rs | 1, 2, 1 | UNMEASURED |
| `BarJob::oracle`, `BarJob::drop` | writers/easycrypt/progress.rs | 1, 1 | UNMEASURED |
| `BarRow::show_proving` | writers/easycrypt/progress.rs | 2 | UNMEASURED |
| `BarRow::end_text` | writers/easycrypt/progress.rs | 5 | UNMEASURED |
| `BarRow::on_event` | writers/easycrypt/progress.rs | 7 | UNMEASURED |
| `BarRow::lockstep_observer`, `BarRow::drop` | writers/easycrypt/progress.rs | 1, 2 | UNMEASURED |
| `LockstepRow::show`, `LockstepRow::on_event` | writers/easycrypt/progress.rs | 1, 5 | UNMEASURED |

No touched function has CC ≥ 15.

## Code review

Deterministic scan: not run (the same sandbox problem). Standards and Spec reviews ran as
sub-agents. Fixed: `on` is now `with_target`; the lockstep summary and the oracle's end are now
one line, as the spec says; `end_text` says why `router` never ends a row as interrupted.
Left open, with reasons:

- Fixed lemmas (ADR 0020 point 6) do not show a tactic in a row: story 84.
- The header shows `done` and `running`; pending is `<n> - <d>` from the bar. The story's layout
  has no pending count.
- `LockstepRow` repeats the `GOAL FAILS` and stuck-point lines of `BarObserver`. The two draw on
  different bars; a shared line function is a small follow-up.
- `std::process::exit(130)` and `exit(1)` in `main.rs` skip the board's `Drop`. The rows are
  gone at that time, so only the registration stays.

## Not done

- Acceptance "by hand: `domino easycrypt prove --jobs 4` on `example-projects`": not run
  (owner's rule).
- Story 82's event tests and the full `cargo test --workspace`: not run (owner's rule).
- CRAP gate: UNMEASURED (see above).
