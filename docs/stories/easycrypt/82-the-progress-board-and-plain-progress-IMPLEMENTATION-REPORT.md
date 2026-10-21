# Story 82 — Implementation report: the progress board, and plain progress for parallel jobs

Rust only. Proving and the files it writes do not change. ADR 0020 points 1, 2 and 4 are
implemented. Point 3 (bar rows) is story 83.

## What changed

### The seam (`src/writers/easycrypt/progress.rs`)

- New trait `ProgressBoard: Sync` with `job(stem, oracles) -> Box<dyn JobProgress>`, and new
  trait `JobProgress: Send + Sync` with `oracle(name) -> Box<dyn ExportObserver>`. `JobProgress`
  has no status method. `ExportObserver` and `DebugObserver` do not change.
- `NopProgressBoard`: no progress.
- `PlainProgressBoard`: each oracle row writes its lines with the key `<stem>/<oracle>` at the
  start (`keyed_line`). The job writes `<stem>  oracles <done>/<total> done` when a row is
  dropped (`job_line`). Each line is one `writeln!` on a locked stderr.
- `OneObserverJob` (crate only): one observer for a whole job. It gets one `tactics` phase, items
  numbered across the oracles, and `PhaseFinished` when the job progress is dropped. This is the
  old `SharedProgress` logic, moved to the job progress.
- `BarProgressBoard` (temporary, until story 83): each job has one `BarExportObserver` through
  `OneObserverJob`. One running oracle of the board at a time has the screen (`busy` flag); the
  other oracles get `NopExportObserver`.
- `lockstep_summary` is split out of `lockstep_summary_line`, so the plain row can use it.

### The callers

- `run_tactics_observed`, `run_side_chain` and `run_jobs` (`src/easycrypt/tactics/mod.rs`) take
  `&dyn ProgressBoard` in place of the factory. The side-invariant chain thread gets the same
  board. `run_tactics` uses `NopProgressBoard`.
- `prove_equivalence` (`src/easycrypt/tactics/oracles.rs`) calls `board.job(stem, queue.len())`
  once. Each worker calls `job.oracle(name)`. `SharedProgress`, `Shared` and the
  `if workers == 1` branch are removed: `--jobs 1` is one worker thread on the same path.
- `prove_equivalence` was over budget (CC 28 before). Its parts are now `check_wanted_oracle`,
  `queue_oracles` and `finish`.
- `crates/domino/src/main.rs`: new `progress_board(mode)`. `easycrypt_prove` makes one board for
  each command run, before the loop over the theorems. The export phases keep their own
  `export_observer`.
- No `NopExportObserver` is left in `oracles.rs` and `tactics/mod.rs`.

### Plain output: a change

The old `tactics: N item(s)` and `tactics i/N: <name>` lines go. The item line is now
`<stem>/<oracle>  started`. Thus each plain line of a job starts with `<stem>/<oracle>` or
`<stem>`, as §3 asks. The node line is `<key>  N7/23` (two spaces), as in the story's example.

### Tests

- The tests in `src/easycrypt/tactics/tests.rs` that used the factory now use a test board,
  `FactoryBoard`, with one observer for each job (as a `--jobs 1` job had before). `WALK` holds an
  `Arc<Mutex<..>>`: the oracle workers now run on threads of their own, and they write to the
  test's walk through a handle taken on the test's thread. `Capturing` uses `Arc<Mutex<..>>`.

## Tests

New, in `src/easycrypt/tactics/tests.rs`, module `progress_board`, with a `RecordingBoard` that
records `(job, oracle, event)` and the logging `FakeEasyCrypt`:

- `with_two_jobs_no_oracle_is_silent`: `--jobs 2`, the four-oracle project
  (`testdata/easycrypt/unanswered-interrupt/four-oracles`; four oracles, not three). Each oracle
  has `LockstepStarted`, `NodeStarted`, `SentenceSent` and `LockstepFinished` on its own key.
- `the_chain_beside_an_equivalence_reports_with_one_job`: `story58`, theorem `OneSided`,
  `--jobs 1`. The `SideInv_` job and the `Eq_` job both have rows with events.
- `each_oracle_has_the_same_events_with_one_job_and_with_two`.

New, in `src/writers/easycrypt/progress.rs`:

- `plain_board_lines_start_with_the_key_of_the_row_or_the_job`
- `one_observer_job_numbers_the_items_of_its_rows_and_ends_the_phase`
- `the_bar_board_gives_the_screen_to_one_row_at_a_time`

Runs:

- Baseline before the first edit: `cargo test -p sspverif --lib -- easycrypt:: writers::easycrypt::progress`:
  540 passed, 0 failed. `DOMINO_EASYCRYPT` was not set, so the EasyCrypt tests skipped.
- The three `progress_board` tests with `DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`:
  3 passed (11.7 s), before the owner's stop rule.
- `cargo test -p sspverif --lib -- writers::easycrypt::progress`: 11 passed (last run).
- `cargo build --workspace` and `cargo clippy --workspace --all-targets`: clean, without and
  with `--features cvc5-lib` (cvc5 environment from `~/.cache/domino/cvc5-lib-env.sh`).
- A full `cargo test --workspace` run with EasyCrypt started. It was stopped by the owner's rule
  (no tests that translate or prove). Before the stop it showed one red test:
  `easycrypt::tactics::tests::live::three_jobs_prove_three_oracles_at_once_and_the_report_keeps_oracle_order ... FAILED`.
  The failure line was not captured, and the test was not run again (owner's rule). This
  diff changes the threads of `--jobs 1` only; with `--jobs 3` the path is the same as before,
  except that the job progress is now a board row. The cause can be the load of the full run
  (the test counts EasyCrypt processes at the same time). It is NOT verified.

## Complexity gate

`sdlc code index .` and `sdlc crap . --since-ref b707e5a2 --threshold 15` did not run: the
sdlc sandbox (bubblewrap) cannot run git in this worktree ("does not resolve to a commit ...
confined by bubblewrap"). `deterministic_scan` failed for the same reason. **CRAP: UNMEASURED.**
`lizard` is not installed. The CC numbers below are from a decision-point count (if, while, for,
&&, ||, match arms) of each function body. They are approximate.

| symbol | file | CC | CRAP |
|---|---|---|---|
| `prove_equivalence` | oracles.rs | 28 → 11 | UNMEASURED |
| `finish` (new) | oracles.rs | 7 | UNMEASURED |
| `check_wanted_oracle` (new) | oracles.rs | 5 | UNMEASURED |
| `queue_oracles` (new) | oracles.rs | 4 | UNMEASURED |
| `work` | oracles.rs | 1 | UNMEASURED |
| `run_tactics_observed` | tactics/mod.rs | 6 | UNMEASURED |
| `run_side_chain` | tactics/mod.rs | 7 | UNMEASURED |
| `run_jobs` | tactics/mod.rs | 4 | UNMEASURED |
| `run_tactics` | tactics/mod.rs | 1 | UNMEASURED |
| `keyed_line` (new) | progress.rs | 7 | UNMEASURED |
| `lockstep_summary` (new), `lockstep_summary_line` | progress.rs | 4, 1 | UNMEASURED |
| `OneObserverRow::on_event` (new) | progress.rs | 7 | UNMEASURED |
| other new board methods (`job`, `oracle`, `drop`, `new`, `lockstep_observer`, `job_line`, `write_stderr_line`) | progress.rs | 1–2 | UNMEASURED |
| `progress_board` (new) | main.rs | 5 | UNMEASURED |
| `easycrypt_prove` | main.rs | 7 | UNMEASURED |

No touched function has CC ≥ 15.

## Code review

Standards and Spec reviews ran as sub-agents. Fixed: the plain item line is back as
`<key>  started`; `OneObserverJob` is `pub(crate)`; the `PlainProgressBoard` comment now says
that the phase lines go and that the job line is written for each dropped row. Left open, with
reasons:

- `keyed_line` repeats three arms of `PlainExportObserver::on_event`. `PlainExportObserver` still
  serves the export phases; its tactics arms are now dead in `prove`. Story 83 can remove them.
- `progress_board` repeats the `ProgressMode` match of `export_observer`. They return different
  types.
- `BarProgressBoard` makes one `MultiProgress` for each job, and the job progress is dropped
  before the fixed lemmas run. Stories 83 and 84 own these.

## Not done

- Full `cargo test --workspace`, with and without `--features cvc5-lib`: not run to the end
  (owner's rule). The tests that run EasyCrypt or translation, in `src/easycrypt/tactics/tests.rs`
  and the `domino` integration tests, were not run after the last edits. The three
  `progress_board` tests passed once before the review fixes.
- `three_jobs_prove_three_oracles_at_once_and_the_report_keeps_oracle_order`: red once in a
  loaded full run; not investigated (see Tests).
- Acceptance "byte-identical export tree, session records, pages and reports": not checked by a
  run. The diff does not change any writer of these files.
- The "plain" test of §3 is a unit test of the line functions, not a run of `PlainProgressBoard`
  through a job.
- CRAP gate: UNMEASURED (see above).
