# Story 84 — Implementation report: rows for the fixed lemmas

Rust only. The lemma files that proving writes do not change: the code that makes their text
is the same, only progress events are added. ADR 0020 point 6 is implemented.

## What changed

### The fixed lemmas (`src/easycrypt/tactics/fixed.rs`)

- `prove_fixed_lemmas` gets the job's `JobProgress`. Each file that it checks is a row,
  `job.oracle(<name>)`. The name is the file stem without `<job stem>_`: `Frame_Ctr_Peek`,
  `init` (from `PkgInv_Ctr_init.ec`). New function `row_name`.
- A file that is accepted from an earlier run (`37780a22`) gets no row.
- New function `announce`: before each candidate text, the row gets
  `ItemStarted { phase: Tactics, name }` and `SentenceSent` with the first line of the text.
  The name is `check file` for one candidate, else `attempt k/n` (the start lemma: `1/2`, `2/2`).
- `first_accepted` takes the candidates as a `Vec` (it must know their number) and the row.
  `check_written` and `check_start` pass the row.
- The row is dropped when the file is accepted or admitted.

### The end of the job (`src/easycrypt/tactics/oracles.rs`)

- `finish` gets the job progress and gives it to `prove_fixed_lemmas`. The job progress is
  dropped after `finish`. Thus the job ends (its `PhaseFinished`, its header) after the fixed
  lemmas, not before them. This closes the open item of story 82.
- `EquivalenceJob::stem` is now `pub(super)`.

### The boards (`src/writers/easycrypt/progress.rs`)

- `BarRow`: `ItemStarted` shows `<row>  <name>` and starts the timer again. `SentenceSent`
  without a node keeps the text and starts the timer again.
- `BarJob::oracle`: when a job makes more rows than its oracles, the header bar length
  increases, so the header stays `<done>/<rows>`.
- `PlainProgressBoard`: the job line uses the larger of the oracle count and the rows made:
  `PkgInv_Ctr  oracles 7/7 done` after 3 oracles, 3 frame files and the start lemma. The plain
  key is `PkgInv_Ctr/Frame_Ctr_Peek`. No new event kind.

## Tests

Ran (`cargo test -p sspverif --lib -- writers::easycrypt::progress tactics::fixed::tests`):
19 passed, 0 failed. New:

- `fixed::tests::a_fixed_row_is_named_by_the_file_stem_without_the_job_stem`
- `fixed::tests::a_frame_file_is_one_check_and_a_start_lemma_one_item_for_each_attempt`
  (event level, without EasyCrypt: the events of `announce`)
- `progress::tests::fixed_lemma_rows_show_their_step_under_the_header` (`InMemoryTerm`)

Written, not run (owner's rule: it starts EasyCrypt on a project):

- `tactics::tests::progress_board::the_fixed_lemmas_have_rows_and_a_rerun_skips_the_accepted_files`
  (`RecordingBoard`, `test-projects/test-package-invariant-imports`): a row for each frame file
  and the start lemma, with `ItemStarted` and `SentenceSent`; one item for each attempt; a rerun
  makes no row; a rerun with one frame file not accepted makes only its row. It compiles.

Also:

- `cargo build --workspace`: clean.
- `cargo clippy --workspace --all-targets`: clean.
- `--features cvc5-lib` (clippy and `cargo test --no-run`): NOT RUN. The build of `cvc5-sys`
  fails in this environment: `cmake: command not found`. This is not caused by the diff.
- Full `cargo test --workspace`: not run (owner's rule).

## Complexity gate

`sdlc code index .` ran (569 symbols). `sdlc crap . --since-ref cea84c6e --threshold 15`
failed: "does not resolve to a commit ... (not a git repo, or an unknown ref)" (sdlc sandbox,
as in stories 82 and 83). **CRAP: UNMEASURED.** The CC numbers are a decision-point count of
each function body.

| symbol | file | CC | CRAP |
|---|---|---|---|
| `prove_fixed_lemmas` | tactics/fixed.rs | 5 | UNMEASURED |
| `row_name` (new) | tactics/fixed.rs | 1 | UNMEASURED |
| `announce` (new) | tactics/fixed.rs | 2 | UNMEASURED |
| `first_accepted` | tactics/fixed.rs | 6 | UNMEASURED |
| `check_written`, `check_start` | tactics/fixed.rs | 2, 4 | UNMEASURED |
| `run_equivalence_job` caller lines, `finish` | tactics/oracles.rs | unchanged, 5 | UNMEASURED |
| `BarRow::on_event` | writers/easycrypt/progress.rs | 8 | UNMEASURED |
| `BarRow::show_proving` | writers/easycrypt/progress.rs | 2 | UNMEASURED |
| `BarJob::oracle` | writers/easycrypt/progress.rs | 2 | UNMEASURED |
| `PlainJob::oracle`, `PlainRow::drop` | writers/easycrypt/progress.rs | 1, 1 | UNMEASURED |

No touched function has CC ≥ 15.

## Code review

Self-review of the diff from `cea84c6e` (the deterministic scan has the same sandbox problem).
Left open, with reasons:

- An oracle row now also shows its `ItemStarted` (`PKENC  Eq_H4_H5 PKENC`) for the short time
  before `LockstepStarted` replaces it.
- The end line of a fixed row on the bar board is `  Frame_Ctr_Peek  done, 0 admits`, also when
  the file was admitted. The page and the report say which file is admitted.

## Not done

- The event-level test with EasyCrypt: written, not run (owner's rule).
- `--features cvc5-lib` build and clippy: no `cmake` in this environment.
- CRAP gate: UNMEASURED (see above).
