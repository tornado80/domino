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

## Follow-up: the end line of a fixed row

- `prove_fixed_lemmas` sends `GoalFinished { oracle: <row>, goal: <row>, admitted }` to the
  row before it drops the row. This is an existing event kind.
- `BarRow` records a `GoalFinished` that comes before any node in `fixed_admitted`. The row
  then ends `  Frame_Ctr_Peek  accepted` or `  init  admitted`, not `done, 0 admits`.
- New test (ran, green): `progress::tests::a_fixed_row_ends_accepted_or_admitted`
  (`InMemoryTerm`). The event test with EasyCrypt now also expects the `GoalFinished`
  (written, not run).
- Filtered run after the follow-up: 20 passed, 0 failed. `cargo clippy --workspace
  --all-targets`: clean.
- CC after the follow-up: `prove_fixed_lemmas` 5, `BarRow::on_event` 9, `BarRow::end_text` 6.
  All below 15.

## Code review (`/code-review`, fixed point `cea84c6e`)

- Deterministic Scan: **UNMEASURED**. `sdlc deterministic-scan . --since-ref cea84c6e` fails:
  the sandbox cannot resolve the ref. No scan ran.
- Complexity: **UNMEASURED** (same cause). CC is below 15 for every touched function (see the
  tables above).
- Standards (sub-agent). One hard finding: the doc comment of the new test said `done`, but the
  test checks `accepted`. Fixed. Judgement calls:
  - Fixed: the field `file: Option<bool>` is renamed to `fixed_admitted`. The
    `show_proving` comment now also names an oracle row that has no node yet.
  - Left open: `BarRow` finds out that a row is a fixed row because it has no node
    (`at.is_none()`). A row-kind enum, set when the row is made, would need a change to the
    `JobProgress` interface. Not done in this story.
  - Left open: the plain board (`max(total, made)`) and the bar board (`inc_length`) each
    increase their total in their own way.
  - Left open: ADR 0020 point 6 says rows have "the file's name". The code removes the job
    stem (`init`), as the story says.
- Spec (sub-agent). Findings:
  - Left open: the event test uses a real EasyCrypt, not `FakeEasyCrypt`. It does not run
    without `DOMINO_EASYCRYPT`.
  - Left open: no test compares the bytes of the files before and after the change. The code
    that writes the files did not change.
  - Not in the spec, kept: the `GoalFinished` of a fixed row (requested by the coordinator for
    the end line), and the header count that includes the fixed rows.
  - `announce` uses `check file` when there is one candidate. `start_proofs` always gives two
    candidates, so a start lemma always shows `attempt k/2`.
- Left open: an oracle row shows its own `ItemStarted` text (`PKENC  Eq_H4_H5 PKENC`) for a
  short time, until `LockstepStarted` replaces it. A fix needs a way to tell oracle items from
  fixed-lemma items, which is the same row-kind question as above.

## Not done

- The event-level test with EasyCrypt: written, not run (owner's rule).
- `--features cvc5-lib` build and clippy: not run. `cmake` is not on PATH in this shell. This is a gap in the environment, not a fault in the code.
- CRAP gate: UNMEASURED (see above).
