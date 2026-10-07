# Story 22 — Implementation report: debug indexes at each level, and `--out` for every run

Each run now writes a result record into its run directory. The indexes are rendered from the
records on disk (ADR 0011). `--out` is now the debug root for every kind of run. It is no longer
limited to a run of one oracle.

## What changed

### Run directory (`src/debug/layout.rs`)

- `run_dir(root, &Target, claim_label)` is the one function that gives a run directory.
  `driver.rs` and `lockstep_run.rs` now call it, so they no longer each build the path. The
  EasyCrypt path does not change.
- `proofstep_dir(root, theorem, left, right)` gives the directory of a proofstep index.
- `Layout::result()` gives `<strategy>_result.json`.

### Result record and indexes (`src/debug/index.rs`, new)

- `ResultRecord` (schema 1) and `write_result`. Each Domino-listing run writes its record at the
  end of the run, also after an interrupt. `stop_reason` is a string: `"interrupted"`,
  `"max_paths"`, and so on.
- `now_utc` gives an ISO-8601 time, with no new dependency.
- `Level::of_filters` maps the CLI filters to the level of the index: root, theorem or proofstep.
- `refresh_indexes(root, &Level) -> Vec<WrittenIndex { path, updated }>` writes the index of the
  level, each index below it that has records, and each existing index above it.
  - Difference from the story: the story asks for `Vec<PathBuf>`. The `updated` flag is needed
    so that stdout can mark an index above the level with `(updated)`.
  - A run of one oracle uses `update_indexes`, which writes existing indexes only.
- One renderer serves all three levels:
  - The oldest-run column.
  - A "no index; run …" hint for a child that has no index.
  - A failures list with check chains, such as
    `invariant: goal-fails → state-relation rel_ctr: goal-fails (#1.1)`. It shows at most 50
    runs.

### Sweep (`src/debug/sweep.rs`)

- `SweepEntry` has two new fields, `claim` and `finished_at`.
- `Failure` is now `{check, part_of, pair, verdict}`, so it also records the failing parts of a
  claim (story 21).
- `write_index` is removed. The new index module renders all indexes.

### CLI (`crates/domino/src/main.rs`, `cli.rs`)

- `OutNeedsOneOracle` is removed. The debug root is `--out`, or `_build/debug` by default.
- After the runs, the indexes are refreshed for the level of the filters. stdout prints one
  `index    <path>` line for each index written, with `(updated)` on an index above the level.

### Documents

- Story 06: the two `--out` lines.
- `00-overview.md`: the Output row.
- `CONTEXT.md`: a new term, "Result record".

## Tests

- 10 unit tests in `index.rs` and 2 in `layout.rs`.
- The two interrupt tests now check that the record exists and that its `stop_reason` is
  `"interrupted"`.
- 4 cvc5-lib CLI tests in `crates/domino/tests/debug_all_claims.rs`:
  - `--out` for one oracle.
  - A theorem run with `--out`.
  - A proofstep run, the update of the theorem index, and a lockstep run.
  - A single-claim run and an all-claim run.
- `cargo test --workspace`: lib 669 passed, 0 failed, 5 ignored. The baseline was 659.
- `cargo test --workspace --features domino/cvc5-lib`: lib 774 passed, 0 failed, 6 ignored. All
  other test binaries pass.
- `cargo clippy --workspace --all-targets`, with and without `cvc5-lib`: no warnings.
- The interrupt tests and `debug_announces…` were run 6 more times. None failed.

## Manual verification (§5)

This was run on `hello-world-oracle-rename-new`.

```
$ debug --proof Proof --proofstep 0
index    …/_build/debug/Proof/medium_composition-small_composition/index.html
_build/debug: Proof            (no _build/debug/index.html)
$ debug --proof Proof
index    …/_build/debug/Proof/medium_composition-small_composition/index.html
index    …/_build/debug/Proof/index.html
$ debug --proof Proof --proofstep 0 --lockstep
index    …/_build/debug/Proof/medium_composition-small_composition/index.html
index    …/_build/debug/Proof/index.html      (updated)
grep -c lockstep → 3
$ debug --proof Proof --out /tmp/dbg
/tmp/dbg/Proof/index.html
/tmp/dbg/Proof/medium_composition-small_composition/index.html
```

Each run exits with `debug::claim_not_verified`, as expected, because `ChangeNameUsefulOracle`
fails. The theorem index links to the proofstep index. The proofstep index links to each run's
viewer.

## Screenshots

- Theorem index: `22-screenshots/1600-theorem.png`, `22-screenshots/800-theorem.png`
- Proofstep index: `22-screenshots/1600-proofstep.png`, `22-screenshots/800-proofstep.png`
