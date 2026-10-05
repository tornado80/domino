# Story 50 — Implementation report

"Plumbing" is now "exit guard" in the code, the viewer, `summary.txt`, the alignment report and
`trace.json`. Translation, the IR's behaviour, lockstep execution and every verdict stay the same.
Older stories and reports keep the old word; this report records the rename once.

## What changed

- **Identifiers.** `Plumbing { DoneGuard, CallResult }` (`src/debug/ir.rs`) is now
  `ExitGuard { DoneFlag, CallResult }`. `PlumbingKind` (`src/debug/lockstep.rs`) is now
  `ExitGuardKind`. Every `plumbing` field and parameter (IR branch, `BranchForm::If`, skeleton and
  alignment nodes, `SideView`) is now `exit_guard`. `plumbing_str` is now `exit_guard_str`.
- **Lowering.** The module-doc section is "What is an exit guard, and what it becomes". The
  `Shape::Plumbing` variant (the unlabelled `ec_result <- None` / `ec_done <- false`
  initialisations, not a branch) is now `Shape::FlagInit`. The test
  `plumbing_variables_never_reach_the_ir` is now `control_flow_variables_never_reach_the_ir`, and
  `plumbing_branches_are_labelled_decision_points` is now `exit_guards_are_labelled_decision_points`.
- **`summary.txt`:** `[exit guard: done flag]` / `[exit guard: call result]`.
- **Alignment report:** `(done-flag guard)` / `(call-result guard)`.
- **Viewer** (`lockstep_viewer.html`):
  - chip `exit guard (done flag)` / `exit guard (call result)`, tooltip
    "<kind>: an exit guard: exists only because EasyCrypt has one exit point; it skips code after
    an earlier return or abort";
  - joint-path table kind cell, for example `determined (exit guard: call result)`;
  - toggle "hide exit guards" (`#hide-exit-guards`), hash key `guards=hide`;
  - `isPlumb` → `isExitGuard`, plus `exitGuardOf` and `exitGuardName`; CSS `plumb` → `exit-guard`,
    `hide-plumb` → `hide-exit-guards`;
  - `plumbingRun` (it adds the always-run export lines to the executed set; it has no relation to
    exit guards) is now `exporterLinesRun`.
- **`trace.json`:** the per-side key is `exit_guard`, values `done-flag` and `call-result`.
  `LOCKSTEP_TRACE_SCHEMA` is 12.
- **Saved joint trees:** `SideView.exit_guard` has `#[serde(alias = "plumbing")]` and
  `ExitGuardKind::DoneFlag` has `#[serde(alias = "done-guard")]`. Serialisation writes only the
  new names.

## Design decisions

- The serde aliases are on the shared lockstep types, not on a separate saved-tree type. The trace
  and the saved tree use the same `SideView`, so one alias pair covers both. The trace accepts the
  old spelling on read, but nothing reads traces back, so this has no effect.
- The chip text carries the kind ("exit guard (done flag)"), so the reader does not have to hover
  to tell the two kinds apart. The tooltip starts with the kind and then gives the definition.
- The hash key changed from `plumb` to `guards`. An old bookmarked hash with `plumb=hide` now
  opens with exit guards shown. Pages embed their own trace and viewer, so old pages keep working.
- No variant for the abort-flag guard (story 22 §3.3).

## Rejected shapes

- A custom `Deserialize` for `SideView` that maps the old key by hand. `#[serde(alias)]` does the
  same in one attribute per name.
- Writing both keys during a transition period. The story requires that serialisation writes only
  the new names, and saved trees are never read by older binaries.
- Keeping `Shape::Plumbing` in the lowering because it names statements, not branches. The
  acceptance grep allows the word only in the alias and its test, and `FlagInit` says what the
  statements are.

## Tests

- `cargo test`: 610 passed, 0 failed, 5 ignored (baseline 609; one new test).
- `cargo clippy --all-targets`: no warnings.
- New: `a_tree_saved_before_the_exit_guard_rename_reads_and_writes_the_new_names` (`job.rs`). It
  reads the `OUTCOME` fixture, kept with its old spelling (`"plumbing": "done-guard"`), checks the
  value is `ExitGuardKind::DoneFlag`, and checks the written JSON has `"exit_guard":"done-flag"`
  and no old name. `a_saved_joint_tree_reads_back_as_it_was_written` now compares the written
  outcome with the fixture in the new names.
- Renamed: `every_exit_guard_is_a_determined_node` (`lockstep_run.rs`, `cvc5-lib` only).
- Real saved tree: the kem-dem `PKENC` tree in `_build` (43 nodes, written with
  `"plumbing"` / `"done-guard"`) was read with `SavedTree::read` in a temporary test. It read
  without error and has 22 nodes with an exit guard. The temporary test was removed.
- Export tree: `domino easycrypt export` on all 12 example projects, with the binary of the
  previous commit (built in a separate worktree) and with this commit. `diff -r` is empty
  (117 files).
- `grep -rni plumbing src crates` finds only the two aliases with their doc comments and the
  `job.rs` fixture and test.
- Headless Chrome, kem-dem `PKENC` trace with the keys renamed to the new spelling and schema 12:
  22 chips, with texts "exit guard (call result)" and "exit guard (done flag)" and the tooltip
  above. Toggle label "hide exit guards"; when checked, all 22 exit-guard rows are hidden and the
  hash is `#guards=hide`. Joint-path table cells: `determined (exit guard: call result)`,
  `determined (exit guard: done flag)`.

## Deviations

- `cvc5-lib` does not build on this machine (no `cmake`). Thus §5's `domino easycrypt debug` and
  `domino easycrypt prove --resume trust` were not run, and the `summary.txt` grep was not done on
  a real run. The `summary.txt` text is checked by reading the code only.
- The live resume check (old binary leaves a tree, new binary resumes it without lockstep and
  without a stale warning) was not run. In its place: the real kem-dem tree from `_build` was read
  by the new code (see Tests), and the fingerprint does not cover the tree's spelling, so a read
  tree is not stale.
- `trace.json` "differs only in key, values and schema" was not checked on two real runs. The
  viewer was checked on an old trace with only these three changes made by hand.
- The trace-schema test in `lockstep_run.rs` (now 12) is under `cvc5-lib` and did not run here.

## Open items

- Run §5 on a machine with `cvc5-lib`: the live resume of a tree saved on the previous commit,
  and the `summary.txt` grep.
- A bookmarked viewer hash with `plumb=hide` no longer hides exit guards.
