# Story 50 — "Plumbing" becomes "exit guard"

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 22 (plumbing branches), 24 (the joint-tree viewer).
**Blocks:** nothing. It may land before or after 48 and 49; whichever lands second resolves the
conflict in `lockstep_viewer.html`.

A **naming** story. Translation, the IR's behaviour, lockstep execution, alignment and every
verdict stay the same. The export tree is byte-identical before and after.

---

## 1. Why this story exists

The owner: *"the term plumbing in the debug ui is not very good and is not self-explanatory. When is
a node considered plumbing?"*

The answer, from `CONTEXT.md` and story 22: a branch is plumbing when it exists only because
EasyCrypt allows one exit point. That covers the done-flag guard `if (!ec_done)`, the call-result
guard `if (!(ec_rN = None))`, and the router's `if (!abort_flag)`. A joint node is shown as
plumbing when either side's head is one. The word explains none of this.

The grilling session settled the name **exit guard**, with three kinds: **done-flag guard**,
**call-result guard** and **abort-flag guard**. `CONTEXT.md` is already updated and lists
"plumbing branch" under _Avoid_. The owner also asked that internal identifiers follow the
glossary, so the code does not keep the old word.

## 2. Inherited from earlier stories

Where the word appears (`grep -rni plumbing src crates`):

- `src/debug/ir.rs`: `enum Plumbing { DoneGuard, CallResult }`, `InlStmt::Branch.plumbing`.
- `src/debug/lockstep.rs`: `PlumbingKind`; each side of a joint node has `plumbing`.
- `src/debug/lockstep_run.rs`: the field in the trace, and tests
  (`every_plumbing_branch_is_a_determined_node`).
- `src/debug/lockstep_report.rs`: `summary.txt` prints `[plumbing: done-guard]` and
  `[plumbing: call-result]`.
- `src/debug/lockstep_viewer.html`: the "plumbing" chip and its tooltip, the "(plumbing)" suffix in
  the joint-path table, the "hide plumbing nodes" toggle, `isPlumb`, and the CSS classes
  `plumb`/`hide-plumb`.
- `src/easycrypt/align.rs` and `src/easycrypt/skeleton.rs`: `Plumbing` in skeleton nodes; the
  alignment report prints "(done guard)" / "(call result)".
- `src/writers/easycrypt/lower.rs` and its tests: the module doc section "What is plumbing, and
  what it becomes".
- `src/easycrypt/job.rs`: a test fixture of a **saved joint tree** with `"plumbing": "done-guard"`.
  Saved joint trees live beside session records (ADR 0008) and are read back by later proof jobs.

## 3. Work to do

### 3.1 What the reader sees

- **Viewer chip:** `exit guard` with the kind as its tooltip and suffix: "exit guard (done flag)" or
  "exit guard (call result)". The tooltip reads: "an exit guard: exists only because EasyCrypt has
  one exit point; it skips code after an earlier return or abort".
- **Joint-path table:** the kind column reads e.g. `determined (exit guard: call result)`.
- **Toggle:** "hide exit guards".
- **`summary.txt`:** `[exit guard: done flag]` / `[exit guard: call result]`.
- **Alignment report:** "(done-flag guard)" / "(call-result guard)".

### 3.2 Identifiers

- `Plumbing` → `ExitGuard` (variants `DoneFlag`, `CallResult`); `PlumbingKind` → `ExitGuardKind`.
- `plumbing` fields → `exit_guard`; viewer `isPlumb` → `isExitGuard`; CSS `plumb` → `exit-guard`.
- Test names and doc comments to match; the lowering's module-doc section becomes "What is an exit
  guard, and what it becomes".
- No variant for the abort-flag guard is added: the router's guard stays out of the IR (story 22
  §3.3). The glossary names it so that prose can.

### 3.3 Serialized names

- `trace.json`: the per-side key becomes `exit_guard`, with values `done-flag` and `call-result`.
  Bump `LOCKSTEP_TRACE_SCHEMA`. Old pages are unaffected because each page embeds its own trace.
- **Saved joint trees:** a proof job must still read a tree written before this story.
  Deserialisation accepts the old key `plumbing` and the old value `done-guard`, for example with a
  serde `alias`. Serialisation writes only the new names. A saved tree does not become stale
  through this rename: the fingerprint covers lockstep's inputs, not the tree's spelling.

### 3.4 Not in this story

- Any change to which branches are exit guards, or to how lockstep handles them.
- Older stories and implementation reports keep the word "plumbing"; they are history. This
  story's report records the rename once.

## 4. Acceptance criteria

- [ ] `grep -rni plumbing src crates` finds only the backward-compatible deserialisation alias and
      its test.
- [ ] The viewer, `summary.txt` and the alignment report use the §3.1 wording.
- [ ] A saved joint tree written before this story (the `job.rs` fixture kept as is, plus one real
      tree saved on the previous commit) resumes without a warning and without re-running lockstep
      execution.
- [ ] `trace.json` differs from before only in the renamed key and values and the schema number.
- [ ] The export tree is byte-identical before and after.
- [ ] `cargo test` passes.

## 5. How to verify

Saved-tree compatibility. Build the commit before this story into a separate worktree, so the
shared stash is never touched:

```sh
OLD=<worktree of the previous commit>/target/debug/domino
D=target/debug/domino
cd example-projects/hello-world-oracle-rename-new
$OLD easycrypt prove --theorem Proof --proofstep 0 -f   # Ctrl-C after the first oracle: leaves a saved joint tree
$D   easycrypt prove --theorem Proof --proofstep 0 --resume trust
```

The second run must resume from the saved tree: no lockstep stage, no stale warning.

Wording:

```sh
$D easycrypt debug --theorem Proof --proofstep 0 --oracle ChangeNameUsefulOracle
grep -c "exit guard" _build/easycrypt/*/\!debug\!/*/ChangeNameUsefulOracle/summary.txt
```

In the viewer, check the chip, its tooltip, the toggle and the joint-path table.
