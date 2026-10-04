# Story 49 — The EasyCrypt listing paints what EasyCrypt runs, returns at `return`, and shows a waiting side

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 48 (persistent listings and target lines), 22 (exit guards in the lowering),
24 (the joint-tree viewer).
**Blocks:** nothing. 50 may land before or after.

This is a **debugger-display** story. **Translation does not change:** the export tree is
byte-identical before and after it. Names in the listing (`ec_r1`, `ec_result_1`, `dummy_1`) stay
exactly as they are; the owner decided against renaming them. The IR, lockstep execution, the joint
tree and every verdict stay the same. What changes is the listing metadata `trace.json` carries
and how the viewer paints it.

---

## 1. Why this story exists

The owner, on the EasyCrypt listing in the joint-tree viewer:

> *"You leave some lines without green colors (I know that when we go to the else branch, the then
> part should be left without color but ec_done and ec_result are not marked as green when an
> oracle is inlined."*
>
> *"Return and abort is marked at an irrelevant point not in the only return that is in the
> oracle. It is good to mark where the return value is assigned but mark the actual return as
> return or abort!"*
>
> *"Sometimes a non if condition is a decision point when for example one oracle has no more
> decision points."*
>
> *"The ec_r1 … is not very readable."*

All four come from the lowering's design (`src/writers/easycrypt/lower.rs`, module doc), which
is right for execution and wrong for reading:

- **Missing green.** These lines are left out of the IR on purpose, and lines outside the IR are
  never painted:
  - `ec_result <- None`, `ec_done <- false`, `ec_result_N <- None`;
  - the router prelude (`ec_result <- None; if (!abort_flag) {`);
  - the router tail (`if (ec_result = None) { abort_flag <- true; }`);
  - `return ec_result;`.
- **Return and abort on the wrong line.** The IR's `Return` is `ec_result <- Some e`. Its `Abort`
  is `ec_done <- true`, an inlined callee's closing `ec_rN <- ec_result_N;` (its fall-through), or
  the router's `abort_flag <- true`. The viewer paints the terminal colour on that label, so the
  single `return ec_result;` is never marked.
- **A non-`if` as a decision point.** "End of the oracle" is a decision point. A side that has
  finished stands at its terminal while the other side resolves its decisions, and the viewer
  paints that line amber as "decision point here". In the hello-world run below, the right side
  sits "at R10 `ec_result <- Some (…)`" for nodes 1–3.
- **`ec_rN`** says nothing about which call it holds.

Example: `example-projects/hello-world-oracle-rename-new`, oracle `ChangeNameUsefulOracle`,
`_build/debug/…/easycrypt/inlined.txt`. Left lines 15–16, 19, 28, 38–42 and right lines 5–7 and
11–15 are never green on any path. The right side's return is painted on R10.

## 2. Inherited from earlier stories

- `InlinedOracle.listing` (`src/debug/ir.rs`) holds the text and the `SiteInfo` of each labelled
  line (`kind`, `pkg_inst_name`, `oracle_name`, `depth`). An `InlStmt::Call` carries
  `frame_lines: (open, close)`. `trace.json` exposes `left_sites` / `right_sites`
  (`src/debug/lockstep_run.rs`).
- Story 22 §3.3: the router prelude and tail stay out of the IR **by design**. Alignment treats a
  lockstep terminal as matching whatever EasyCrypt skeleton remains on that side. This story does
  not change that; it only describes those lines to the viewer.
- Story 48: listings are built once and repainted from a spec, and each selection has a **target
  line** per side. This story changes the spec and two rows of the target table.
- `CONTEXT.md`: **waiting side**, **exit guard**.

## 3. Work to do

### 3.1 Describe the lines outside the IR

Have the lowering record a **role** for every listing line the IR does not label, and add those
roles to `trace.json` as `left_lines` / `right_lines` (bump `LOCKSTEP_TRACE_SCHEMA`). Each entry
holds its line and role, and the frame it belongs to where that matters:

| Role | Lines |
|---|---|
| `entry-init` | the entry frame's `ec_result <- None`, `ec_done <- false` |
| `router-guard` | the router's `if (!abort_flag) {` and the entry call comment `(* ec_result <@ … *)` |
| `frame-init` | an inlined frame's `ec_result_N <- None`, `ec_done_N <- false` |
| `guard-head` | the `if` line of an exit guard (`DoneGuard`, `CallResult`), so the painter can tell a guard head from its body |
| `router-tail` | `if (ec_result = None) {` |
| `router-abort` | the router's `abort_flag <- true;` |
| `return` | `return ec_result;` |

Braces and `var` lines get no role and are never painted, as today.

Also add `left_frames` / `right_frames`: one entry per inlined call, holding its open and close
lines, the callee's package instance and oracle, the caller's result temporary (`ec_r1`), and the
frame's renamed result local (`ec_result_1`). §3.5 reads this table.

Labelled lines keep their `SiteInfo`. Nothing here creates an IR statement.

### 3.2 Paint every line EasyCrypt runs

On a joint path, each side's listing is painted **executed** on:

1. the lines it paints today (consumed ranges, decision labels, the finished path's `lines`);
2. `entry-init` and `router-guard`: on every path, because the debugger models "this oracle call
   happens";
3. `frame-init` of each frame whose open line is executed;
4. **after the path's terminal**, what EasyCrypt still runs up to the end of the procedure:
   - every frame-closing line it passes;
   - the `guard-head` of every exit guard it passes, but not the guard's body (the guard is false
     there);
   - `router-tail`;
   - `router-abort`, only if the side aborted;
   - `return`.

The tail in step 4 comes from walking the listing structure from the terminal outwards: frames
and guards enclosing it, then their continuations at each level. It needs no solver. The *then*
of a branch not taken stays uncoloured, as today.

For an inner node (not a terminal pair), steps 1–3 apply to the prefix. Step 4 applies only to a
side that is **waiting** (§3.4).

### 3.3 Return and abort on `return ec_result;`

- The `return` line gets the terminal colour: **return** (green, solid edge) or **abort** (red).
- The IR terminal line keeps the executed colour and gets a tag:
  - **result set**: `ec_result <- Some e` in the entry frame;
  - **aborts here**: `ec_done <- true`, a failed `assert`, an inlined frame's fall-through closing
    line, or `router-abort` when the entry frame fell through.
- An inlined callee's outcome on this path is tagged at its frame-closing line (`ec_r1 <-
  ec_result_1;`): **callee returns** or **callee aborts**.
- The legend gains "result set / aborts here" (tag only) next to "return" and "abort".
- The **Domino** listing is unchanged: its `return`/`abort` statement *is* the terminal.

### 3.4 The waiting side

A side is **waiting** at a node when its head is its oracle's end and the node is not a terminal
pair.

- **Tree row:** the side reads `L waiting at return` (or `R …`), not its head's line and keyword.
  The chip is neutral, not the decision style.
- **Joint-path table:** that side's cell reads "waiting" with the `return` line's source.
- **Listing:** the side's target line (story 48 §3.3) is its `return` line on the EasyCrypt
  listing, or its return/abort statement on the Domino listing. That row gets a **waiting** style
  (dashed edge, neutral background) and the tag "waits here", never "decision point here". The
  §3.2 step-4 tail is painted, because EasyCrypt has nothing left to decide on that side.
- **Terminal pair:** each side's target line is its `return` line (EasyCrypt) or return/abort
  statement (Domino).

This changes display only. *End of the oracle* stays a decision point in lockstep execution.

### 3.5 Callee annotations

Using `left_frames` / `right_frames`:

- Every occurrence of a frame's result temporary (`ec_r1`) or renamed result local (`ec_result_1`)
  gets a hover: "`ec_r1`: result of `rand.UsefulOracle` (call at L17)" and "`ec_result_1`: the
  result inside `rand.UsefulOracle`".
- An end-of-line tag on the `var` line of each, on the frame-closing line ("← result of
  `rand.UsefulOracle`") and on its call-result guard ("did `rand.UsefulOracle` return?").
- A gutter bracket from the frame's open line to its close line, labelled `rand.UsefulOracle`.
  Nested frames nest their brackets.

The listing text itself is untouched.

### 3.6 Not in this story

- Renaming anything in the export or in the listing text (owner: no translation change).
- "Plumbing" to "exit guard" in the UI: story 50.

## 4. Acceptance criteria

- [ ] The export tree is byte-identical before and after (run `domino easycrypt export --force` on
      hello-world-oracle-rename-new and kem-dem-cca-ssp, then diff).
- [ ] The joint tree, every verdict and `inlined.txt` are unchanged. `trace.json` gains only
      `left_lines`, `right_lines`, `left_frames` and `right_frames`, and its schema number goes up
      by one.
- [ ] On `ChangeNameUsefulOracle` (EasyCrypt listing), joint path J1: left L14–16, L19, L28,
      L38 and L42 are executed or return-coloured. L39 is
      not (the side returned). L42 is **return**. L35 carries "result set". L23 and L32 carry
      "callee returns". Right side: R5–R7 and R11 are executed, R12 is not, R15 is **return**, and
      R10 carries "result set".
- [ ] On an EasyCrypt path that aborts in an inlined callee (find one in kem-dem or a
      test project and name it in the report): the callee's
      frame-closing line says "callee aborts", `router-abort` is executed, the `return` line is
      **abort**, and the body of every guard skipped after the abort is uncoloured.
- [ ] On nodes 1–3 of `ChangeNameUsefulOracle`, the right side shows "waiting at return" in the
      tree and "waiting" in the joint-path table. The right listing is centred on R15 with the
      waiting style. No right row is styled "decision point here".
- [ ] The same waiting display on the Domino listing (`domino debug --lockstep`), with the return
      statement as the waiting line.
- [ ] Hovering `ec_r1` anywhere shows its callee. The frame bracket for `rand.UsefulOracle` spans
      L17–L23.
- [ ] Rust tests on the roles and frames of a lowered oracle with a nested call, a mid-body abort
      and a fall-through abort.

## 5. How to verify

```sh
D=target/debug/domino
cd example-projects/hello-world-oracle-rename-new
$D easycrypt debug --theorem Proof --proofstep 0 --oracle ChangeNameUsefulOracle
$D debug --proof Proof --proofstep 0 --oracle ChangeNameUsefulOracle --lockstep
```

Headless Chrome on both pages: select J1 and nodes 1–3, and screenshot both listings. Repeat on the
aborting-callee oracle chosen above. Attach the screenshots and the export-tree diff (empty) to
the implementation report.
