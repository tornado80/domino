# Story 27 — Early returns as `goto` in the debugger and in `domino inline`

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 26.
**Blocks:** 28.
**Decisions:** grilling of 2026-10-12/20, Question 9 (shape C).

A **listing** story. Rust only. The executor does not change.

---

## 1. Why this story exists

The debugger's IR (`src/debug/ir.rs`) keeps an inlined call as a nested `InlStmt::Call`. The
executor is correct: a `Return` inside a frame binds the call's result and continues after the
`Call`. But the listing prints such a return as `bind <- e;  // return from P.O`
(`ir.rs:565`), and the rest of the callee follows it. A return that can run before the callee's
last statement then *reads* as if it falls through.

The HTML viewer (story 26, `src/debug/view.rs`) already solves this: it prints
`bind <- e; goto end_P_O;  // returns from P.O` and puts `end_P_O:` after the inlined body. It also
stops a block after a statement that always exits. The owner wants the debugger pages and
`domino inline` to show early returns the same way.

The owner chose **one module for the rules, and each renderer keeps its own output** (Question 9,
shape C). The debugger's listing keeps "a label is a line number", which `trace.json`, the `smt/`
files, executed-line highlighting and lockstep alignment depend on.

Vocabulary (`CONTEXT.md`, already updated): **Early return**, **Listing**.

## 2. Inherited

- `ir.rs`: one pass builds the IR and the listing; `Call` records `frame_lines` and `arg_lines`;
  structural lines (braces, the frame header) have no label.
- `view.rs`: `Frame::end` (a `OnceCell` filled by the first early return), `View::labels`,
  `View::end_label` (`end_<Inst>_<Oracle>`, then `_2`, `_3` for a second inlining of the same
  oracle in one listing), `View::exits`, `View::block` (stops after a statement that always exits).

## 3. Work to do

### 3.1 The rules module

A new module (for example `src/debug/inline_rules.rs`) owns these rules, on the transformed AST:

- **which returns are early**: a `return` that is not in tail position of its oracle;
- **the label of a frame**: `end_<Inst>_<Oracle>`, characters other than letters and digits
  replaced by `_`, with `_2`, `_3`, … for a second inlining of the same oracle in one listing;
- **which statements always exit**: a `return`, an `abort`, or an `if` whose remaining branches all
  exit; a `for` loop never counts;
- **whether a condition is trivial** under given constants (`Some(true)`, `Some(false)`, `None`).
  Story 28 uses this; this story moves it out of `view.rs` only.

`view.rs` calls this module instead of its own copies. Its output does not change.

### 3.2 The debugger listing

- A `Return` that is early prints, on its own one line (one IR statement, one line):
  `bind <- e; goto end_P_O;  // returns from P.O`.
- A frame that has an early return prints `end_P_O:` in place of its closing `}`, at the frame's
  indentation. A frame without one keeps `}`.
- A tail return keeps `bind <- e;  // return from P.O`. The entry oracle's returns stay `return e;`.
- Statements after a statement that always exits are not in the IR today only if the transform
  removed them. If some remain, print them as today; the executor never reaches them.
- `InlStmt` does not change. `Call`'s `frame_lines` now end at the `end_P_O:` line when there is
  one.
- The same rendering is used for the Domino listing and the EasyCrypt listing, and in
  `domino inline`.

### 3.3 Snapshots

Every pinned listing snapshot with an early return in an inlined callee changes. Update them, and
list them in the report.

### 3.4 Rejected alternatives

- **Copy the goto rendering into `ir.rs`** (shape A): two copies of the rules.
- **One renderer: `view.rs` with labels** (shape B): breaks "label = line number", and brings the
  viewer's renamed locals into the debugger, where they must match the detail pane.

## 4. Acceptance criteria

- [ ] A test: 4WHS `Full4WHS`, `PRF.Eval` inlined in a game with `bprf: true`: the listing has a
      `goto end_PRF_Eval;` line and an `end_PRF_Eval:` line, and executed-line highlighting of a path
      that takes the early return paints the `goto` line and not the code after it.
- [ ] A test: `Scheme_KEMDEM.DEC` in kem-dem-cca-blended-parallel: the same, with the label at the
      frame's indentation.
- [ ] A test: a callee without an early return renders as before.
- [ ] `domino html --no-solver` pages are byte-identical before and after (view.rs uses the module).
- [ ] `trace.json` labels still equal line numbers of the listing.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS && $D inline --proof Full4WHS --proofstep <step> --oracle Send2
$D debug --proof Full4WHS --proofstep <step> --oracle Send2 && open <out>/index.html
```
