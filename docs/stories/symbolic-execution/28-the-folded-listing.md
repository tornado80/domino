# Story 28 — The folded listing: hide trivial branches in the debugger and in `domino inline`

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 27.
**Blocks:** nothing.
**Decisions:** grilling of 2026-10-12/20, Questions 9 (shape C) and 10 (A).

A **listing and viewer** story. Rust and the viewer's HTML/JS. The executor does not change.

---

## 1. Why this story exists

The HTML viewer (story 26) folds constants: it drops a branch whose condition is `false` and puts
the body of a branch whose condition is `true` in its place. The owner wants the same in the
debugger pages and in `domino inline`, as a choice: a checkbox on the debugger pages and an option
on the CLI.

Folding is a **view, not other code** (Question 9). The executor always walks the full IR. The
folded listing is a second rendering of the same IR, and each of its lines points back to the line
of the full listing it comes from.

Vocabulary (`CONTEXT.md`, already updated): **Trivial branch**, **Folded listing**, **Exit guard**.

## 2. Decisions (Question 10)

- The toggle is on **both** listings, the Domino listing and the EasyCrypt listing.
- **Exit guards are never folded.** On the EasyCrypt listing the done-flag guard has the literal
  condition `true` (`ExitGuard::DoneFlag`), but EasyCrypt has to step over it. Only a branch with
  `exit_guard: None` can be trivial.
- The default is the **full** listing. The checkbox "hide trivial branches" switches the view, and
  the page remembers the choice for each viewer in local storage (wrapped in `try`/`catch`; the page
  works without it).
- `domino inline` gets `--fold-trivial-branches`, off by default.
- `domino html` keeps folding always, as now.

## 3. Work to do

### 3.1 Which constants fold

- A lockstep run and `domino inline` have a game instance: its constants fold.
- A side tree (symbolic-execution 25) and a package tree (symbolic-execution 29) have free
  parameters: only the literals `true` and `false` fold.
- The rule is the one of story 27's module (`Some(true)` / `Some(false)` / `None`).

### 3.2 The folded rendering

- `ir.rs` renders the IR a second time with folding on. A trivial `false` branch prints nothing; a
  trivial `true` branch prints its body at the branch's indentation, with no braces.
- The folded rendering has a **line map**: for each folded line, the label (full-listing line) it
  comes from. Lines that exist only in the folded view do not exist; every folded line has a label.
- A label with no folded line (the branch line of a trivial branch) maps to the first visible line
  after it. The viewer shows the decision of that branch on that line.

### 3.3 The debugger pages

- The page carries both listings and the line map. The checkbox switches the listing shown.
- Executed-line highlighting, the path tree and the detail pane use the line map in the folded view,
  so a path paints the same statements in both views.
- `trace.json` keeps full-listing labels only. Bump `TRACE_SCHEMA` if the page data changes.

### 3.4 `domino inline`

- `--fold-trivial-branches` prints the folded listing for both sides. Without it, output is as in
  story 27.

### 3.5 Rejected alternatives

- **Folded by default everywhere** (Question 10, B): a first look at a failing path can hide the
  branch it refers to.
- **Folding only on the Domino listing** (Question 10, C): branches that come from Domino code can be
  trivial on the EasyCrypt listing too.
- **Execute the folded IR**: two IRs whose labels differ; every artifact would need to say which.

## 4. Acceptance criteria

- [ ] A test: 4WHS `Hybrid2` (`b: false`), `Prf.Eval`: the folded listing has no ideal branch; the
      full listing has it; each folded line maps to a label of the full listing.
- [ ] A test: on the EasyCrypt listing, done-flag guards are present in the folded view.
- [ ] A test: a side tree with a free parameter folds nothing but literal conditions.
- [ ] A test: `domino inline --fold-trivial-branches` output equals the folded rendering; without the
      option the output equals story 27's.
- [ ] The viewer: the checkbox switches the listing, highlighting matches in both views, the choice
      survives a reload, and the page works with local storage blocked. Check it in a browser and
      put screenshots in `28-screenshots/`.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS && $D inline --proof Simple4WHS --proofstep <step> --oracle Send2 --fold-trivial-branches
$D debug --proof Simple4WHS --proofstep <step> --oracle Send2 && open <out>/index.html
```
