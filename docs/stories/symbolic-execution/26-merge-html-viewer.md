# Story 26 — Merge `amir/html-viewer`: the `domino html` proof viewer

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** EasyCrypt 71.
**Blocks:** 27, EasyCrypt 74.
**Decisions:** grilling of 2026-10-12/20, Question 1.

A **merge** story. It only makes the branch build and pass its tests, with the smallest changes that
the merge needs. Stories 27 and 28 take the viewer's inlining ideas into the debugger.

---

## 1. Why this story exists

Branch `amir/html-viewer` (same tip on `domino-repo` and `myorigin`: `6746b2e9`) forked from this
epic's lineage before story 19 landed here. It has 11 commits that HEAD does not have:

| Commit | What |
|---|---|
| `64c3fe69` | its own copy of story 18 (symbolic return value and new state per path) |
| `b2acefd2` | `domino html`: a per-theorem proof viewer |
| `2fcde2fc`, `7361066c`, `0c3475e8`, `d7416848` | colours for Boolean parameters, frames for assumption packages, readable specialized inlining (`src/debug/view.rs`) |
| `33998950`, `a4702e97`, `4e4677e9` | hybrid game hops in the viewer, and fixes for hybrid hops |
| `0db5c7ff`, `ab1140a2`, `6746b2e9` | early returns as `goto`, no dead code after a return |

Its documents are `docs/stories/19-html-*-IMPLEMENTATION-REPORT.md`. The number 19 is already used
in this epic (`19-all-claim-runs-and-strategy-split.md`).

## 2. Work to do

### 2.1 The merge

`git merge domino-repo/amir/html-viewer`. Conflicts against HEAD (2026-10-13): `crates/domino/src/cli.rs`,
`crates/domino/src/main.rs`, `src/debug/{driver,exec,mod,progress,report}.rs`,
`src/transforms/theorem_transforms.rs`, `src/writers/mod.rs`. Story 71 changes some of these again;
check after it.

### 2.2 Rules for the resolution

- **Story 18: keep HEAD's version.** HEAD already has story 18 and its report. Where `64c3fe69`
  differs, keep HEAD, unless a later commit of the branch needs the branch's form. Then take the
  smallest part of it and say so in the report.
- **`src/debug/view.rs` and `src/writers/html.rs` come in unchanged.** `ViewTransform` and
  `PipelineOptions::split_temporaries` come in. The debugger's `ir.rs` keeps its own renderer
  (story 27 changes that).
- **The `html` subcommand** comes in as it is.
- **Documents:** move the five reports to `docs/stories/symbolic-execution/` and rename them
  `26-html-*-IMPLEMENTATION-REPORT.md`. Add one line at the top of each: "Landed in this epic as
  story 26 (merge); written on `amir/html-viewer` as story 19."
- **Hybrid hop fixes** (`src/gamehops/hybrid.rs`, `src/parser/theorem.rs`, `src/proof.rs`): keep
  them, and run the hybrid example projects.

### 2.3 Rejected alternatives

- **Rebase the 11 commits on HEAD:** rewrites a branch that is on two remotes.
- **One merge with the other branches** (Question 1): no way to find which branch broke a test.

## 3. Acceptance criteria

- [ ] One merge commit of `amir/html-viewer` (`6746b2e9`).
- [ ] `domino html` runs on every known-good example project with `--no-solver`, and the pages are
      byte-identical to the pages from the branch's own binary.
- [ ] `domino debug`, `domino inline` and `domino easycrypt debug` give the same output as before
      the merge on 4WHS Simple4WHS (listings, `trace.json`, `summary.txt`).
- [ ] The five reports are in `docs/stories/symbolic-execution/` under number 26.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 4. How to verify

```bash
cargo test --workspace
cd example-projects/4WHS && $D html --no-solver && $D inline --proof Simple4WHS --proofstep 0 --oracle Send1
```
