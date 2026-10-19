# Story 29 — The package tree: one-sided execution of a package oracle with open calls

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 25, EasyCrypt 73, EasyCrypt 75.
**Blocks:** EasyCrypt 76.
**ADR:** 0017 (imports are open calls); 0016 (package-invariant lemmas).
**Decisions:** grilling of 2026-10-12/20, Questions 5 and 5b.

---

## 1. Why this story exists

ADR 0016 proves a package invariant in EasyCrypt as
`hoare[<V>(I).<O> : PkgInv_… ==> res <> None => PkgInv_…]` for every `I <: <V>_Imports {-<V>}`. A
tactics run follows a tree that Domino built (as the side-invariant job follows the side tree of
story 25). A package alone has no tree today.

The owner chose (Question 5) the one-sided walk of story 25, on the **EasyCrypt listing** of the
package oracle alone, with each import call as an **open call**: a fresh value of the import's option
type, so `None` (the import aborted) and `Some v` with any `v`. No virtual package is in the listing,
so the tree has the same shape as the code of the EasyCrypt lemma. Story 75 gives the solver check
the same model (one unknown outcome for each call site).

Vocabulary (`CONTEXT.md`, already updated): **One-sided execution**, **package tree**, **Open call**,
**Package-invariant lemma**.

## 2. Inherited

- Story 25: `src/debug/side.rs` (`run_side`, the one-sided rules), `src/debug/side_run.rs`
  (`free_theorem`, the base frame, `run_side_command`, `one-sided_result.json`, the fingerprint),
  `Level::SideInv` in the debug index, the viewer's one-column mode.
- EasyCrypt 73: named package-invariant claims.
- EasyCrypt 75: the call-result record and the package context with free parameters.

## 3. Work to do

### 3.1 The listing

- The EasyCrypt listing of `<V>.<O>` alone: the package variant's oracle after `EasyCryptTransform`,
  with **no inlining across the import interface**. An import call stays one `Call`-like statement
  of the IR: an **open call**.
- The router prelude and the abort flag are not in the listing: a package has no abort flag (story 04
  of the EasyCrypt epic).

### 3.2 The walk

- The walker takes the **owner of the state**: a composition (story 25) or a package (this story). It
  finds the open calls itself from the package's import interface. No caller passes a flag that says
  "treat calls as open".
- At an open call, the walk binds a fresh symbolic value of the call's option type. The next
  statement is the call-result guard (an exit guard); its two arms are decided by the solver like any
  branch: pruned when infeasible, both walked otherwise.
- The package's parameters are free constants.
- The base frame: the declarations the package check of story 75 uses, and each named package
  invariant on the old state.
- At each terminal that does not abort, check each named invariant on the new state, under
  `no-abort` (the same rule as the side tree). A terminal that aborts has nothing to check.
- Claim names: `package-invariant!<name>!<P>!`, from the owner function (story 74).

### 3.3 Output

- `domino easycrypt debug --pkg-inv <P>` runs each oracle of `P` (or `--oracle O`), for the first
  variant of `P` that the theorem uses. Pages under `<out>/<theorem>/!debug!/PkgInv_<P>/<O>/`, result
  record `one-sided_result.json`, a fingerprint as in story 25 (ADR 0008).
- The debug index gets a level `PkgInv`, and the theorem index one row `pkg-inv  <P>` for each package
  with an invariant, after the side-invariant rows.
- The viewer's one-column mode says "package invariants of `<P>`".

### 3.4 Rejected alternatives

- **Story 25 unchanged on PR 426's virtual game:** the body of `P$Env` would be in the listing and not
  in the EasyCrypt lemma (an alignment mismatch).
- **A flag from the caller to make calls open:** the walker's mode would leak to every caller.

## 4. Acceptance criteria

- [ ] A test fixture: package `Ctr` with a counter invariant and one import; an oracle that only keeps
      the invariant when the import returns `Some`: the tree has a split at the call-result guard,
      the `None` arm aborts with nothing to check, and the `Some` arm verifies.
- [ ] A test: an oracle that breaks the invariant on one path: that terminal's check fails, the others
      verify, and the claim name comes from the owner function.
- [ ] A test: the tree's decision skeleton equals the decision skeleton of `<V>.<O>` in the exported
      `Pkg_<V>.ec` (alignment).
- [ ] A test: the theorem index lists `pkg-inv` rows and links their index.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd test-projects/test-package-invariant-imports
$D easycrypt debug --theorem <theorem> --pkg-inv Ctr && open <out>/<theorem>/!debug!/PkgInv_Ctr/index.html
```
