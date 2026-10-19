# Story 75 — Open calls in the solver check of a package invariant

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 74.
**Blocks:** symbolic-execution 29.
**ADR:** 0017 (imports are open calls).
**Decisions:** grilling of 2026-10-12/20, Questions 5 and 5b.

A **Domino core** story (SMT encoding of the package check). Rust only.

---

## 1. Why this story exists

Story 74 brings in PR 426's virtual game: the package next to a virtual package `P$Env` with one
`Bits(*)` state and one uninterpreted function for each import. The owner wants the same freedom with
a simpler model that the debugger and EasyCrypt share (Question 5b, ADR 0017): **each import call
site gets its own unknown outcome**, given to the oracle as an input.

Vocabulary (`CONTEXT.md`, already updated): **Open call** (the old term *virtual package* is in its
_Avoid_ list).

## 2. Inherited

- Story 74: `src/package_invariant/{context,verify,virtualgame}.rs`, `prove --package`, the choice of
  needed packages, the start checks.
- The SMT writer encodes each oracle as a function of the game state and the arguments, and an
  `invoke` as a call to the callee's function.

## 3. Work to do

### 3.1 The call-result record

- For each oracle `O` of package `P`, collect the import call sites of `O` after the transforms
  (`loopunroll` included). Each site has an index in control-flow order.
- Declare a datatype `<P>-<O>-calls` (one per oracle), like the game state: one field for each call
  site, of that call's return type wrapped in `Maybe`. `None` means the import aborted.
- `O`'s SMT function takes one more argument of that type.
- At call site `k`, the call is replaced by reading field `k` of the argument. `None` aborts the
  oracle exactly as an abort of the callee does today (the abort cascade). `Some v` binds `v`.
- An oracle with no import call has no record and no extra argument.

### 3.2 The check

- Each claim (one for each named invariant and each oracle, story 74) and each start check is proved
  for every value of the record: the record is a declared constant, never constrained.
- `virtualgame.rs` is deleted. PR 426's CLI, its choice of packages, its errors and its verify
  driver stay. Where the virtual game reused the theorem machinery (a synthetic `Theorem` with one
  `GameInstance`), build the package context directly instead, with the package's parameters as
  free constants (as symbolic-execution 25's `free_theorem` does for a composition).
- A call site in a loop that `loopunroll` could not unroll is an error with the oracle and the span.

### 3.3 Rejected alternatives (see ADR 0017)

- Keep the virtual package; one uninterpreted function for each import without a state (not sound);
  one argument for each call site (long argument lists).

## 4. Acceptance criteria

- [ ] `rg virtualgame src` finds nothing.
- [ ] The two test projects of story 74 give the same verdicts as before.
- [ ] A new test project: an oracle that calls the same import twice and whose invariant would only
      hold if both calls returned the same value: the check fails. (A model with one function for
      each import and no state would wrongly prove it.)
- [ ] A new test project: an import that aborts: the oracle aborts, and the invariant claim is not
      checked on that path.
- [ ] A test: the SMT file of the check declares one record for each oracle with import calls, with
      one field for each call site in control-flow order.
- [ ] Every known-good example project proves as before.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd test-projects/test-package-invariant-imports && $D prove --package Ctr --transcript
grep -- '-calls' <transcript>
```
