# Story 74 — Merge `amir/check-package-invariants-once` (PR 426): package invariants are checked once

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 72, 73, symbolic-execution 26 (merge order).
**Blocks:** 75.
**Decisions:** grilling of 2026-10-12/20, Questions 1 and 7.

A **merge** story, with the adaptation that the merge needs. Story 75 replaces its virtual game.

---

## 1. Why this story exists

PR 426 (draft, `f7496a61`, one commit "feat: check package invariants once", based on `main` of
2026-09-03) checks each package invariant once for each package instead of once for each instance in
each game of each equivalence:

- `src/package_invariant/` (new): `context.rs`, `error.rs`, `verify.rs`, `virtualgame.rs`. The
  package is put next to a virtual package `P$Env` and checked for arbitrary package parameters:
  *invariant start* (the invariant holds in the initial state) and one claim for each oracle.
- `src/writers/smt/contexts/game_defs.rs` (new): game definitions moved out of `emit.rs`.
- `verify_fn.rs`: the package-invariant claims and their start checks are removed from every
  equivalence. Game invariants stay.
- `src/project/mod.rs`: a `prove` run finds which packages the theorem needs and checks each once.
  It skips theorems with only reduction hops, and the case where a proofstep and `--oracle` are both
  given.
- CLI: `domino prove --package <P>` (only that package; not with `--proof` or `--proofstep`);
  `--oracle` limits it; `--invariant-start` also limits package invariants to their start.
- Test projects `test-package-invariant` and `test-package-invariant-imports`.

The owner wants it merged last of the three branches (Question 1), on top of named invariants
(story 71), resolved claim kinds (story 72) and named operators (story 73).

## 2. Work to do

### 2.1 The merge

`git merge domino-repo/amir/check-package-invariants-once`. Conflicts against HEAD (2026-10-13):
`crates/domino/src/{cli,main}.rs`, `src/gamehops/equivalence/{mod,smtrewrite,verify_fn}.rs`,
`src/project/error.rs`, `src/transforms/theorem_transforms.rs`,
`src/writers/smt/contexts/equivalence.rs`, `src/writers/smt/contexts/equivalence/emit.rs`.
Stories 71–73 change these files again; expect more.

### 2.2 Adaptation

- **Named invariants:** the package check makes one claim for each named invariant of the package,
  for each oracle, and one start check for each. Names come from the owner functions of story 71,
  with the package as the owner: `package-invariant!<name>!<P>!` (one owner function; extend it so
  that it can take a package with no instance).
- **Resolved claims:** the package check builds `ResolvedClaim`s with `ClaimKind::PackageInvariant`
  (story 72). No name lookup.
- **The debugger:** an equivalence no longer has package-invariant claims. The core claim set
  (symbolic-execution 23) and the all-claim run lose them. The base frame still assumes each package
  invariant on the old state. The side tree (symbolic-execution 25) keeps its package-invariant
  checks until story 77.
- **EasyCrypt:** no change. The EasyCrypt `invariant` check already has no package claims (story 69).
- **The virtual game stays as it is** in this story. Story 75 replaces it (ADR 0017).
- Keep `--package`, `--oracle` and `--invariant-start` as PR 426 defines them, on the CLI words of
  `main` (`--proof`, `--proofstep`; Question 7).

### 2.3 Rejected alternatives

- **Rewrite PR 426 before the merge** (open calls first): the merge would then mix the port and the
  new model; one story each keeps each change reviewable.

## 3. Acceptance criteria

- [ ] One merge commit of `f7496a61`.
- [ ] `domino prove --package Ctr` on both new test projects gives the verdicts that PR 426 gives on
      its own branch, with one claim for each named invariant.
- [ ] A test: an equivalence's claim set has no package-invariant claim; its base frame assumes them.
- [ ] A test: a whole-theorem `prove` checks each needed package once, even when several game
      instances use it.
- [ ] Every known-good example project proves as before.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 4. How to verify

```bash
cd test-projects/test-package-invariant-imports && $D prove --package Ctr
cd example-projects/4WHS && $D prove --proof Simple4WHS
```
