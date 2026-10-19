# Story 77 — Side invariants built from package lemmas; the game-invariant start lemma

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 76.
**Blocks:** nothing.
**ADR:** 0016 (partly supersedes 0014).
**Decisions:** grilling of 2026-10-12/20, Questions 4, 6 and 11.

A **translation, tactics, debugger and CLI** story, Rust only.

---

## 1. Why this story exists

After story 76 every package has its package-invariant, frame and start lemmas. `SideInv_<C>_<O>`
(story 69) still proves the package invariants of `C`'s instances by walking the composition's oracle.
ADR 0016 says that it gets them from the package lemmas instead, and walks only for the game
invariants. The owner also wants a start lemma for game invariants (Question 6).

## 2. Inherited

- Story 69: `SideInv_<C>_<O>.ec`, `SideInv_<C>.ec`, `side_inv_<C>`, the side-invariant job, the
  `prove` planning (`plan_run`).
- Story 73: `PkgInv_<N>_of_<I>_in_<C>` wrappers and `GameInv_<N>_of_<C>`.
- Story 76: `PkgInv_<V>_<O>`, `Frame_<V>_<O>`, `PkgInv_<V>_init`, the package-invariant job.
- Symbolic-execution 25: the side tree.

## 3. Work to do

### 3.1 The proof of `SideInv_<C>_<O>`

The statement does not change. The proof:

1. Split `side_inv_<C>` into one hoare goal for each wrapper and one for the game invariants
   (`conseq` with the conjunction of hoare lemmas, as the glue does with `conseq`).
2. For each instance `X` with invariants, bottom-up along the call graph (it is acyclic):
   - if `X` defines the oracle that the router calls for `O`, apply `PkgInv_<V_X>_<O'>` with `I` set
     to `X`'s import provider (an instance or an import adapter of `C`);
   - if `X` is called through another instance `Y`, apply `Frame_<V_Y>_<O''>` with
     `J` set to `X`'s wrapper (and the wrappers of the instances below `X`), and discharge its axioms
     with `X`'s package-invariant lemmas;
   - an instance that `O` never reaches keeps its invariant because nothing writes its state.
3. The game invariants: walk the side tree as story 69 does.

The proof of steps 1–2 is generated from the call graph, not from a tree. Settle the exact tactic
sequence on the fork with a hand-written two-package example first, and put it in the report.

### 3.2 The side tree checks only game invariants

- Story 25's side tree no longer checks package invariants. The base frame still assumes them on the
  old state.
- A composition with no game invariant needs no side tree and no walk: `SideInv_<C>_<O>` is proved by
  steps 1–2 only.

### 3.3 The game-invariant start lemma

`SideInvInit_<C>.ec`: `hoare[Game_<C>.init : true ==> GameInv_<N>_of_<C> {| … |} /\ …]`. The
side-invariant job proves it. Its Domino verdict is the game invariant's start check. `inv` gets no
start lemma: the main lemma's `last first` goal proves it (ADR 0016 point 4).

### 3.4 Jobs and the whole-theorem run

- A side-invariant job of `C` checks that `PkgInv_<V>.ec` and its oracle files are on disk for every
  variant of an instance of `C`. A file with admits counts. If one is missing, the composition does
  not start, and the job warns: `package invariants of <P> are not proved: run prove --pkg-inv <P> first`.
- A whole-theorem run starts the package-invariant jobs first. Each side-invariant job waits only for
  the packages of its own composition. Proof jobs start at once (oracle lemmas need neither).

### 3.5 Rejected alternatives (see ADR 0016)

- Re-walk each caller in each composition; a combined lemma with `J`; a side-invariant job that proves
  package lemmas.

## 4. Acceptance criteria

- [ ] The report shows the hand-written two-package `SideInv` proof from package and frame lemmas that
      compiles on the fork (§3.1).
- [ ] Translation of Full4WHS: every `SideInv_<C>_<O>` proof uses the package lemmas and walks only for
      game invariants; with the package lemmas admitted, each `SideInv_<C>.ec` compiles.
- [ ] A test: a side tree of a composition with package invariants and no game invariant is not run.
- [ ] A test: `prove --side-inv C` with a missing package file does not start and prints the warning.
- [ ] A test: a whole-theorem run starts a package job before the side job that needs it, and a proof
      job at once.
- [ ] The report gives, for H6 on Full4WHS, the admits and wall time of `SideInv_H6_*` before and after.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --pkg-inv PRF --tactics
$D easycrypt prove --theorem Full4WHS --side-inv H6 --tactics --jobs 4
```
