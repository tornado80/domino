# Story 25 — One-sided execution: the side tree of one composition oracle

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 19 (all-claim runs), 21 (checks), 22 (debug indexes, `--out`), 23 (core claim set),
EasyCrypt 50 (exit guards), EasyCrypt 58 (package and game invariant claims).
**Blocks:** EasyCrypt 69.
**ADR:** 0014 (side invariants are hoare lemmas of the composition).

---

## 1. Why this story exists

ADR 0014 proves the package and game invariants of a composition as `hoare` lemmas, one for each
oracle, for every value of the composition's parameters. A tactics run follows a tree that Domino
built, the way an equivalence's proof follows lockstep execution's joint tree. A joint tree needs
two oracles, so a composition alone has no tree today, and no verdict for its side invariants.

The owner chose a one-sided execution over a blind walk from EasyCrypt's program shape (grilling of
2026-10-09/12, Question 11): it decides branches in advance, prunes infeasible paths, and gives a
Domino verdict for each admit.

Vocabulary (`CONTEXT.md`, already updated): **One-sided execution**, **side tree**, **Package
invariant**, **Game invariant**, **Check**, **Listing**.

## 2. Inherited from earlier stories

- **Lockstep execution** (EasyCrypt 23, `run_lockstep_command`, `src/debug/lockstep_run.rs:614`):
  walks two oracles on a listing, with a shared base frame and a check at each terminal pair.
- **Story 23:** the core claim set; the package and game invariant claims, with only their
  built-in dependency `no-abort`.
- **EasyCrypt 58:** `package_invariant_claim_name(game_inst, pkg_inst)` and
  `game_invariant_claim_name(game_inst)` (`src/writers/smt/contexts/equivalence/emit.rs:1688`) are
  the one owners of the claim names.
- **ADR 0008:** a saved tree with a fingerprint of what the run read.

## 3. Work to do

### 3.1 The walk

- Input: one composition `C` and one of its oracles `O`, on the **EasyCrypt listing** (the code
  that the side-invariant lemma is about).
- The composition's parameters are **free** constants: no game instance fixes them.
- The base frame holds the old state, the oracle's arguments, and every package invariant of `C`'s
  package instances and `C`'s game invariant on the old state.
- The walk is the one-sided part of lockstep execution: straight-line code up to a decision point,
  then the decision. A branch whose guard the solver decides is **determined**; otherwise both arms
  are explored. Samplings are draws with no pairing. Exit guards are marked as in lockstep
  execution.
- At each terminal that does not abort, the walk checks, under `no-abort`, each package invariant
  (one check for each package instance) and the game invariant on the new state. A terminal that
  aborts has nothing to check (the side invariant is under `!abort`).

### 3.2 Claim names

The checks are named for the composition, not a game instance:
`package-invariant!<C>-<PkgInst>!` and `game-invariant!<C>!`. Change the two owners of the names so
that they take the name of the owner of the state (a composition here, a game instance in lockstep
execution), and keep one owner for each name.

### 3.3 Output

- A **side tree**: nodes, decisions, terminals and the verdict of each check, in the same JSON style
  as the joint tree, with the fingerprint of ADR 0008.
- `domino easycrypt debug --side-inv <C>` runs it for every oracle of `C` (or `--oracle O` for one)
  and writes the debug pages under `!debug!/SideInv_<C>/<O>/`. The joint-tree viewer shows a side
  tree with one column.
- The debug index (story 22) lists the runs at the theorem level.

### 3.4 Rejected alternatives

- **A blind one-sided walk from EasyCrypt's program shape** (the tactics run reads each `if` and
  sends `if.`). No verdicts, no pruning, and every infeasible arm costs a sentence.
- **Lockstep execution of `C` against itself.** Lockstep execution pairs decisions of two sides, so
  every branch would be split four ways, and the claims are about one side.

## 4. Acceptance criteria

- [ ] A test on a small composition with one package invariant that a path breaks: the side tree
      has that terminal's check as failing, and the others as verified.
- [ ] A test: a branch on a parameter is explored both ways (the parameter is free).
- [ ] A test: the claim names are `package-invariant!<C>-<PkgInst>!` and `game-invariant!<C>!`,
      from the one owner of each name. Lockstep execution's names do not change.
- [ ] `domino easycrypt debug --side-inv H6` on Full4WHS writes a side tree for each oracle and
      the viewer opens them.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt debug --theorem Full4WHS --side-inv H6
ls <out>/!debug!/SideInv_H6/
```
