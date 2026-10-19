# Story 73 — Named invariants in EasyCrypt and in the debugger

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 71, 72.
**Blocks:** 74, 76, symbolic-execution 29.
**ADR:** 0018 (invariant operator names).
**Decisions:** grilling of 2026-10-12/20, Questions 3, 3a and 3b.

A **translation, tactics and debugger** story. Rust only.

---

## 1. Why this story exists

Since story 71 an owner can declare several named invariants. The debugger already checks one claim
for each name. EasyCrypt translation still makes one operator for each owner, the conjunction of its
named invariants (story 71 §3.2). Then a leaf part can only belong to the whole package, so an admit
cannot say which invariant fails, and the Domino listing and the EasyCrypt listing name different
checks.

The owner chose one operator and one claim for each named invariant, at every level (Question 3),
with names that are one-to-one without a new language rule (Questions 3a and 3b, ADR 0018).

Vocabulary (`CONTEXT.md`, already updated): **Package invariant**, **Game invariant** (named, several
for each owner), **Leaf part**, **Check**.

## 2. Inherited

- Story 58 and story 69: `PkgInv_<Pkg>` (template, in `Pkg_<V>.ec`), `PkgInv_<C>_<Inst>` and
  `GameInv_<C>` (in `Comp_<C>.ec`), `side_inv_<C>`; the name functions `pkg_inv_template_name`,
  `pkg_inv_op_name`, `game_inv_op_name` (`src/writers/easycrypt/invariant.rs:473-487`);
  `OpRegistry::define_named` and `OpNameCollision`; `InvariantOp { name, claim, relation }`.
- Symbolic-execution 25: the side tree checks with names from the two owner functions.
- Story 71: the owner functions take the invariant name.

## 3. Work to do

### 3.1 The names (ADR 0018)

| Operator | File | Name |
|---|---|---|
| Template | `Pkg_<V>.ec` (first variant of the package) | `PkgInv_<N>_of_<P>` |
| Wrapper for one instance | `Comp_<C>.ec` | `PkgInv_<N>_of_<I>_in_<C>` |
| Game invariant | `Comp_<C>.ec` | `GameInv_<N>_of_<C>` |
| Side invariant | `Comp_<C>.ec` | `side_inv_<C>` (no change) |

- `<N>` is first mapped by `mangle_smt_def_name` (`invariant.rs:1260`). Then, in each part (`<N>`,
  `<P>`, `<I>`), every `_` is written `__`. One function does this escape, and only the three name
  functions call it.
- A reference to another file uses the full name (`Comp_<C>.PkgInv_…`), as today.
- Two invariant names of one owner that `mangle_smt_def_name` cannot tell apart (`my-inv`,
  `my_inv`) stay a hard error (`OpNameCollision`), as for state relations.

### 3.2 Translation

- One template operator for each named package invariant, one wrapper for each named invariant of
  each instance, one game-invariant operator for each named game invariant.
- `side_inv_<C> s = !s.<C>_abort_flag => <every wrapper> /\ <every game invariant>`.
- The unfold order of story 62 (`side_invariant_ops`) lists each named operator.

### 3.3 Claims and leaf parts

- `InvariantOp::claim` of a wrapper is `package_invariant_claim_name(name, C, Inst)`, of a game
  invariant `game_invariant_claim_name(name, C)`. A leaf part that unfolds one of them belongs to that
  named claim, and its admit says, for example, `package invariant main of Prf: unreachable`.
- The side-invariant job (story 69) takes the verdict of that named check from the side tree.

### 3.4 The debugger

- The side tree (symbolic-execution 25) checks each named package invariant of each instance and each
  named game invariant: `package-invariant!<name>!<C>-<Inst>!`, `game-invariant!<name>!<C>!`.
- The viewer and `summary.txt` show the invariant name in each check's label.

### 3.5 Rejected alternatives (see ADR 0018)

- One operator for each owner, the conjunction of its names (story 71's interim shape): Domino gives
  a verdict for each name and EasyCrypt one for each package.
- A flat `_` join with the hard error; `_of_` with a language rule; nested theories; numbers; a
  suffix on a clash.

## 4. Acceptance criteria

- [ ] A test: every name that the three name functions make reads back to its parts, including
      parts with `_`, `__` and a trailing `_`.
- [ ] A test: package `A_B` with invariant `c` and package `A` with invariant `B_c` in one theorem
      give two different template names and two different wrapper names; translation succeeds.
- [ ] A test fixture with a package that has two named invariants: two templates, two wrappers,
      `side_inv_<C>` has both; a path that breaks only the second makes only its leaf part fail, and
      the side tree has that check failing and the other verified.
- [ ] Translation of Full4WHS: every operator is renamed to `PkgInv_main_of_…` / `GameInv_main_of_…`,
      and the exported files compile with every proof admitted.
- [ ] The implementation report gives the admits of `SideInv_H6_*` before and after (they must not
      grow).
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt export --theorem Full4WHS --out /tmp/ec73 --force && cd /tmp/ec73 && easycrypt compile Comp_H6.ec
$D easycrypt debug --theorem Full4WHS --side-inv H6 --oracle Send1
```
