# Story 81 — Game constants and function parameters in state relations

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** nothing new (independent of 78–80).
**Blocks:** nothing.
**ADR:** 0019 (point 5).
**Decisions:** grilling of 2026-10-20/21, Question 9.

A **translation** story, Rust only. Test-first.

---

## 1. Why this story exists

Merge `3662315a` also gave state relations the new names: the prover binds `left.<X>` for each
constant of the left game instance, and `(left.<f> …)` and `(left.<I>.<f> …)` as `<<func-…>>`
aliases (`smtrewrite.rs`, the equivalence rewrite). The two-sided translation (`build_side_record`,
`invariant.rs`) binds only `left.<I>.<state field>` and `left.<I>.<value param>`.

## 2. Work to do

The game instance is fixed, so no new field (ADR 0019 point 5). In `build_side_record`'s lookup:
- `left.<X>` for a value constant → the instance's binding: the literal, or the theorem constant
  through `lookup.theorem_consts` (the same value as `theorem_const`);
- `(left.<f> a …)` and `(left.<I>.<f> a …)` → `func_op_name(<bound theorem const>) a …`.

The same for `right`, and for the source's own binder names (`state-left.…`, `translate_atom`).

## 3. Tests first

Extend `test-projects/test-game-invariant-consts` (story 80), or a new project if story 81 lands
first, with an equivalence invariant that reads `left.c`, `(right.f …)` and `(left.P.f …)`.

- [ ] `domino prove` accepts the project.
- [ ] Text: `StateRelation_…` has the literal or the theorem constant for `left.c` and the operator
      for the function calls.
- [ ] Compile of the full tree (skips without `easycrypt`).

## 4. Acceptance criteria

- [ ] All tests of §3 green.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
