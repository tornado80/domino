# Story 79 — Package parameters and function constants in game invariants

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 78.
**Blocks:** 80.
**ADR:** 0019 (point 2).
**Decisions:** grilling of 2026-10-20/21, Questions 1, 6, 7 and 8.

A **translation** story, Rust only. Test-first.

---

## 1. Why this story exists

The prover binds `game.<Inst>.<param>` in a game invariant (`gen_varbinding`), and
`(game.<fn const> …)` and `(game.<Inst>.<fn param> …)` as `<<func-…>>` aliases
(`generate_func_aliases_game`). Translation binds only `game.<Inst>.<state field>`
(`invariant/side.rs`, `game_lookup`).

## 2. Inherited

- Story 78: `<P>_pkgparams` and the `<C>_params_<I>` fields of `<C>_side`, filled by `side_inv_app`.
- Story 73: `GameInv_<N>_of_<C> (s : <C>_side)`.
- Translation of a composition: each function constant is the operator of the theorem constant
  that the game instance binds it to (`func_op_name`). `discover_compositions` keeps the first game
  instance of each composition, so that binding is the one that `Comp_<C>` uses.

## 3. Work to do

`game_lookup` also maps:
- `game.<I>.<p>` for a value parameter → ``g.`<C>_params_<I>.`<P>_param_<p>``;
- `(game.<I>.<f> a …)` for a function parameter → ``g.`<C>_params_<I>.`<P>_param_<f> a …``;
- `(game.<f> a …)` for a function constant of the composition → `func_op_name(<bound theorem const>) a …`,
  with no new field and no link (ADR 0019 point 2).

`game.<X>` for a value constant is story 80. Until then it stays `Unrecognised`.

## 4. Tests first

New project `test-projects/test-game-invariant-params`: a composition `C` with a value constant
passed to package `P`'s `b` and a function constant passed to `P`'s `f`; a game invariant that reads
`game.P.b`, `(game.P.f …)` and `(game.f …)`.

Write these red first:
- [ ] `domino prove` accepts the project.
- [ ] Text: `GameInv_<N>_of_C` reads ``g.`C_params_P.`P_param_b`` and applies the operator of the
      bound theorem constant for `(game.f …)`.
- [ ] Compile of the full tree (skips without `easycrypt`).
- [ ] A side-invariant job of `C` has 0 admits (skips without `DOMINO_EASYCRYPT`).

## 5. Acceptance criteria

- [ ] All tests of §4 green.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
