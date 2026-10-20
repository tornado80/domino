# Story 80 — Game constants in game invariants (`<C>_const_<X>`, `links_<C>`)

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 79.
**Blocks:** nothing.
**ADR:** 0019 (points 3 and 4); partly supersedes ADR 0014 point 1.
**Decisions:** grilling of 2026-10-20/21, Questions 4, 5 and 8.

A **translation and tactics** story, Rust only. Test-first.

---

## 1. Why this story exists

`easycrypt export` on 4WHS stops with
`unrecognised s-expression in invariant file ./games/H2.comp.smt2: game.bcr`. The prover binds
every composition constant as `game.<X>` (`gen_pkgbinding`, `smtrewrite.rs`). In EasyCrypt a game
constant is in no memory: the router's `init` passes it to the packages and keeps no copy. `H2`
has two game instances that bind `bcr` to `false` and `true`, and a constant `b` that no package
reads.

## 2. Inherited

- Story 78: the `<C>_params_<I>` fields of `<C>_side`.
- Story 79: `game_lookup` for `game.<I>.<p>` and function constants.
- Story 69/77: `SideInv_<C>_<O>`, `SideInvInit_<C>`, `side_inv_<C>`, `game_inv_<C>`, the side
  walk, and the equivalence file that joins `conseq Eq_X_<O> SideInv_<L>_<O> SideInv_<R>_<O>`.
- `game::composition_const_needs_arg`: which constants are `init` arguments.
- `proof::RunArgValue`: a game instance's binding of a constant, as a literal or a theorem constant
  binder.

## 3. Work to do

Only for a composition **with game invariants** (the owner module detects it; no flag leaves it).
A composition with package invariants only does not change.

### 3.1 The fields

`<C>_side` gets `<C>_const_<X> : <ty>` for each constant `X` that is an `init` argument
(`composition_const_needs_arg`), in declaration order, before the abort flag. `game.<X>` →
``g.`<C>_const_<X>``.

### 3.2 The links

`op links_<C> (s : <C>_side) : bool`: one equation for each value parameter `p` of each instance `I`
whose package has a params record:
- bound to constant `X` in the composition → ``s.`<C>_params_<I>.`<P>_param_<p> = s.`<C>_const_<X>``;
- bound to a literal → ``… = <literal>``.

`game_inv_<C> s = links_<C> s /\ GameInv_…`, under the `!abort` guard of `side_inv_<C>`. The side
tree has no Domino verdict for `links_<C>`: oracles never write parameters, so each leaf closes it
like a frame goal. Settle the tactic on the fork with the test project and put it in the report.

### 3.3 The lemmas

- `lemma SideInv_<C>_<O> (x1 … : <ty>) : hoare[… : side_inv_<C> {| …; <C>_const_<X1> = x1; … |} ==> side_inv_<C> {| … same … |}]`.
  The binders are named after the constants, mangled.
- `SideInvInit_<C>`: the same binders, and the precondition fixes the `init` arguments to them;
  the post-state gives `links_<C>` from what `init` stores.
- `SideInv_<C>.ec` joins with the same binders.
- The equivalence file instantiates each side's lemma with that game instance's bindings
  (`RunArgValue`): `SideInv_H2_O false b`.

### 3.4 Rejected alternatives (ADR 0019)

- Map `game.<X>` to the package parameter it is passed to: fails for an unread constant.
- A separate `<C>_consts` argument: two arguments on every operator for no new power.
- Links as an unguarded operator with frame lemmas; links as a precondition only.

## 4. Tests first

New project `test-projects/test-game-invariant-consts`, in the shape of 4WHS `H2`: composition `C`
with `c : Bool` passed to a package's `b`, and `u : Bool` that no package reads; a game invariant
`(=> game.c …)` that reads `game.u` too; game instances `C_0` (`c: false`) and `C_1` (`c: true`);
an equivalence between `C_1` and a second composition.

Write these red first:
- [ ] `domino prove` accepts the project.
- [ ] Text: `C_side` has `C_const_c` and `C_const_u`; `links_C` has `C_params_P.P_param_b = C_const_c`;
      `game_inv_C` starts with `links_C`.
- [ ] Text: `lemma SideInv_C_<O> (c u : bool)`, and `SideInvInit_C` with the same binders.
- [ ] Text: the equivalence file uses `SideInv_C_<O> true <u's binding>`.
- [ ] Text: a composition with package invariants only has no constant field and no `links_`.
- [ ] Compile of the full tree (skips without `easycrypt`).
- [ ] A whole-theorem run has 0 admits (skips without `DOMINO_EASYCRYPT`).

## 5. Acceptance criteria

- [ ] All tests of §4 green.
- [ ] Manual: `easycrypt export` on `~/ec4whs/4WHS` no longer stops at `H2.comp.smt2`; the report
      lists the next error, if one exists.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
