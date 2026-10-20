# Invariants take parameters as a second record; game constants are fields linked to them

**Status:** accepted. Partly supersedes ADR 0014 (point 1, "the lemmas say nothing about the
composition's parameters"). Implemented by `docs/stories/easycrypt/78-package-parameters-in-package-invariants.md`,
`79-package-parameters-in-game-invariants.md`, `80-game-constants-in-game-invariants.md` and
`81-game-constants-in-state-relations.md`. Grilling of 2026-10-20/21, Questions 1–9.

Merge `3662315a` (2026-10-07) brought main's SMT rewrite into this branch. Since then the prover
binds more names in an invariant file than state fields: `pkg.<param>` in a package invariant,
`game.<const>` and `game.<Inst>.<param>` in a game invariant, `left.<const>` and
`left.<Inst>.<param>` in a state relation, and function constants and parameters as
`<<func-…>>` aliases (`smtrewrite.rs`, `gen_pkgbinding`, `gen_varbinding`,
`generate_func_aliases_*`). Story 58 recorded on 2026-10-06 that "`pkg.<name>` binds only the state
fields", which was true before the merge, and ADR 0014 used that fact. Translation was not changed,
so `easycrypt export` stops with "unrecognised s-expression" on 4WHS `H2.comp.smt2` (`game.bcr`).
No decision left these names out.

In EasyCrypt a package parameter that is not baked into a type (Bool, value Integer) is a module
variable of the package instance, a function parameter is a global operator chosen by the variant,
and a game constant is in **no memory**: the router's `init` passes it to the packages and keeps
no copy.

We decided:

1. **`<Pkg>_pkgparams`**, a record type declared next to `<Pkg>_pkgstate` by the same owner, with
   one field for each parameter that the variant does not bake into a type: Bool, value Integer and
   function parameters. The template becomes `PkgInv_<N>_of_<P> (p : <P>_pkgparams) (s : <P>_pkgstate)`.
   A package without such parameters has no record and keeps one argument. Each variant fills the
   function fields with its own operators, so one template still serves every variant.
   `pkg.<param>` reads `p`.
2. **`<C>_side` gets one `<C>_params_<Inst> : <P>_pkgparams` field for each instance with
   parameters**, read from memory like the state. The wrapper `PkgInv_<N>_of_<Inst>_in_<C>` has no
   memory, so it passes this field to the template. `game.<Inst>.<param>` reads it too.
   `(game.<fn const> …)` is the operator that the composition already uses for that constant.
3. **`<C>_side` gets one `<C>_const_<X>` field for each game constant that is an `init`
   argument**, so `side_inv_<C>` keeps one argument (ADR 0007). `game.<X>` reads it. The value
   comes from a binder of `SideInv_<C>_<O>`, from the `init` argument in `SideInvInit_<C>`, and from
   the game instance's binding (a literal or a theorem constant) in the equivalence.
4. **`links_<C>`**, a conjunct of `game_inv_<C>` under the `!abort` guard: each value parameter
   field equals the game constant or the literal it is bound to in the composition. In SMT this
   holds by definition; in EasyCrypt it is the only thing that relates `game.<X>` to the module
   variable that the code reads. Constant fields and links exist only when the composition has game
   invariants, so a composition with package invariants only does not change.
5. **State relations need no new fields**: the game instance is fixed, so `left.<X>` is its binding
   and `(left.<f> …)` and `(left.<Inst>.<f> …)` are the operator of the bound theorem constant.

## Considered options

- **Map `game.<X>` to the package parameter it is passed to.** Fails for a constant that no package
  reads (4WHS `H2.b`).
- **Parameters as fields of `<Pkg>_pkgstate`.** Breaks *equal state* (`CONTEXT.md`) and puts
  each parameter two times in the two-sided record.
- **One positional template argument for each parameter.** Each new parameter changes every caller.
- **A separate `<C>_consts` argument of `side_inv_<C>`.** A clean memory / logic split, but every
  `GameInv_`, `side_inv_` and `PkgInv_…_in_<C>` operator gets two arguments for no new power.
- **The links as an unguarded operator with a frame lemma for each oracle.** A new lemma kind that
  every composition with constants must prove, also when no invariant reads a constant.
- **The links as a precondition only.** The post-state does not give them back, so a chain of
  oracle calls cannot use them.
- **One template for each variant when the body reads a function parameter**, or an error when the
  variants differ. A hidden mode in the owner rule, or a failure for any project with two PRF
  variants.

## Consequences

- `SideInv_<C>_<O>` and `SideInvInit_<C>` take one binder for each game constant field; the
  equivalence instantiates them. They still hold for every value of the constants, as ADR 0014 wants.
- The two-sided game-state record does not change: its parameter fields stay flat
  (`l_pkg_<Inst>_<param>`).
