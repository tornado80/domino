# Story 58 — Implementation report: translate package and game invariants

The EasyCrypt `inv` now has the package and game invariants of both sides as conjuncts under
the `!abort` guard (ADR 0010). EasyCrypt-mode lockstep execution checks each one-sided claim as
a sub-verdict of `invariant`, and the tactics driver gives each conjunct the view of its own claim.

## What changed

- **New submodule `src/writers/easycrypt/invariant/side.rs`.** It holds the parser for
  one-sided files (`SideFileParser`), the operator building (`build`) and the new error type
  `SideInvariantError`. `InvariantError::Side` wraps it (transparent).
  - Each package template's files and each composition's files are parsed one time. Across
    all files of one owner there must be exactly one invariant form of its kind.
  - `pkg.<field>` becomes ``s.`<Pkg>_<field>``. `game.<Inst>.<field>` becomes
    ``g.`{l_|r_}pkg_<Inst>.`<Pkg>_<field>``. Only state fields bind. The body uses the existing
    `TCtx` translator with an empty operator registry.
  - Operator order in the file: the `Domino_` operators, then the `PkgInv_<Pkg>` templates, then
    the wrappers (left, then right), then the `GameInv_` operators (left, then right), then
    `params_inv`.
- **`invariant.rs`.**
  - Name helpers next to `pkg_state_type_name`: `pkg_inv_template_name(pkg)` → `PkgInv_<Pkg>`,
    `pkg_inv_op_name(side, inst)` → `PkgInv_<l|r>_<Inst>`, `game_inv_op_name(game_inst)` →
    `GameInv_<GameInst>`.
  - `pkg_state_fields(inst, names)`: the state fields of one instance. `build_side_record` and
    `side.rs` both use it, so the field names have one rule.
  - `OpRegistry::define_named` registers each new name. A collision is
    `SideInvariantError::OpNameCollision`.
  - `inv`: the guarded part is `Domino_invariant l r /\ PkgInv_l_<Inst> l /\ … /\ GameInv_<L> l
    /\ PkgInv_r_<Inst> r /\ … /\ GameInv_<R> r`. Without one-sided invariants, `inv` is the same
    as before, byte for byte.
  - The equivalence parser's `handle_define_package_invariant` / `handle_define_game_invariant`
    give `SideInvariantError::InEquivalenceFile`. `InvariantFile::skipped` no longer names them.
  - `mangle_local_binder` also escapes a binder that would be `s` or `g` (the parameters of
    the new operators). No existing invariant has such a binder, so no golden changed.
  - `pub struct InvariantOp { name, claim: Option<String> }`,
    `pub fn invariant_ops(left, right, relations) -> Vec<InvariantOp>` (order: `inv`,
    `params_inv`, `Domino_<r>`…, wrappers, templates, `GameInv_`…), and
    `pub fn side_invariant_ops(left, right)` (the last three groups). Both read no file.
- **`emit.rs`.** `package_invariant_claim_name(game_inst, pkg_inst)` and
  `game_invariant_claim_name(game_inst)`, re-exported from `writers::smt::contexts`. The
  three `format!` sites of `emit.rs` use them. (`gamehops/equivalence/smtrewrite.rs` still
  has its own two `format!` calls for the `define-fun` names; the story did not ask for that change.)
- **Lockstep.** `LockstepTerms::side_invariants`: on `ClaimSet::NoDependencies`, one goal for
  each claim from `generate_game_or_package_invariant_claims`, without dependencies. The engine
  checks them on every feasible pair, after the relation breakdown, in the same `relations`
  list of `invariant`. On the Domino listing the list is empty. The goal view of the report
  lists them with the relations. `easycrypt_check_names(eqctx)` gives the names of all checks.
- **Fingerprint.** `PARTS` has a fifth part, `claims` (the hash of `easycrypt_check_names`).
  `describe_part("claims")` is `"the claims checked"`. A tree saved before this story is stale,
  and it is still used.
- **Tactics.** `tactics/mod.rs` has no hard-coded operator names: the unfold list comes from
  `invariant_ops`, and `Prover::side_ops` from `side_invariant_ops`. `driver.rs` has
  `Part::SideInvariant { op, claim }` (label `invariant/<op>`). A wrapper or a `GameInv_`
  operator starts that part and is unfolded. A template is unfolded in the part it is in.
  `pair_view` uses only the sub-verdict of `claim`, with the abort rule. If the sub-verdict
  is not there, the view is `Inconclusive`. On an unreachable pair, the `invariant` verdict
  applies.

## Goldens

- New: `testdata/easycrypt/story58/4WHS/Eq_Hybrid1_Hybrid2_Invariants.ec` and
  `Eq_Real_Hybrid3_Ideal_Hybrid3_Invariants.ec`. Each has a compile test.
- Unchanged: `story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec` (byte-identical) and
  `story42/4WHS/Eq_H1_1_H2_0_Invariants.ec`.
- New synthetic project `testdata/easycrypt/story58/`: `OneSided` (package `Ctr` with a package
  invariant, composition `Game` with a game invariant, on both sides) and one theorem for each
  hard error: `HelperFun`, `TwoForms`, `WrongKind`, `Stateless`, `InEquivalence`.

## Tests

- `invariant::side::tests` (10): the 4WHS shapes and goldens, `OneSided`, the five errors
  (each names the file), the name collision, and the order of `invariant_ops`.
- `export::tests::story58_one_sided_full_tree_compiles_in_dependency_order`.
- `tactics::tests::a_one_sided_invariant_part_has_the_view_of_its_own_claim`.
- `tactics::tests::live::a_tree_saved_without_the_claims_part_is_stale_and_still_used`
  (cvc5-lib).
- `lockstep_run::tests::every_pair_has_a_sub_verdict_for_each_one_sided_invariant_claim`
  (cvc5-lib).
- The existing compile tests of Simple4WHS and Full4WHS (full tree in dependency order, base
  cases included) pass with the real `easycrypt` (r2026.09-9-g884dad7).
- `domino easycrypt prove --theorem OneSided`: 1 oracle, 3 goals closed, 0 admits.

## Lockstep time on the synthetic project

`OneSided` `Inc`: 1 joint path. After this story: lockstep 0.0 s, with 4 more solver checks
on the pair (the four one-sided claims). The time before this story was not measured. With one
joint path both times are below the 0.1 s resolution of the report.

## Left open

- **Owner-run** (overview §7): a tactics run on `Simple4WHS` `Hybrid1 ~ Hybrid2`. Compare
  with the oracles it proved before. Record the leaves that admit a `PkgInv_`/`GameInv_` part,
  their Domino views, and the lockstep time before and after.
- Story 21 §3.3 later changes when the sub-verdicts are checked (see the note in §3.7 of the
  story).
