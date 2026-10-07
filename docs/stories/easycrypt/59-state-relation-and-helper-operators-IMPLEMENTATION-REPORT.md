# Story 59 — Implementation report: `StateRelation_` and `Helper_` operators

The translator now gives a `define-state-relation` the prefix `StateRelation_` and every other
`define-fun` of the invariant file the prefix `Helper_`. The prefix `Domino_` is gone. The tactics
driver finds a state-relation part by its `invariant_ops` entry, not by a string prefix. A helper
is unfolded and stays inside the part that contains it.

## What changed

- **`src/writers/easycrypt/invariant.rs`.**
  - The two name rules replace `relation_op_name`:
    `state_relation_op_name(raw)` → `StateRelation_<mangled>` and
    `helper_op_name(raw)` → `Helper_<mangled>`.
  - A private `DefKind { StateRelation, Helper }` selects the rule. `OpRegistry::define` takes
    it. `handle_define_state_relation` gives `StateRelation`, `handle_definefun` gives `Helper`.
    The collision rules of story 58 are the same.
  - `InvariantFile::helpers`: the SMT names of the translated helper `define-fun`s, file order.
  - `InvariantOp` has a new field `relation: Option<String>`: the raw SMT name, for a
    `StateRelation_` operator only.
  - `invariant_ops(left, right, relations, helpers)`: `inv`, `params_inv`, then the new
    `leaf_part_ops(left, right, relations, helpers)`: the `StateRelation_` operators, the
    `Helper_` operators, then `side_invariant_ops`.
- **Plumbing of the helper names.** `EquivalenceReport::helpers` (`export.rs`),
  `WalkedTree::helpers` (`tactics/mod.rs`) and `SavedTree::helpers` (`job.rs`,
  `#[serde(default)]`, so a tree saved before this story reads with no helpers).
- **Tactics driver (`tactics/driver.rs`).**
  - `Prover::side_ops` is now `Prover::part_ops` (from `leaf_part_ops`).
  - The step choice of `solve_ambient` is the pure function
    `ambient_step(goal, part, part_ops) -> (Step, Part)`; `Step` is at module level.
    `part_of_op(op)` gives `Part::Relation(raw)` for an operator with `relation`,
    `Part::SideInvariant` for an operator with `claim`, else `None` (the operator stays in the
    current part). A `Helper_` operator was an atom before; now it is unfolded.
  - `Part::Relation` holds the raw SMT name. Its claim label is
    `invariant/StateRelation_<mangled>`, so the admit comment is
    `(* domino: J7 invariant/StateRelation_rel_keys; … *)`.
  - Doc comments in `goals.rs`, `driver.rs`, `job.rs` and `mod.rs` use the new names.
- **Debug page (§3.4).** `lockstep_run.rs` takes the part names from `state_relation_op_name`,
  so the Verdicts renderer shows `StateRelation_<name>` on the EasyCrypt listing. The page has
  no prefix rule.
- **Fingerprint.** No code change. The `claims` part hashes `easycrypt_check_names`, which now
  has the `StateRelation_` names. Thus a tree saved before this story is stale (`claims`), and
  it is still used (ADR 0008).

## Goldens and documents

- Regenerated with `domino easycrypt export` on `example-projects/4WHS` (`Simple4WHS`,
  `Full4WHS`). The only differences are the operator names:
  `story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec`, `story42/4WHS/Eq_H1_1_H2_0_Invariants.ec`,
  `story58/4WHS/Eq_Hybrid1_Hybrid2_Invariants.ec`,
  `story58/4WHS/Eq_Real_Hybrid3_Ideal_Hybrid3_Invariants.ec` (13 `Helper_` operators and
  `StateRelation_invariant`).
- `story27/kem_dem_tactics_report.txt` is a recorded run (no test reads it). Its two
  `Domino_invariant` names are changed by text, not by a new run.
- New synthetic theorem `testdata/easycrypt/story42/params/theorem/ParamsHelper.ssp` with
  `invariant-helper.smt2`: one helper `define-fun same-bit` and one `define-state-relation
  invariant` that calls it.
- `docs/easycrypt-export.md` and `00-overview.md` (an amendment on the Invariants row, and the
  story 47 line) use the new names. Old stories and reports are not changed.
- The `Leaf part` hunk of `CONTEXT.md` is not part of this story and is not committed.

## Tests

- `invariant::tests::a_state_relation_and_a_helper_get_their_own_prefixes` (also asserts that
  `Domino_` is gone) and `a_state_relation_and_a_helper_compile` (real `easycrypt`).
- `invariant::side::tests::invariant_ops_name_the_operators_in_unfold_order_with_their_claims`:
  now with a helper and the `relation` field.
- `tactics::tests::a_state_relation_starts_a_part_and_a_helper_stays_inside_one`: a leaf
  `StateRelation_a l r /\ Helper_h x` gives one `Part::Relation("a")`; the helper is unfolded
  in `Whole`, `Invariant` and `Relation("a")` and keeps that part.
- `tactics::tests::live::a_tree_saved_before_the_state_relation_names_is_stale_and_still_used`
  (cvc5-lib, needs `DOMINO_EASYCRYPT`).

Results:

- `cargo test --workspace`: 675 passed, 0 failed, 5 ignored in the main crate (baseline 672);
  all other suites pass.
- `cargo test --workspace --features domino/cvc5-lib`: 786 passed, 0 failed, 6 ignored
  (baseline 782).
- With `DOMINO_EASYCRYPT=easycrypt/_build/default/src/ec.exe` and cvc5-lib, the filters
  `easycrypt::`, `writers::easycrypt` and `debug::`: 642 passed, 0 failed.
- `cargo clippy --workspace --all-targets`, with and without `--features domino/cvc5-lib`: no
  warnings.
- `grep -rn 'Domino_' src testdata`: only the new test that asserts that the old name is gone.

## Open items

- **Owner-run (overview §7):** a tactics run on `Simple4WHS` `Hybrid1 ~ Hybrid2` must prove at
  least the oracles it proved before this story. Not done by this session.
- A `Helper_` operator is now unfolded where it was an atom before. On `Real_Hybrid3 ~
  Ideal_Hybrid3` (13 helpers) this can change the time of the leaf closing. The owner run
  shows the effect.
- Existing export trees need `--force` to be written again (ADR 0004).
