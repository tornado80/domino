# Story 62 — Implementation report: the invariant's operators are unfolded in call order

Rust only. The translation and the sentence (one `rewrite … in hpre.`) do not change.

## What changed

- **`invariant.rs`, the writer.** For each translated `define-fun` and `define-state-relation`,
  `called_defs` records the raw names of the earlier definitions that its body uses (every atom
  that names a registered definition). `call_order` sorts the names: each caller comes before
  its callees, and among ready names the earlier one in translation order comes first.
  `InvariantFile::state_relations` and `InvariantFile::helpers` are now in call order.
- **Cycle.** A cycle gives `InvariantError::CallCycle { names }` ("the invariant definitions a,
  b call each other in a cycle"). SMT-LIB cannot give one, because a body can only call an
  earlier definition; the error is a guard.
- **`invariant_ops` / `leaf_part_ops`** do not change their logic. They keep the order they get,
  and their doc says the lists must be in call order. The relations come before the helpers.
  This is a call order of all of them, because a helper cannot take a state sort
  (`translate_sort` has no state sort), so it never calls a relation.

### Rejected shape

One combined `definitions` list with a kind on each entry. It is a more general order, but it
changes `job.rs`, the saved joint trees and the tactics run. The two lists are sufficient
because of the rule above.

## Tests

- `invariant_ops_put_each_caller_before_its_callees`: a new fixture
  (`testdata/easycrypt/story42/params/theorem/ParamsCallOrder.ssp`,
  `invariant-call-order.smt2`). `invariant` calls two relations, one relation calls a helper,
  one helper calls another. The result is `inv, params_inv, StateRelation_invariant,
  StateRelation_plain_rel, StateRelation_bit_rel, Helper_outer_bit, Helper_inner_bit`.
- `call_order_keeps_translation_order_between_unrelated_definitions`,
  `a_call_cycle_is_an_error_that_names_the_definitions`.
- `invariant_ops_name_the_operators_in_unfold_order_with_their_claims` (side.rs): the input
  now starts with `invariant`, in call order, and the test says that `invariant_ops` keeps the
  order.
- `cargo test --lib`: 680 passed, 5 ignored. `cargo clippy --workspace --all-targets`: clean.
  `cargo build --release --workspace`: OK.

## Not done

- The Full4WHS check (story 62 §5, no "unused unfold" in H2_1 ~ H3_0) was not run: the owner
  asked for no EasyCrypt proof runs in this session.
- `--features cvc5-lib` builds were not run.
- A joint tree saved before this story keeps its old relation order on resume. A new
  translation gives the new order.
- The CRAP gate was not measured (`sdlc` is not available here). By inspection, `call_order`
  and `called_defs` each have CC below 6.
