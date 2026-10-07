# Story 59 — `StateRelation_` and `Helper_` operators replace `Domino_`

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 58 (`invariant_ops`, the one owner of the operator names); symbolic-execution 21
(the tactics run takes its state relations from the translation, not from the debug check list).
**Blocks:** nothing.

---

## 1. Why this story exists

The owner said: *"I think `Domino_rel` should be `StateRelation_rel`."*

Today `relation_op_name` (`src/writers/easycrypt/invariant.rs`) gives the prefix `Domino_` to
**every** `define-fun` and `define-state-relation` of the equivalence's invariant file. These are
two kinds of operator:

- a **state relation** (a predicate over the left and right states), and
- a **helper function** (any other function of the file).

The tactics driver reads every operator that starts with `Domino_` as a state-relation part
(`Part::Relation`, `src/easycrypt/tactics/driver.rs`). So a helper that is a conjunct of a leaf is
wrongly read as a state relation, and gets the verdict of a state relation of that name, or of
`invariant`. The prefix also does not say what the operator is. Story 58 named the new one-sided
operators `PkgInv_` and `GameInv_` for the same reason.

Vocabulary (`CONTEXT.md`): **`StateRelation_` operator**, **`Helper_` operator**, **State
relation**, **Invariant**, **Check**.

## 2. Inherited from earlier stories

- **Story 53:** `relation_op_name` is the one rule for the operator name, and the tactics run
  uses it to unfold.
- **Story 58:** `invariant_ops(left, right, relations)` lists every operator of the invariant file
  in unfold order, with the claim each one stands for. `PkgInv_` and `GameInv_` are registered in
  `OpRegistry`. The tactics module has no hard-coded operator names.
- **Symbolic-execution 21:** the tactics run takes the names of the state relations from the
  translation, not from the debug check list. On the EasyCrypt listing, the debug pages name a
  state-relation check by its EasyCrypt operator.

## 3. Work to do

### 3.1 Two name rules

Replace `relation_op_name` with two functions, next to the `PkgInv_` / `GameInv_` helpers:

```rust
/// `define-state-relation` / a `define-fun` that is a state relation → `StateRelation_<mangled>`.
pub(crate) fn state_relation_op_name(raw: &str) -> String
/// any other `define-fun` of the invariant file → `Helper_<mangled>`.
pub(crate) fn helper_op_name(raw: &str) -> String
```

The translator decides the kind from the SMT statement kind (`SmtStatementKind::StateRelation`
is a state relation; every other `define-fun` is a helper). The invariant is then
`StateRelation_invariant`. `inv` uses it inside the `!abort` guard.

Register both prefixes in `OpRegistry`. The collision rules of story 58 still hold.

### 3.2 `invariant_ops`

`invariant_ops` lists `StateRelation_<r>` operators and `Helper_<h>` operators in the place of
the `Domino_` operators, state relations first. Helpers are unfolded too, so that a solver sees
through them.

### 3.3 The tactics driver

- A leaf part that is an application of a `StateRelation_<r>` operator becomes
  `Part::Relation(r)`. Find it by the `invariant_ops` entry, not by a string prefix in the driver.
- A `Helper_<h>` application is **never** a part of its own. It is unfolded and stays inside the
  part that contains it.
- The claim label of a state-relation part becomes `invariant/StateRelation_<r>`. The admit
  comment changes the same way (`(* domino: J7 invariant/StateRelation_rel_keys; … *)`).
- Change the doc comments in `goals.rs`, `driver.rs`, `job.rs` and `mod.rs` that name `Domino_`.

### 3.4 The debug page on the EasyCrypt listing

The shared Verdicts renderer of story 21 shows `StateRelation_<name>` for a state-relation check
on the EasyCrypt listing. It reads the name from the run's metadata, not from a prefix rule in the
page.

### 3.5 Goldens and documents

- Regenerate every golden that holds `Domino_` (`testdata/easycrypt/story06/…`,
  `testdata/easycrypt/story42/…`, `testdata/easycrypt/story27/kem_dem_tactics_report.txt`, and the
  goldens of story 58).
- `docs/easycrypt-export.md` and the overview: use the new names. Old stories and implementation
  reports stay as they are.
- `CONTEXT.md` already has the two new terms.

## 4. Acceptance criteria

- [ ] `grep -rn 'Domino_' src testdata` finds nothing, except a test that asserts the old name is
      gone.
- [ ] For `Simple4WHS`, `Eq_Hybrid1_Hybrid2_Invariants.ec` has `op StateRelation_invariant`, and
      `inv` uses it inside the `!abort` guard.
- [ ] A synthetic invariant file with one state relation and one helper `define-fun` translates to
      one `StateRelation_` and one `Helper_` operator, and both compile in EasyCrypt.
- [ ] A unit test of the driver: a leaf whose conjuncts are `StateRelation_a l r` and
      `Helper_h x` gives one `Part::Relation("a")`, and the helper is unfolded inside a part, never
      a part of its own.
- [ ] The goldens are regenerated, and the EasyCrypt compile tests pass.
- [ ] A saved joint tree from before this story is reported as stale and still used (ADR 0008).
- [ ] **Owner-run, not by the implementing session** (overview §7): a tactics run on `Simple4WHS`
      `Hybrid1 ~ Hybrid2` proves at least the oracles it proved before this story.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt export --theorem Simple4WHS --force
grep -n '^op StateRelation_\|^op Helper_\|Domino_' <out>/*/Eq_Hybrid1_Hybrid2_Invariants.ec
grep -A12 '^op inv' <out>/*/Eq_Hybrid1_Hybrid2_Invariants.ec
```

## 6. Rejected alternatives

- **`StateRelation_` for every `define-fun`, helpers too.** Rejected: a helper then has a false
  name, and the driver still reads it as a state relation.
- **`StateRelation_` for state relations, `Domino_` for helpers.** Rejected: `Domino_` would then
  mean "a helper", which the word does not say.
- **Keep `Domino_`.** Rejected: the prefix does not tell the kind, and helpers are misread.

## 7. Notes / risks

- Existing export trees need `--force` to be written again (ADR 0004).
- The fingerprint of saved joint trees includes the invariant part, so old trees become stale.
  ADR 0008 still applies: they are used, with a warning.

## 8. State handed to the next story

Record in `59-…-IMPLEMENTATION-REPORT.md`: the two name helpers, the goldens regenerated, and the
owner-run check left unchecked.
