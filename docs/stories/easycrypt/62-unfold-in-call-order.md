# Story 62 — The invariant's operators are unfolded in call order

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 58, 59.
**Blocks:** 64.

A **bug** story, Rust only. Translation does not change.

---

## 1. Why this story exists

`unfold_premise` (`src/easycrypt/tactics/driver.rs:953`) sends one sentence,
`rewrite /inv /params_inv /StateRelation_… /Helper_… /PkgInv_… in hpre.`, with the operators in the
order of `invariant_ops` (`src/writers/easycrypt/invariant.rs:1013`). `rewrite /a /b in h` unfolds
`a`, then `b`. An operator that is not in `h` at that moment is not unfolded, and EasyCrypt warns
"unused unfold". `invariant_ops` lists the state relations in translation order, and the main
invariant (`StateRelation_invariant`, which calls the others) comes **after** the relations that it
calls. So those relations are never unfolded in the premise.

The transcripts of 2026-10-08 show it: 225 of the 249 premise unfolds have the warning, all of them
in H2_1 ~ H3_0 (13 of 13), H5 ~ H6_0 (13 of 13), H6_1_0 ~ H6_1_1 (78 of 78), H6_1_1 ~ H7_0 (68 of
68) and H7_1_1_0 ~ H7_1_1_1 (53 of 53). Found first in `Eq_H2_1_H3_0_Reproved.md` §2.4.

## 2. Inherited from earlier stories

- **Story 58:** `invariant_ops` is the one owner of the operator names and their order;
  `PkgInv_` wrappers come before their templates.
- **Story 59:** `StateRelation_<r>` for state relations, `Helper_<h>` for other `define-fun`s.
- The side-goal fallbacks 2 and 4 (`try_with_premise`) and the leaf use the same
  `unfold_premise`.

## 3. Work to do

- `invariant_ops` returns the operators in **call order**: an operator comes before every
  operator that its body uses. `inv` and `params_inv` stay first. Build the order from the call
  graph of the invariant file (which `define-fun` / `define-state-relation` body uses which), with
  a stable tie-break (translation order), so the output is deterministic.
- A cycle in the call graph cannot happen in SMT-LIB `define-fun`s. If the graph has one anyway,
  translation fails with an error that names the operators.
- No other change: the sentence stays one `rewrite … in hpre.`

### Rejected alternative

- **Repeat the unfold until nothing changes** (`do rewrite …` or several sentences). Rejected: it
  hides the order in the number of rounds, and costs a round trip each time.

## 4. Acceptance criteria

- [ ] A unit test on an invariant file where `invariant` calls two relations and one relation
      calls a helper: `invariant_ops` gives `inv, params_inv, StateRelation_invariant, …` with each
      caller before its callees.
- [ ] The existing test `invariant_ops_name_the_operators_in_unfold_order_with_their_claims` is
      updated to the new order.
- [ ] In a Full4WHS run of H2_1 ~ H3_0, no premise unfold gets an "unused unfold" message.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --proofstep 4 --tactics
grep -c 'unused unfold' <out>/progress/Eq_H2_1_H3_0/ec-transcript.jsonl   # expect 0
```
