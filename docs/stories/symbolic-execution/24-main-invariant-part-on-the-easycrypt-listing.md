# Story 24 — The main invariant is a part of `invariant` on the EasyCrypt listing

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 21 (`ClaimQuery` with parts, the EasyCrypt-listing parts); EasyCrypt 58 (`inv`
holds the package and game invariants); EasyCrypt 59 (`StateRelation_` operators).
**Blocks:** nothing.

---

## 1. Why this story exists

The owner asked: *"Would the decision change discussed above affect EasyCrypt proving? In
EasyCrypt, we need to prove both the main invariant and game and package invariants. EasyCrypt
debugger needs to prove both as well because they are not all in conjunction in Domino."*

It does. After story 58, the `invariant` check of the EasyCrypt listing has this goal:

```
StateRelation_invariant ∧ PkgInv_<l|r>_<Inst> … ∧ GameInv_<GameInst> …   (on the new states)
```

Story 21 §3.1 gives this check the parts "each `StateRelation_<r>` **except
`StateRelation_invariant`**, then the `PkgInv_` and `GameInv_` operators". That rule is correct on
the Domino listing, where the `invariant` check *is* the main invariant. It is not correct on the
EasyCrypt listing, where the check is the whole conjunction. Thus the main invariant conjunct has
no verdict of its own.

The defect, at HEAD `f2827ce1`:

- `easycrypt_invariant_query` (`src/debug/lockstep_run.rs`) gets its state-relation parts from
  `state_relation_parts` (`src/debug/claims.rs`), which removes `invariant`.
- `easycrypt_check_names` (same file) removes `invariant` in the same way.
- `pair_view` (`src/easycrypt/tactics/driver.rs`) has the special case
  `Part::Relation(name) if name == "invariant" => invariant(claim("invariant"))`. The leaf splitter
  makes this part when it unfolds `StateRelation_invariant`. So this conjunct gets the verdict of
  the **whole** conjunction.

The effect: when only a package or game invariant fails on a pair, the view of the main
invariant conjunct is `Fails` (`Inconclusive` on a pair where a side aborts). §3.6 of the tactics
driver then admits that conjunct with reason `domino-fails` and **no EasyCrypt attempt**, also
when the conjunct is provable. This is the "worst verdict" rule that story 58 rejected.

## 2. Inherited from earlier stories

- **Story 21:** a check is one negated goal with its own verdict. `check_parts` checks the parts
  of a claim only when the claim's goal fails or is inconclusive, under the claim's dependencies.
  A record keeps each part as a `PartVerdict` named by its EasyCrypt operator on the EasyCrypt
  listing.
- **Story 58 / ADR 0010:** `inv = params_inv ∧ abort equality ∧ (!abort ⇒ StateRelation_invariant
  ∧ PkgInv_… ∧ GameInv_…)`. `invariant_ops` owns the operator names.
- **`part_view`:** a verified or unreachable `invariant` stands for each part. Else a part has the
  view of its own verdict, and is `Inconclusive` when the record has no verdict for it.
- **The fingerprint (ADR 0008):** its `claims` part hashes `easycrypt_check_names`. A change to
  that list makes each saved tree stale.

## 3. Work to do

### 3.1 The EasyCrypt listing adds the main invariant part

In `easycrypt_invariant_query`, the parts are, in this order:

1. `StateRelation_invariant`: the negated goal of the `invariant` state relation on the new states,
   with no dependency. This is the first conjunct of the whole goal.
2. Each other state relation, as now (`state_relation_parts`).
3. The `PkgInv_` and `GameInv_` operators, as now.

`easycrypt_invariant_query` builds part 1 itself. `state_relation_parts` does not change and gets
no flag: the Domino listing still removes `invariant`, because there the `invariant` check is the
main invariant.

`easycrypt_check_names` adds `StateRelation_invariant` at the same position, so the two lists stay
equal. Update the doc comments of both functions.

### 3.2 The tactics driver uses the part's own verdict

In `pair_view`, remove the arm `Part::Relation(name) if name == "invariant"`. The part then goes
through `part_view` like each other state relation, with the name
`state_relation_op_name("invariant")`.

`Part::Invariant` (the whole `inv`) does not change: it keeps the verdict of the whole check. A
whole `invariant` that fails still makes `leaf_of` split at once, so that each conjunct gets its
own attempt.

### 3.3 Saved trees

No migration. The new check name changes the `claims` part of the fingerprint, so a tree saved
before this story is stale and is built again. If a record has no `StateRelation_invariant` part,
`part_view` gives `Inconclusive`, never `Fails`. Thus the driver tries EasyCrypt on the conjunct.

### 3.4 Correct story 21

In story 21 §3.1, change the EasyCrypt-listing bullet to: "each `StateRelation_<r>`, **including**
`StateRelation_invariant` (the check is the whole conjunction), then the `PkgInv_` and `GameInv_`
operators". Add a pointer to this story.

## 4. Acceptance criteria

- [ ] On the EasyCrypt listing, when `invariant` fails or is inconclusive, the record has a part
      `StateRelation_invariant` with its own verdict, before the other state relations.
- [ ] `easycrypt_check_names` and the part names of `easycrypt_invariant_query` are equal, in the
      same order (a unit test).
- [ ] On the Domino listing, the parts of `invariant` do not change: no `state-relation invariant`.
- [ ] `pair_view` has no special case for `Part::Relation("invariant")`.
- [ ] Unit test: only a `PkgInv_` part fails, and the `StateRelation_invariant` part is verified.
      The view of `Part::Relation("invariant")` is `verified`; the view of the `PkgInv_` part is
      `fails`; the view of `Part::Invariant` is `fails`.
- [ ] Unit test: only the `StateRelation_invariant` part fails. Its view is `fails`; the view of
      the `PkgInv_` part is `verified`.
- [ ] Unit test: `invariant` fails and the record has no `StateRelation_invariant` part. The view
      of `Part::Relation("invariant")` is `inconclusive`.
- [ ] On a pair where a side aborts, a failing `StateRelation_invariant` part has the view
      `inconclusive`, as each other part of `invariant` has.

## 5. How to verify

```sh
source ~/.cache/domino/cvc5-lib-env.sh
cargo test --workspace --features cvc5-lib --no-fail-fast
```

Then, on an example with a package invariant (for example the story 58 fixture), run the
EasyCrypt export with the tactics driver. Make a package invariant fail on one oracle, and look at
the tactics report: the `StateRelation_invariant` conjunct has an EasyCrypt attempt and no
`domino-fails` admit. The EasyCrypt-listing page of that pair shows a `StateRelation_invariant`
check.

## 6. Rejected alternatives

- **A flag on `state_relation_parts` that keeps `invariant`.** Rejected: the caller must then know
  which listing it is on, and pass a mode that only one caller uses. The EasyCrypt query already
  builds its own parts (the side invariants), so it also builds this one.
- **Keep the special case and give it the worst verdict of the whole.** This is the defect.
  Story 58 rejected it: a `Fails` view admits a provable conjunct with no EasyCrypt attempt.
- **Derive the main invariant verdict from the other parts.** Rejected: the main invariant is
  not a conjunction of the other parts, so no other verdict tells what it is.
- **A whole `invariant` that is inconclusive while each part is verified counts as verified.**
  Not in this story. It is correct logic (the parts are now all the conjuncts), but no driver
  decision uses it: §3.6 only acts on `Fails`. Open a story if the page or the report needs it.

## 7. Notes / risks

- Each saved EasyCrypt-listing tree becomes stale once (§3.3). The next run builds it again.
- One more check for each failing or inconclusive `invariant` on the EasyCrypt listing: one more
  solver call for each such pair. Parts are only checked when the whole does not verify, so a
  passing run has no extra cost.

## 8. State handed to the next story

- On the EasyCrypt listing, each conjunct of `inv` after `!abort ⇒` has a check of its own.
- `pair_view` maps each `Part::Relation` and each `Part::SideInvariant` through `part_view`.
