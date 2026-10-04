# Story 47 — `inv` guards only the invariant

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 06 (invariant translation), 42 (`params_inv`), 43 (invariant layout).
**Blocks:** nothing. It is independent of story 46.

---

## 1. Why this story exists

The owner: *"I notice a redundancy in invariant translation where all relations are ANDed together
in `Domino_invariant` but then they also appear in `inv`."*

Today `inv`'s guarded part is the conjunction of **every** `define-state-relation` in the
equivalence's invariant files (`build_invariant_file`, `src/writers/easycrypt/invariant.rs`,
`state_relation_conj`). Hand-written invariant files usually conjoin their relations inside
`invariant` already, so each relation is stated twice. From
`testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec`:

```
op Domino_invariant (l : Hybrid0_state) (r : Hybrid1_state) : bool =
     …
  /\ Domino_state_eq l r
  /\ Domino_keys_computed_correctly l r
  /\ Domino_time_of_nonces l r
  /\ Domino_time_of_sid l r
  /\ Domino_time_of_acceptance l r.

op inv (l : Hybrid0_state) (r : Hybrid1_state) : bool =
     params_inv l r
  /\ l.`l_abort_flag = r.`r_abort_flag
  /\ (   !l.`l_abort_flag
      =>    Domino_state_eq l r
         /\ Domino_keys_computed_correctly l r
         /\ Domino_time_of_acceptance l r
         /\ Domino_time_of_nonces l r
         /\ Domino_time_of_sid l r
         /\ Domino_invariant l r).
```

This repetition costs proof time. Every `rewrite /inv … in hpre` hands smt each relation twice, and
every leaf has to prove each relation twice. It also departs from Domino. Domino assumes **only**
`invariant` on the states before an oracle call (`claim_assumption_parts`,
`src/writers/smt/contexts/equivalence/emit.rs`: `build_invariant_old_call("invariant")`). Every other
relation is a claim or a helper. When `invariant` does not include a relation, conjoining it into
`inv` makes EasyCrypt both assume and prove something Domino never assumed. A relation
`invariant` leaves out is not needed for the equivalence, and EasyCrypt's claim set has no
separate relation claims, so nothing proves it on its own.

Vocabulary (`CONTEXT.md`): **Invariant** (the state relation named `invariant`), as distinct from
**State relation**.

## 2. Inherited from earlier stories

- **Story 06:** every `define-state-relation` becomes `op Domino_<mangled> (l, r)`, in file order,
  and is pushed onto `InvariantParserState.state_relations`. Only those relations make up `inv`'s guarded
  part; a `define-fun` never does.
- **Story 42 / ADR 0007:** `inv = params_inv l r /\ l.abort = r.abort /\ (!l.abort => …)`. That
  shape stays; only the `…` changes.
- **Story 43:** `inv` is laid out one conjunct per line. With a single guarded conjunct, the
  layout puts `Domino_invariant l r` on the line after `=>`, as in
  `testdata/easycrypt/story42/4WHS/Eq_H1_1_H2_0_Invariants.ec`.
- **Story 27 (tactics):** `unfold_ops` (`src/easycrypt/tactics/mod.rs`) lists `inv`,
  `params_inv` and every `Domino_<rel>` that lockstep execution reports. `solve_ambient` labels a
  part by the op at its head (`Part::Relation`). Neither needs to change: unfolding
  `Domino_invariant` exposes the relations it calls, and those are labelled as before.
- **An old-style `(define-fun invariant …)`** over raw game-state sorts (for example
  `example-projects/hello-world-2rand-test`) **already fails translation**, with
  `unsupported SMT sort <GameState_…>`. This story does not change that.

## 3. Work to do

- `inv`'s guarded part becomes the single application `Domino_invariant l r`, the op translated from
  the `define-state-relation` whose SMT name is exactly `invariant`. Look it up through the op
  registry by its raw name. Do not hard-code the mangled name.
- Every `define-state-relation` is still translated to its own `Domino_` op, in file order, whether
  or not `invariant` calls it. `state_relations` keeps its order. It is no longer folded into `inv`,
  so drop it if nothing else reads it.
- **No invariant, no translation.** If none of the equivalence's invariant files defines a
  `define-state-relation invariant`, translation fails with a new `InvariantError` that names the
  equivalence (`<left> ~ <right>`) and its invariant files, and says that the invariant must be a
  `define-state-relation` named `invariant`. Today an equivalence with no relations at all gets
  `!abort => true`; that case is now this error too.
- Fixtures that have no `invariant` gain one: `testdata/easycrypt/story42/params/theorem/
  invariant.smt2`, `invariant-trivial.smt2` and `invariant-different-packages.smt2`. Each new
  `invariant` is the conjunction of the file's relations, so every story-42 test keeps the meaning
  it had. Re-check each test's expected text afterwards: an assertion that pinned the old guarded
  conjunction changes on purpose.
- Regenerate the golden files whose `inv` changes:
  `testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec`, and any other golden file a
  test points to (grep `testdata` for `op inv`). Unit tests in `src/writers/easycrypt/tests.rs` and
  `invariant.rs` that build `inv` by hand follow suit.
- Amend the **Invariants** row of `00-overview.md` §3 with an "**Amended by story 47:**" note.
- **Leave alone:** ADRs, earlier stories and their reports.

## 4. Acceptance criteria

- [ ] For every equivalence that translates, `op inv` is exactly
      `params_inv l r /\ l.abort = r.abort /\ (!l.abort => Domino_invariant l r)`.
- [ ] Every `define-state-relation` still has its `Domino_` op in the invariant file, in file
      order.
- [ ] An equivalence whose invariant files define no `define-state-relation invariant` fails
      translation with an error naming the equivalence and its files. A unit test covers this.
- [ ] The story-06 golden file's `inv` no longer lists the five relations. Its `Domino_invariant` is
      unchanged.
- [ ] Translation of `example-projects/4WHS` (Full and Simple) and
      `example-projects/kem-dem/kem-dem-cca-ssp` still succeeds. Each generated
      `Eq_*_Invariants.ec` compiles under `easycrypt compile` when EasyCrypt is available.
- [ ] A tactics run on `kem-dem-cca-ssp` proves at least the oracles it proved before this story.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt export --theorem Full4WHS --force
grep -A6 '^op inv' <out>/*/Eq_H2_1_H3_0_Invariants.ec    # one guarded conjunct
grep -c '^op Domino_relation' <out>/*/Eq_H2_1_H3_0_Invariants.ec   # still 10

cd ../../testdata/easycrypt/story42/params
# temporarily remove `invariant` from one fixture:
$D easycrypt export --theorem Params --force; echo $?    # non-zero, names the equivalence
```
