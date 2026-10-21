# Story 87 — The EasyCrypt `invariant` check assumes `no-abort`

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 23 (lockstep execution on the EasyCrypt listing), symbolic-execution 19, 21 and 23
(claim sets, parts, the core set), 58 (the claims part of the fingerprint).
**Blocks:** nothing.
**ADR:** none (ADR 0008's fingerprint gets a more precise `claims` part; the ADR does not change).
**Decisions:** owner's request of 2026-10-21: "give `invariant` the `no-abort` dependency". This
reverses one point of story 23 §3.2 ("Not assumed: any claim dependency, `no-abort`, or any project
lemma") for `no-abort` on `invariant` only. Open questions in §7; §3 uses the recommended answers.

A **debugger** story, Rust only. Test-first.

---

## 1. Why this story exists

`domino-ec easycrypt debug --theorem Full4WHS --proofstep 8` (`ec4whs`, H5 ~ H6_0) reports, for
NewSession:

```
[4] terminal-pair J2
    left  consumed L20, at L20 Game_H5.abort_flag <- true;
    right consumed L19, at L19 ec_r1 <- ec_result_1;
    equal-output: [unsat: ok]
    invariant:    [unknown: inconclusive]  models/J2.invariant.smt2
      StateRelation_relation_state_equality:     [unknown: inconclusive]
      StateRelation_relation_trivial_equalities: [unknown: inconclusive]
```

and the run ends with `easycrypt::debug_not_verified`. Yet `domino prove` proves the hop, and
EasyCrypt closes `Eq_H5_H6_0_NewSession.ec` with no admit.

J2 is the path `LTK.[kid] = None`. Both sides abort. H5 aborts before it writes anything. H6
(`KX_noprfkey`) first does `ctr_ <- ctr_ + 1` and `State.[ctr_] <- …`, and then aborts when
`PRF.Hon(kid)` returns `None`. Domino's abort return keeps the state reached at the abort
(`OracleContext::smt_construct_abort`), so the two new states differ in `ctr_` and `State`, and the
relation is genuinely false there. (cvc5 says `unknown`, not `sat`, because of the quantified
invariant on the old states.)

Nobody needs the relation on that pair:

- `domino prove` checks `invariant` under its declared dependencies, `invariant: [no-abort]` in
  `Full4WHS.ssp`, so the pair is vacuous.
- EasyCrypt's `inv` is `params_inv ∧ l.abort_flag = r.abort_flag ∧ (¬l.abort_flag ⇒ relations)`:
  after an abort it asks nothing of the states.
- The Domino-listing debugger agrees with both. `domino debug --lockstep --proofstep 8 --oracle
  NewSession`, with `--claim-set obligations` and with `--claim-set core`, gives J2: `equal-aborts`
  verified, `invariant` `unreachable (dependency-false: no-abort)`.

Only the EasyCrypt claim set (`ClaimSet::NoDependencies`, `claims.rs`) checks `invariant` with no
dependency. The story 23 implementation report recorded exactly this as an **open difference**
("Domino's invariant verdict is stricter at abort pairs, and `prove` only gets around it with the
`no-abort` dependency this mode does not assume"), and the test
`the_invariant_is_checked_on_the_state_at_the_abort` pins it. The tactics already work around it:
`pair_view` (`tactics/driver.rs`) turns an `invariant` failure on a pair where a side aborts into
`Inconclusive`. Nothing closed the difference.

`no-abort` is not a project lemma. Story 23 dropped the dependencies because "EasyCrypt won't have
them", which is true of project lemmas but not of `no-abort`: EasyCrypt has it, as the
`¬abort_flag` guard in `inv` and the `if (!abort_flag)` of every router.

## 2. What the EasyCrypt claim set should check

With `equal-output` = `equal-aborts ∧ same-output` (unchanged) checked on every pair, `invariant`
under `no-abort` gives exactly EasyCrypt's postcondition `={res} ∧ inv`:

| Pair | EasyCrypt needs | `equal-output` | `invariant` under `no-abort` |
|---|---|---|---|
| neither side aborts | `={res}`, flags equal, relations | `same-output` | checked |
| both abort | flags equal (the relations are guarded) | holds | `unreachable (dependency-false: no-abort)` |
| exactly one aborts | flags equal: **false** | fails | `unreachable (dependency-false: no-abort)` |

The third row still fails as a pair, through `equal-output`. That is where EasyCrypt fails too.

Nothing else of the EasyCrypt claim set changes: `equal-output` keeps no dependency (`same-output`
compares the return-value-or-abort values, so it means the right thing on aborting pairs; story 23
report, "How equal-output was built"), and no project lemma is assumed.

## 3. Work to do

### 3.1 `invariant` gets `no-abort`

`easycrypt_invariant_query` (`lockstep_run.rs`) builds the claim with the one built-in dependency
`no-abort` (`ClaimKind::BuiltIn(BuiltInFact::NoAbort)`), the way `side_run.rs` gives every
side-invariant claim `left-no-abort`:

```rust
let claim = ResolvedClaim {
    name: "invariant".to_string(),
    kind: ClaimKind::StateRelation,
    dependencies: vec![ResolvedDependency {
        name: BuiltInFact::NoAbort.name().to_string(),
        kind: ClaimKind::BuiltIn(BuiltInFact::NoAbort),
    }],
    admitted: false,
};
ClaimQuery { parts: state_relation_parts(…), ..ClaimQuery::of(eqctx, &claim, oracle) }
```

`check_claim` already does the rest: on a pair where a side aborts, `false_by_terminals("no-abort",
…)` is `Some(true)` and the verdict is `Unreachable { DependencyFalse { dependency: "no-abort" } }`
with no solver call; elsewhere the dependency is pushed before the negated goal and the parts are
checked under it.

- The pages and `trace.json` show `invariant` with `dependencies: ["no-abort"]`
  (`ResolvedClaims::infos`, `ClaimGoalView`).
- The `ClaimSet` variant no longer has no dependencies: rename `ClaimSet::NoDependencies` to
  `ClaimSet::EasyCrypt` and rewrite its documentation: "`equal-output` (the conjunction of the
  `equal-aborts` and `same-output` goals, no dependency) and `invariant` under `no-abort`, as
  EasyCrypt's `inv` guards its relations under `¬abort_flag`. No project lemma is assumed."
- Update the module documentation of `lockstep_run.rs` (the paragraph "`smt_construct_abort` …
  the EasyCrypt claim set, which cannot, does not") and the `equal-output` comment in
  `easycrypt_queries` ("with the empty dependency set they genuinely share" stays true for
  `equal-output`).

### 3.2 The tactics drop the workaround

`pair_view` (`tactics/driver.rs`) no longer needs to turn an `invariant` failure on an aborting pair
into `Inconclusive`: there is none. Remove that branch and its doc sentence ("On a pair where a side
aborts, an invariant failure is not held against EasyCrypt …"). An `Unreachable` verdict already maps
to `DominoView::Verified` (`view_of_verdict`).

Effect on `prove`: a leaf below an aborting pair whose `invariant` was `GoalFails` or `Inconclusive`
now reads as Domino-verified, so its admits are labelled `domino-verified-ec-failed` instead of
`domino-inconclusive`, and the whole-leaf check (`prove_node_inner`, `all_fail`) can no longer fire on
such a pair. No tactic changes.

### 3.3 The fingerprint sees the dependency

The `claims` part of the joint-tree fingerprint (ADR 0008, `lockstep_fingerprint.rs`) hashes only
the names of the checks (`easycrypt_check_names`). After §3.1 the names are the same but the
verdicts differ, so a saved tree from before would be reused with its old `invariant` verdicts under
`--resume trust`. Hash each check with its dependencies (`invariant [no-abort]`), so every saved
EasyCrypt joint tree reads as stale once, with the existing warning "the claims checked".

## 4. Rejected alternatives

- **Make the goal EasyCrypt's `inv` literally**: `equal-aborts ∧ (no-abort ⇒ relation)`. It would
  also fail `invariant` on a pair where exactly one side aborts, as EasyCrypt does. But it checks
  `equal-aborts` twice, gives no `dependency-false` scope, and differs from how `prove` and the
  Domino-listing debugger state the same claim. The pair fails through `equal-output` anyway (§2).
- **Use the theorem's declared dependencies of `invariant`.** Then project lemmas declared there
  would come back, which story 23 rightly excludes (EasyCrypt does not have them). The core set
  (`--claim-set core`, symbolic-execution 23) is the Domino-listing version of this idea; the
  EasyCrypt set takes only `no-abort`, whatever the theorem declares.
- **A flag** (`easycrypt debug --claim-set …`). The EasyCrypt claim set is what EasyCrypt proves;
  there is one right answer, not a choice. `domino debug --claim-set` keeps the choices.
- **Keep the workaround in `pair_view` only.** The debug report and `debug_not_verified` stay wrong
  for every oracle whose aborting paths write state before the abort.

## 5. Tests first

- [ ] Red: `the_invariant_is_checked_on_the_state_at_the_abort` (`AbortState`: the left does
      `ctr <- ctr + 1; assert b`, the right only `assert b`; `invariant` is `left.p.ctr =
      right.p.ctr`) is renamed `the_invariant_is_not_asked_of_a_pair_that_aborts` and expects
      `[(false, false, 0, 2), (true, true, 0, 1)]` (rank 1 = unreachable), with the reason
      `DependencyFalse { dependency: "no-abort" }` on the second pair. The first pair still fails:
      without an abort the counters differ.
- [ ] `AbortDiff` (exactly one side aborts): `equal-output` still fails (rank 2) and `invariant` is
      `unreachable (dependency-false: no-abort)`.
- [ ] `AbortBoth`: unchanged for `equal-output`; `invariant` unreachable on the aborting pair.
- [ ] `trace.json` of an EasyCrypt-listing run lists `invariant` with `dependencies: ["no-abort"]`
      and `equal-output` with `[]`; the goal view shows the `no-abort` assertion.
- [ ] The parts of `invariant` are not checked on an aborting pair (`a_relation_breakdown_is_only_made_for_a_failing_invariant` style).
- [ ] `pair_view`: a pair where a side aborts with `invariant` `Unreachable` gives
      `DominoView::Verified`; the old abort branch is gone.
- [ ] Fingerprint: the `claims` part differs from the one computed with the names alone, and a
      tree saved before is reported stale with "the claims checked".
- [ ] The Domino-listing claim sets (`Obligations`, `Core`) and the side tree's claims are unchanged
      (existing tests stay green).

## 6. Acceptance criteria

- [ ] All tests of §5 green; `cargo clippy` clean; no `NoDependencies` left in `src/`.
- [ ] The owner's check, `ec4whs`:
      `domino-ec easycrypt debug --theorem Full4WHS --out autogenerated --proofstep 8 --oracle NewSession`
      ends without `debug_not_verified`, and J2 reads `invariant: unreachable (dependency-false:
      no-abort)`.
- [ ] `domino-ec easycrypt debug --theorem Full4WHS --out autogenerated` over all proofsteps
      reports no failure that is not also a failure of `domino debug --lockstep --claim-set core`
      on the same pair.
- [ ] The story 23 implementation report's section "Invariant vs abort (open difference, `prove`
      untouched)" gets a line: closed by story 87.

## 7. Open questions

1. **`no-abort` or the literal `inv` shape (§4, first point)?** Recommended: `no-abort`, so that the
   three debuggers (prove, Domino listing, EasyCrypt listing) state `invariant` the same way.
2. **`same-output` under `no-abort` too?** Not needed: `equal-output` is right on aborting pairs as
   it is (§2). Recommended: unchanged.
3. **Rename `ClaimSet::NoDependencies`?** Recommended: yes (`ClaimSet::EasyCrypt`), since the name
   would now be false.
