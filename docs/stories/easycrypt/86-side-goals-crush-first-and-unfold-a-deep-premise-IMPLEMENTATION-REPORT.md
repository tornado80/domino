# Story 86 — Implementation report: side goals crush the premise first, and unfold a deep premise

Rust only. The §7 questions use the recommended answers (the quick close stays first; no crush
for leaf parts; fallbacks 2–5 keep their order). No ADR.

## What changed

### The crush fallback (`src/easycrypt/tactics/driver.rs`)

- New `Prover::try_crush`: on an ambient side goal `forall <binders>, A => B` it sends
  `move=> /> <binders> *; smt().` with `try_close` (the goal count must drop by one, else
  rollback). A goal without a premise gets no crush, and nothing is sent.
- `fallbacks` sends the crush first, as `Role::SideGoalFallback(1)` and
  `Closing::Fallback { k: 1, of: 5 }`. Today's four fallbacks are now 2–5. `FALLBACKS` is 5.
  The live page and the time-by-role rows read `k`/`of` and `n` from these values, so they need
  no other change.
- New `Prover::premise_binders`: the binders of `forall …, A => B`. `try_crush` and
  `try_with_premise` both use it (the old inline match in `try_with_premise` is gone).
- `close_side_goal` is `pub(super)`, so the scripted tests can call it.

### The unfold of a deep premise (`driver.rs`, `goals.rs`)

- New `goals::may_mention_op`: `true` if a node applies the operator or if a node is a stub
  (`Form::stub`, the cut of a `head` answer at depth 4). `goals::mentions_op` is deleted: no
  caller was left. Its old test uses `may_mention_op` (the fixture has no stubs). A private
  `goals::children` holds the child walk.
- `unfold_premise` uses `may_mention_op`. After an accepted `rewrite … in <name>.` it returns
  `Ok(false)` when the answer warns `unused unfold: /<op>` for each operator of the sentence
  (new `Prover::all_unfolds_unused`, which reads `session.last()`). The order (all ops, then
  only the head) and the target hypothesis are unchanged.
- Small fix found on the way: with one unfold operator, "all ops" and "only the head" are the
  same sentence, and a refused unfold was sent twice. It is now sent once.
- `unfold_premise` is `pub(super)` for the tests.

### Tests (`src/easycrypt/tactics/tests.rs`, `goals.rs`, `live/tests.rs`)

- `run_leaf` is now a call of the new `run_fake(…, act)`: the same fake EasyCrypt and prover,
  driven by `act`. `run_side_goal` calls `close_side_goal(0, "branch-condition", false)`. The
  fake has a new answer `unused` with the `unused unfold: /inv` warning.
- `proof_of` puts its JSON on one line (the fake answers one line for each sentence).
- `live/tests.rs`: the two fallback examples use the new numbering (`2/5`, `3/5`).

## Tests

Ran, filtered, `--test-threads=1`, all with the scripted fake EasyCrypt (no EasyCrypt, no
cvc5). All passed:

- `goals::tests::an_operator_at_depth_2_may_be_mentioned` (new).
- `goals::tests::an_operator_below_a_stub_may_be_mentioned` (new).
- `goals::tests::a_formula_without_stubs_and_without_the_operator_does_not_mention_it` (new).
- `tactics::tests::a_side_goal_tries_the_crush_after_the_quick_close_then_the_four_fallbacks`
  (new): `auto => /#.`, `move=> /> &1 &2 *; smt().`, `smt().`, `move => &1 &2 hpre.`,
  `rewrite /inv in hpre.`, `smt().`, `smt(<hints>).`, `move => &1 &2 hpre.`,
  `rewrite /inv in hpre.`, `smt(<hints>).`, then the admit. The premise is a `/\` chain whose
  `inv` is below a stub.
- `tactics::tests::the_crush_closes_a_side_goal_and_nothing_else_is_sent` (new).
- `tactics::tests::a_crush_that_leaves_a_goal_open_is_rolled_back_and_fallback_2_follows` (new).
- `tactics::tests::a_side_goal_without_a_premise_gets_no_crush` (new).
- `tactics::tests::an_unused_unfold_is_nothing_unfolded` (new): `unfold_premise` is `false`.
- `tactics::tests::an_unfold_of_a_deep_premise_is_sent_and_unfolds` (new): `true`.
- Red check: with the stub rule removed from `may_mention_op`, the stub test, the order test and
  the deep-unfold test fail (no `rewrite /inv in hpre.` is sent). With the rule back, they pass.
- Regression: `cargo test --lib -- --test-threads=1 easycrypt::tactics::` (153 passed),
  `tactics::live` (25 passed), `easycrypt::transcript` and `easycrypt::time_by_role` (17
  passed). These tests use scripted sessions only.
- `cargo clippy --workspace --all-targets`: clean. `cargo fmt --check`: clean.

Written, not run: none. The §6 checks are below.

## Complexity

The gate did not run: `sdlc code index .` succeeded, but `sdlc crap` failed in the bwrap
sandbox (`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`), as for the earlier
stories. **CRAP: UNMEASURED.** CC of each symbol edited or added (decision points counted by
hand):

| Symbol | CC |
|---|---|
| `goals::may_mention_op` | 3 |
| `goals::children` | 1 |
| `Prover::unfold_premise` | 8 |
| `Prover::all_unfolds_unused` | 3 |
| `Prover::premise_binders` | 4 |
| `Prover::try_crush` | 2 |
| `Prover::try_with_premise` | 6 |
| `Prover::fallbacks` | 5 |
| `Prover::close_side_goal` (visibility only) | 4 |
| `tests::run_fake` / `run_leaf` / `run_side_goal` | 3 / 1 / 1 |

All are below 15.

## Owner's checks (§6): deferred to the lead's 4WHS run

Each with `--jobs 12` in `ec4whs`, defaults otherwise:

- Proofstep 8 (H5 ~ H6_0): deferred to the lead's 4WHS run.
  `domino-ec easycrypt prove --project 4WHS --out autogenerated --theorem Full4WHS --proofstep 8 --force --jobs 12`.
  It must have at most 13 side-goal admits (25 before), and no `branch-condition` admit on the
  first guard after the router in any oracle.
- Proofstep 10 (H6_1_0 ~ H6_1_1): deferred to the lead's 4WHS run.
  `domino-ec easycrypt prove --project 4WHS --out autogenerated --theorem Full4WHS --proofstep 10 --force --jobs 12`.
  At most 14 side-goal admits (26 before), the same rule for the first guard.
- Proofstep 11 (H6_1_1 ~ H7_0): deferred to the lead's 4WHS run.
  `domino-ec easycrypt prove --project 4WHS --out autogenerated --theorem Full4WHS --proofstep 11 --force --jobs 12`.
  At most 25 side-goal admits (37 before), the same rule for the first guard.
- In the transcripts of these runs, a fallback "(premise unfolded)" sends `rewrite /inv … in
  hpre.`: deferred to the lead's 4WHS run.
- No hop gets a new admit, and the part-fallback time of steps 0–7 grows by at most 10 %
  (proofsteps 0–7, the same command with `--proofstep 0` … `7`): deferred to the lead's 4WHS
  run.

## Deviations from the spec

- `mentions_op` is deleted, not kept beside `may_mention_op`: it had no caller left.
- An unfold that EasyCrypt accepts with `unused unfold` for each op stays in the script (it
  changes nothing). Only the return value says "nothing unfolded"; no caller reads it today
  except the tests.
- The time-by-role rows needed no change: they group all side-goal fallbacks in one row.

## Addendum: the lead's 4WHS run (2026-10-22)

The lead session built `cargo build -p domino --release --features cvc5-lib` at commit 6985e837
(stories EC 86–89 and symbolic-execution 30–33), installed it as `~/.cargo/bin/domino-ec` (the old
binary is `domino-ec.bak-2026-10-21`) and ran, in `~/ec4whs`, one run at a time, with
`--force --jobs 12` and a memory watchdog:
`domino-ec easycrypt prove --project 4WHS --out autogenerated --theorem Full4WHS <job>`.
"Before" is the run of 2026-10-21 in `Proof_Statistics.md`.

| Job | Admits before | Admits now | Admits now, by goal type | Wall before | Wall now | Peak memory |
|---|---|---|---|---|---|---|
| `--side-inv H2` | 14 | **0** | — | 2,519 s | 2,148 s | 5.5 GB |
| `--side-inv H6` | 88 | **2** | 2 `side-goal` (Reveal J3, Test J2) | 3,576 s | 3,407 s | 6.8 GB |
| `--proofstep 8` (H5 ~ H6_0) | 44 | **12** | 10 `branch-condition`, 2 `side-goal` | 533 s | 741 s | 13.3 GB |
| `--proofstep 10` (H6_1_0 ~ H6_1_1) | 28 | **14** | 11 `branch-condition`, 3 `side-goal` | 932 s | 1,438 s | 13.9 GB |
| `--proofstep 11` (H6_1_1 ~ H7_0) | 81 | **84** | 19 `branch-condition`, 6 `side-goal`, 5 `equal-output`, 16 invariant conjuncts, 38 cases of 17 split parts | 2,761 s | 4,150 s | 14.2 GB |

- Story 86 targets (`branch-condition` + `side-goal` admits): proofstep 8 has 12 (at most 13, 25
  before), proofstep 10 has 14 (at most 14, 26 before), proofstep 11 has 25 (at most 25, 37 before).
  All three are met. The crush `move=> /> &1 &2 *; smt().` is sent; in H5 ~ H6_0 Reveal it closes the
  guard at node 0 and fails at nodes 1–3.
- Invariant conjuncts: H5 ~ H6_0 has 0 (14 before), H6_1_0 ~ H6_1_1 has 0 (2 before). In the side
  invariants, all 14 (H2) and all 86 (H6) game-invariant conjuncts close now. The proof files show
  `rewrite /side_inv_<C> … in hpre.` (story 86 §3.2) followed by `smt(…)`.
- H6_1_1 ~ H7_0: the key case split (stories 88 and 89) occurs in Send2, Send3, Send4 and Send5
  (`case (ctr1 = ctr0{2}) => [->|?].`). Story 89 counts one admit for each case that does not close:
  38 admitted cases of 17 parts. Counted by part, 16 + 17 = 33 invariant-conjunct parts are admitted,
  the same as before (33). The total is 84 against 81 only because of the count by case.
  The side invariants have no case split: their parts close before part fallback 4.
- **Time.** The side invariants have a shorter wall time (−15 % and −5 %), but their work (Σ oracles) is +2 % (H2) and +23 % (H6). The hops are slower in wall time: +39 % (step 8),
  +54 % (step 10), +50 % (step 11). In H6_1_0 ~ H6_1_1 Send3, the part-fallback time went from 6 m 31 s
  to 13 m 44 s (22 failed, 56 before), and the largest answer from 0.2 MB to 1.4 MB. The probable
  cause is that a deep premise of a leaf part is now unfolded (story 86 §3.2), so each part `smt`
  gets a much larger premise. Story 86 allows at most +10 % part-fallback time on proofsteps 0–7;
  those proofsteps were not run, but this result makes it likely that the limit is not kept there.
- Not run: `--side-inv H7`, proofsteps 0–7, and the story 87 `easycrypt debug` checks.
  The proof files in `~/ec4whs` are changed on disk and not committed; `Proof_Statistics.md` is not updated.
