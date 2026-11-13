# Story 106 — The reduction walk proves a reduction's oracle lemmas

**Epic:** EasyCrypt export: the reduction walk — `docs/stories/easycrypt/epic-the-reduction-walk.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 104 (the `#pre` check), 105 (the shape recognizers).
**Blocks:** 107.
**ADR:** `docs/adr/0024-a-reductions-oracle-lemma-is-proved-by-a-strict-reduction-walk.md`
(decisions 1 to 4).
**Algorithm:** `docs/proving-algorithm.md` §10.
**Decisions:** owner's grilling session of 2026-11-12/13, Questions 2 to 10.

A **prover** story: `src/easycrypt/tactics/reduction_walk.rs`, `driver.rs`, `mod.rs` (report),
a new fixture, tests and docs. Test-first.

---

## 1. Why this story exists

Story 103 proves a reduction's oracle lemmas with `prove_blind` (`driver.rs:2602`). This story
replaces that call with the reduction walk of `docs/proving-algorithm.md` §10, which uses the
recognizers of story 105 and the check of story 104.

## 2. The facts this story uses

- `driver.rs:2600`: for `Judgement::Reduction`, `prove_oracle` sends `proc; inline *.` and calls
  `prove_blind(0, BLIND_BUDGET)`. `BLIND_BUDGET` has no other user.
- `prove_blind` has four other callers (`driver.rs:1735`, `2622`, `2629`, `2663`). They do not change.
- `sp_front`: `sp k l` with the counts from the goal.
- `close_side_goal(node, claim, router)` (`driver.rs:1484`): the quick close, the side-goal fallback
  sequence (proving-algorithm §7.1), then an admit with `router` or `domino-verified-ec-failed`.
- `leaf_of(node, None)` (`driver.rs:2098`): exit path, `auto => &1 &2 hpre`, invariant opened into
  leaf parts, each part closed or admitted (proving-algorithm §6, §9.3).
- `exit_decisions(cond, aborts)` (`driver.rs:464`) and `decide_if`.
- `AdmitReason` (`driver.rs:41`) with `ALL` and `slug`; `DominoView::NotApplicable`.
- The report line `  <O>: blind walk, no joint tree` (`mod.rs:2371`).
- `reduction_setup` (`oracles.rs`) knows the reduction, and so the assumption composition.

## 3. What to build

1. **The walk** in `reduction_walk.rs`, entry `prove_reduction(&mut Prover)`, as §10 of
   `docs/proving-algorithm.md` describes it. The driver calls it in place of
   `prove_blind(0, BLIND_BUDGET)`. Remove `BLIND_BUDGET`.
2. **The assumption theory `<A>`** is the EasyCrypt theory of the reduction's assumption composition
   (`Comp_<Assm>`), from the job's reduction. Only the walk reads it.
3. **Side goals.** The walk sends the structural tactic alone, then tries `auto => />.` on the side
   goal, then calls `close_side_goal`. `close_side_goal` and the leaf procedure choose the reason
   from the judgement: on `Judgement::Reduction` they admit `reduction-ec-failed` with
   `DominoView::NotApplicable`. No caller passes a reason or a flag.
4. **Two admit reasons** in `AdmitReason` (and `ALL`): `reduction-mismatch` and
   `reduction-ec-failed`. Both state their view, so the comment has no `Domino:` field.
5. **Admit ids** are the arm path: `R` at the root, `.t` for the *then* arm and `.e` for the *else*
   arm of each `if.` split, for example `R.t.e`. The claim is the mismatch text of story 105, or the
   step: `assumption-guard`, `tail-branch`, `if-conditions`, `seq-coupling`, `leaf`, or the name of
   a leaf part.
6. **The tail branch** (Question 4 and the exception of Question 6): `rcondf{2} ^if; 1: auto => />.`,
   then the same with `auto => /#`, then `rcondt{2}` with `/>` and `/#`, then `rcondt{2} ^if.` with
   `close_side_goal`. If no try is accepted, admit `reduction-mismatch` with the claim
   `undecided-tail-branch`.
7. **Exit guards** (Question 7): decide side 1, then side 2, each with `rcondt`/`rcondf` in the order
   of `exit_decisions` and with `auto => />` and then `auto => /#` as the closers. If a side is not
   decided, undo both sides and send `if.` (rule 7 of story 105). This is not a mismatch.
8. **The quick close** runs at the leaf and at the start of each arm of an `if.` split, and nowhere
   else.
9. **Report:** the line becomes `  <O>: reduction walk`, and the admits are counted by reason as for
   other jobs.
10. **The `#pre` check** of story 104 runs before each `seq 1 1`, with `seq-post`,
    `DominoView::NotApplicable`, and the arm path as the id.
11. **Docs:** `docs/proving-algorithm.md`: §1.1 row "Reduction oracle lemma", §1.5 (the blind walk
    budget is only for the blind walk), §9.1, §9.2 (the two reasons and their sites), §10 (remove
    "designed, not built"). `docs/easycrypt-export.md`: "The reduction proof job" names the reduction
    walk. `docs/stories/easycrypt/00-overview.md`: rows 104–107.

## 4. Tests first

- [ ] Unit test: `AdmitReason::ALL` has the two reasons, and the comment of a `reduction-mismatch`
      admit is `admit. (* domino: R.t.e left-only-if; reduction-mismatch *)`.
- [ ] Unit test: on `Judgement::Reduction`, `close_side_goal` admits `reduction-ec-failed` (with a
      prover whose session refuses every sentence).
- [ ] Unit test: after `export` of `reduction-consts`, the report entry of `prove` says
      `reduction walk`, not `blind walk`.
- [ ] Live test (needs `DOMINO_EASYCRYPT`): `prove --gamehop 0` on `reduction-consts` closes the
      oracle lemma with no `admit`, and the whole tree compiles. (Story 103's test, kept.)
- [ ] **New fixture** `testdata/easycrypt/reduction-two-calls/`: a reduction whose package oracle
      forwards two calls in one oracle to the assumption game (an `Init` that samples a key, then a
      `Mac` that returns `None` when the key is missing). Live test: no `admit`, the proof has
      `rcondt{2}` at both assumption guards and a `seq 1 1` at the key, and the tree compiles.
- [ ] Live test, mismatch: export `reduction-two-calls`, then add one `if (true) { }` to the left
      game's oracle in the exported `Comp_<L>.ec`, then `prove`. Exactly one `reduction-mismatch`
      admit with the claim `left-only-if`, and the other arm of the split before it has no admit.

## 5. Acceptance criteria

- [ ] All tests of §4 green, with filtered test runs only. `cargo clippy` clean.
- [ ] Complexity: every touched function within budget (`.sdlc-workspace/crap-coverage.sh <filter>`).
      `driver.rs` does not grow.
- [ ] No `prove` run on a 4WHS-size project in this story (story 107 does that).

## 6. Rejected alternatives

From the grilling of 2026-11-12/13 (ADR 0024): a mode flag on `prove_blind`; `rcondt{2}` by trial;
`if{2}` on the tail branch; admitting the whole oracle or the whole job at a mismatch; one sentence
for each step with a short closer list; always `if.`; cheap trial decisions for every pair of
`if`s; the leaf procedure only, or the quick close only; reusing `program-mismatch` and
`domino-verified-ec-failed`, or one reason `reduction`; live tests only; full replay in
`FakeEasyCrypt`.
