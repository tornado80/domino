# Story 106 — Implementation report: the reduction walk proves a reduction's oracle lemmas

Prover story. Branch `amir/easycrypt-export`, ADR 0024. Implementation in 17487d34, review fixes in
dfe47be0.

## What was built

- **The walk** (`src/easycrypt/tactics/reduction_walk.rs`, `prove_reduction`): §10.1 of
  `docs/proving-algorithm.md`. After `proc; inline *.` the driver calls it in place of
  `prove_blind(0, BLIND_BUDGET)`; `BLIND_BUDGET` is gone. Per arm: quick close at the arm start,
  `sp k l`, the goal read in full, `classify`, then one step: `rcondt{2} ^if.` (assumption guard),
  the tail branch tries (`rcondf{2}`/`rcondt{2}` with `/>`, `/#`, then `rcondt{2} ^if.`), the exit
  guards (side 1 then side 2 in the order of `exit_decisions`, else undo and `if.`), `if.` with
  arms `.t`/`.e`, `seq 1 1` after the `#pre` check of story 104, the leaf procedure, or a
  `reduction-mismatch` admit. A step's side goal is a bullet: `auto => />.`, then
  `close_side_goal`.
- **`AdmitReason::ReductionMismatch` / `ReductionEcFailed`** (`reduction-mismatch`,
  `reduction-ec-failed`), in `ALL` before `interrupted`; neither carries `Domino:`.
- `close_side_goal` and `admit_ec_failed` (the leaf procedure's admits) admit
  `reduction-ec-failed` with `DominoView::NotApplicable` and the arm path on `Judgement::Reduction`;
  the whole-leaf claim of a reduction is `leaf`.
- **Assumption theory**: `ReductionOracleLemma::assumption` (`Comp_<A>`), filled by the exporter
  from the lemma's side spec; the job hands it to the prover (`Prover::walk`, with the arm path).
- Report line `  <O>: reduction walk`.
- `SyncSampling`, `sampled_head`, `synchronized_sampling` moved from `driver.rs` to `goals.rs`, so
  `driver.rs` shrinks (−38 lines) although it gained the two reasons and the judgement checks.
- **Fixture** `testdata/easycrypt/reduction-two-calls/`: `Mod.Query(m)` calls `Init` (samples
  `key`) then `Mac(m)` (`Unwrap(key)`) of the assumption game `MacGame`.
- Docs: proving-algorithm §1.1, §1.5, §9.1, §9.2, §10 status; easycrypt-export "The reduction proof
  job"; 00-overview.

## Decisions and deviations

- **Live EasyCrypt matched the hand-made recognizers.** On `reduction-two-calls` the assumption
  guards (`Comp_MacGame.Game_MacGame.abort_flag`), the tail branch and the exit guards were all
  recognized as printed by EasyCrypt; no recognizer fix was needed. The story-105 fixtures under
  `reduction-walk-goals/` were not replaced by captured goals (the Full4WHS shapes still need
  story 107).
- Defensive mismatch claims not in §10.4: `sp` (front not a program, or `sp` refused),
  `not-a-program-pair`, and `seq-coupling` when two samplings give no plan. `if.` accepted with
  other than three goals is undone and admitted `if-conditions` mismatch.
- The root `R` gets the quick close, as §10.1 says (`walk("R", true)`); story §3.8 says "only at the
  leaf and the start of each arm" — §10.1 was followed.
- `close_side_goal` keeps its `router` flag for the other jobs; the walk passes `false` and the
  reduction branch returns before it is read.
- `goals::sampled_in_pre` still has no caller (the walk uses `synchronized_sampling`, which calls
  `sampled_var_in_pre`), so its `#[allow(dead_code)]` stays.
- The fixture samples `Bits(n)`: the exporter supports sampling only `Bits`.

## Tests run

| Command | Result |
|---|---|
| `cargo test -p sspverif --lib reduction_walk -- --test-threads=1` | 18 passed (15 recognizers, reasons/label, branch walk on a fake EasyCrypt, report line) |
| `cargo test -p sspverif --lib on_a_reduction_a_side_goal` | passed |
| `cargo test -p sspverif --lib reduction -- --test-threads=1` (no `DOMINO_EASYCRYPT`) | 59 passed, 1 ignored |
| filters `side_goal`, `leaf`, `admit`, `render`, `reason`, `sampling`, `the_reports_name_the_reduction` | all passed |
| live `prove_closes_the_reduction_consts_oracle_lemma_and_the_tree_compiles` (`systemd-run … MemoryMax=6G`) | passed, 5.8 s, no admit |
| live `prove_closes_the_reduction_two_calls_oracle_lemma_and_the_tree_compiles` | passed: 0 admits, 8 goals closed, EasyCrypt 13.3 s; two `rcondt{2} ^if.`, `seq 1 1 : (#pre /\ k{1} = k{2})`; files compile |
| live `an_extra_if_on_the_left_is_one_left_only_if_mismatch` | passed: one admit `R.t left-only-if; reduction-mismatch`, `R.e` closed, 7.8 s |
| `cargo clippy -j 2 --workspace --all-targets` | clean |
| `.sdlc-workspace/crap-coverage.sh reduction_walk prove_closes_the_reduction an_extra_if_on_the_left on_a_reduction_a_side_goal side_goal leaf_ admit` | coverage ingested |
| `sdlc crap gate . --since-ref f2dad927 --threshold 15` | not run: `bwrap: loopback: Failed RTM_NEWADDR` |

## Written, not run

None in this story. Hop 12 of Full4WHS is story 107.

## Epic §5 "Done when"

- [ ] Stories 104–107 done with reports — 104, 105, 106 done.
- [x] `prove` on `reduction-consts` and `reduction-two-calls` leaves no admit.
- [ ] Hop 12 of Full4WHS — story 107.
- [x] `docs/proving-algorithm.md` — §10 and the new reasons.
