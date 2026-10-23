# Story 92 — Implementation report: a pruned crush after the old side-goal fallbacks

Rust only. No ADR. Story 93 is not in this change. The `drop_ops` input and the fourth fallback
slot do not block it.

## What changed

### The pruned crush sentence (`src/easycrypt/tactics/goals.rs`)

- New pure function `pruned_crush_sentence(goal, drop_ops) -> Option<String>` (§3.2 step 2–3).
  It walks the conclusion with `as_forall` and `as_implication`. Each value binder gets `x<i>`,
  each kept premise gets `h<i>`, each premise whose head operator is in `drop_ops` gets `_`. A
  `forall` between two premises is walked too. The sentence is
  `move=> <names>; move: <kept>; smt().`, or `move=> <names>; smt().` when nothing is kept.
  `None` when the conclusion has no premise.
- Deviation from the spec signature: the function takes the `Goal`, not only the conclusion,
  because the names must be fresh against the hypotheses (`fresh_name_besides`).
- A memory binder keeps its name and stays in the context (`move:` of a memory is not sent).
- New `is_dropped`: the head operator matches a name of `drop_ops` exactly or after more
  qualifiers (`Top.Comp_H5.side_inv_H5`). The driver has no name pattern such as `side_inv_`.

### The fallback sequence (`src/easycrypt/tactics/driver.rs`)

- `FALLBACKS` is 4. The sequence is: 1 crush, 2 `smt().` with the premise unfolded,
  3 `smt(<hints>).`, 4 pruned crush (§3.1). Old fallbacks 2 (`smt().`) and 5
  (`smt(<hints>)` with the premise unfolded) are removed.
- New `try_pruned_crush`: snapshot, `move=> /> <mems>.` with `Want::Full`; a refusal returns
  `false`; a drop of the goal count returns `true`. Then the pruned sentence with `Want::Status`.
  If the goal does not close, both sentences are rolled back.
- New `fallback(k, shown, f)`: one closing attempt with role `SideGoalFallback(k)`. With it,
  `fallbacks()` is a straight list of four calls (lower complexity than before). The live page
  shows `pruned crush` for fallback 4; both sentences of the pruned crush have role
  `SideGoalFallback(4)`.
- New `Prover::drop_ops: &[String]`.

### The drop list (`src/writers/easycrypt/invariant.rs`, `src/easycrypt/tactics/mod.rs`)

- New `side_inv_drop_ops(comps)`: `Comp_<C>.side_inv_<C>` of each composition with side
  invariants, each name once. It uses `side_inv_op_name`, the same function as the
  precondition (`proof.rs`, `side_inv_app`).
- `mod.rs` fills `drop_ops`: equivalence → both compositions; side invariants → the job's
  composition; package invariants → empty (§3.3).

## Tests

Ran, filtered, `--test-threads=1`, under `systemd-run -p MemoryMax=6G`. No test starts
EasyCrypt or cvc5. All green (the last runs: 17 of 17, 53 of 53, 25 of 25).

New in `goals.rs` (pure):

- `the_pruned_crush_drops_the_side_invariant_and_reverts_the_rest_in_order` (§5 test 1):
  `move=> x0 x1 h2 _ h3 x4 h5; move: x0 x1 h2 h3 x4 h5; smt().`
- `without_drop_ops_the_pruned_crush_drops_nothing` (§5 test 2).
- `a_side_invariant_applied_to_a_record_literal_is_dropped` (§5 test 3). Parentheses make no
  node in the formula tree, thus the application is the premise.
- `a_goal_without_a_premise_has_no_pruned_crush_and_one_with_only_dropped_premises_no_move`
  (§5 test 4).
- `the_pruned_crush_names_are_fresh_against_the_hypotheses`.

New or changed in `tactics/tests.rs` (scripted fake EasyCrypt):

- `a_side_goal_tries_the_crush_after_the_quick_close_then_the_three_fallbacks` (changed, §5
  test 6 and 8): every try fails; the sequence is `auto => /#.`, crush, `move => &1 &2 hpre.`,
  `rewrite /inv in hpre.`, `smt().`, `smt(<hints>).`, `move=> /> &1 &2.` (asked `full`), the
  pruned sentence, then one admit with `domino-verified-ec-failed`, as before. No `move=> />`
  stays in the script.
- `the_pruned_crush_closes_a_side_goal_and_nothing_else_is_sent` (§5 test 7).
- `a_crush_that_leaves_a_goal_open_is_rolled_back_and_fallback_2_follows` (changed): fallback 2
  is now the unfolded `smt().`
- `a_side_goal_without_a_premise_gets_no_crush` (changed): only `auto => /#.` and
  `smt(<hints>).`

Also ran: the filters `fallback`, `time_by_role`, `transcript`, `tactics::goals`,
`tactics::live`, `crush`, `side_goal`.

### Written, not run (deferred until the proofstep 11 job finishes)

- `the_drop_list_of_an_equivalence_holds_both_side_invariants_of_the_precondition`
  (`invariant/side.rs`, §5 test 5). It exports `test-projects/test-package-invariant-params`.
  Command:
  `systemd-run --user --scope -p MemoryMax=6G timeout 900 cargo test -j 4 --lib the_drop_list_of_an_equivalence -- --test-threads=1`

## Acceptance criteria not done here

- The owner's check on `ec4whs` (§6: proofsteps 4, 8, 10, 11, H7_1_1_0 ~ H7_1_1_1,
  `--side-inv H6`, `--side-inv H7`), the per-hop fallback tables and the transcript records of
  missed targets. Big project: not run. The owner runs them.
- Complexity: UNMEASURED (no Rust recipe for `sdlc crap`). By hand, each function in the diff
  has a cyclomatic complexity under 10.

## Clippy

`cargo clippy --all-targets`: clean.

## Issues

- None found in the code around the change. Open: §7 questions 1 and 2 stay open.
