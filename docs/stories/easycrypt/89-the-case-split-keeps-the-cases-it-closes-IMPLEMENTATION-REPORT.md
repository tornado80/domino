# Story 89 — Implementation report: the case split keeps the cases it closes

Rust only. The §7 questions use the recommended answers (see "Open questions"). No ADR.
The spec is the version of commit 94324086 (each case is closed with the crush alone).

## What changed

### Part fallback 4 keeps the cases it closes (`src/easycrypt/tactics/driver.rs`)

- New `CaseLeaf { node, pair, part, close }`: the leaf part that the split works on, and the
  sentence that closes a case. New `CaseTally { closed, admitted }`.
- `atom` gives the split its last fallback sentence as `close`: the crush
  `move: <premises> => />; smt(<hints>).` when there are premises, else `smt(<hints>).` (§3.2).
- `key_case_split(&CaseLeaf)` returns `true` when at least one case closed. Then the split is
  kept and the other cases are admitted. When no case closed, or when EasyCrypt refused a
  `case` (or the `case` did not give two goals), the split is undone and the part is admitted
  once, with the last `smt` outcome, as before (§3.3). It tells the live page
  "case split: k of n cases closed" (§3.5).
- `split_cases` returns `Option<CaseTally>` (`None`: a refused `case`). It always walks both
  bullets, and keeps the case path (`c = k{2}`, `c <> k{2}`, nested cases joined with `, `).
- New `close_case`: the crush is the only closing sentence of a case (`try_close`, so a failed
  crush is undone). On a failure the case is admitted with `admit_part` and the note
  ` (case <path>)`, and `admit_smt` is the crush's outcome. When the leaf deadline has passed,
  the case is admitted without a sentence, with the note ` (case <path>, leaf time budget
  spent)` (§3.4). The admit reason is the part's own (`pair_view`).
- `Snap` records the number of admits, and `rollback` takes back the admits made after the
  snapshot. Thus an undone split does not leave its case admits in the statistics.

### Reports (`src/easycrypt/tactics/mod.rs`, `live/mod.rs`)

- New `OracleTactics::case_admits`: the number of admitted cases (claims with ` (case `) and the
  number of parts they are cases of (a run of case admits with the same node and part is one
  part).
- New `OracleTactics::admits_summary`: the admit text of the oracle line, now with
  `; N of them cases of M parts` when there are case admits, e.g.
  `5 admits (stuck 1, domino-verified-ec-failed 4; 4 of them cases of 3 parts)`.
- `EquivalenceTactics::render` was over budget (CC about 22). Its loop body moved to the new
  `render_oracle`, and the admit text to `admits_summary`.
- New `LiveHandle::attempt_shown`: changes the text of the attempt in flight.

## Tests

Ran, filtered, `--test-threads=1`. No test starts EasyCrypt.

New or changed in `tactics/tests.rs` (scripted fake EasyCrypt; `run_key_split_with` tells which
cases the crush closes, which sentence is refused, a slow first crush and the leaf budget):

- `two_key_pairs_split_into_four_cases_each_a_bullet` (changed): each of the 4 cases gets the
  crush alone; no `smt().` or bare `smt(<hints>).` in a case. Red before the change.
- `a_case_that_does_not_close_is_admitted_and_the_split_kept` (§5 first test): one pair, the
  `=` case fails, the `<>` case closes. The script keeps `case`, `+ admit.` with the note
  ` (case c = Comp_H3.M.k{2})`, and `+ <crush>`. The admit reason is
  `domino-verified-ec-failed` for a verified pair. Red before the change.
- `three_of_four_cases_close_and_one_is_admitted_with_the_nested_note`: one admit, note
  ` (case c = Comp_H3.M.k{2}, d <> Comp_H3.M.j{2})`. Red before.
- `one_failing_case_undoes_the_whole_split` (changed): no case closes; no `case` in the script,
  one part admit with the last `smt` outcome.
- `a_refused_case_undoes_the_whole_split`: the second `case` is refused; all is undone, also the
  cases that closed.
- `the_cases_after_the_leaf_budget_are_admitted_without_a_crush`: leaf budget 1 s, the first
  crush takes 2 s; only one crush is sent, and the 3 other cases have the budget note.
- `the_report_counts_admitted_cases_apart` (§3.5). This test was written after the code.

Regression:

- `cargo test --lib easycrypt::tactics::`: 162 passed.
- `cargo test --lib --features cvc5-lib easycrypt::`: 575 passed, 0 failed
  (722 s).
- `cargo clippy --workspace --all-targets` (with and without `cvc5-lib`) and `cargo fmt --check`:
  clean.

Written, not run: none.

Not written: the §5 test "with no premises, the case's sentence is `smt(<hints>).`". The leaf
procedure always introduces `hpre`, so the fake walk cannot reach a leaf with no premises. The
code takes the last fallback sentence of `atom`, which is `smt(<hints>).` when there are no
premises.

## Complexity

`sdlc code index .` and `sdlc crap . --since-ref f675e219 --threshold 15` failed in the bwrap
sandbox (`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`; then `--since-ref` did
not resolve), as for the earlier stories. **CRAP: UNMEASURED.**

CC of each symbol edited or added (decision points counted by hand):

| Symbol | CC |
|---|---|
| `Prover::atom` | 5 |
| `Prover::key_case_split` | 6 |
| `Prover::split_cases` | 6 |
| `Prover::close_case` (new) | 3 |
| `Prover::snap`, `Prover::rollback` | 1, 5 |
| `OracleTactics::admits_summary` (new) | 3 |
| `OracleTactics::case_admits` (new) | 4 |
| `EquivalenceTactics::render` | 9 (was about 22) |
| `EquivalenceTactics::render_oracle` (new) | 13 |
| `LiveHandle::attempt_shown` (new) | 2 |
| test helpers `run_key_split_with`, `split_said`, `split_script` | 2, 1, 2 |

All are below 15.

## Owner's checks (deferred to the lead's 4WHS run)

Run in `~/ec4whs`, one at a time, with the memory watchdog:

1. Measure first (by hand): in `Eq_H6_1_1_H7_0_Send3.ec`, replace the `admit.` of one of the
   12 parts with `case (ctr1 = ctr0{2}) => [->|?]; [admit | move: <premises> => />; smt(get_setE
   mem_set remE mem_rem emptyE)].` (the premises of that part's fallback 3 sentence in the
   transcript) and compile. Report whether the `<>` case closes, and whether the `=` case closes
   with the crush.
2. `domino-ec easycrypt prove --project 4WHS --out autogenerated --theorem Full4WHS --proofstep 8 --force`
3. The same with `--proofstep 11`.
4. `domino-ec easycrypt prove --project 4WHS --out autogenerated --theorem Full4WHS --side-inv H6 --force`
5. The same with `--side-inv H2`, then `--side-inv H7`.

For each, report: for the parts of §1 (12 hop parts, 108 side-invariant parts) how many cases
close; the oracle line `… ; N of them cases of M parts` of `report.txt`; the change in the
EasyCrypt time of Send3 (and of each side-invariant job); and that no proof file has an
admitted case without a closed case beside it (`grep -n "(case " *.ec`). Then add the case
counts to `Proof_Statistics.md` (not generated by Domino, not edited here).

## Deviations from the spec

- §3.1 says "both bullets are always walked". When a `case` inside the first bullet is refused,
  the second bullet is not walked: the whole split is undone anyway (§3.1, second paragraph).
- A failed crush is undone (`try_close`) before the case admit. Before this story the failed
  `smt` stayed, because the whole split was undone.
- The live page shows the "k of n" text, but the attempt state is "closed" also for a split
  that is kept with admitted cases.
- `Proof_Statistics.md` is in `ec4whs` and is not made by Domino; it is part of the lead's run.

## Open questions (§7)

1. Keep a split in which no case closes? No (recommended answer): it is undone and the part is
   admitted once.
2. Count of admits: one per case in the `admit` count, and "N of them cases of M parts" beside it.
3. `MAX_KEY_PAIRS`: kept at 6; the leaf budget limits the time.
