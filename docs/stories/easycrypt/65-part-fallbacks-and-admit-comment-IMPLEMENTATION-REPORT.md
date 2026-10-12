# Story 65 — Implementation report: the part fallback sequence, and what an admit says

Rust only. The translation does not change.

## What changed

- **`driver.rs`, `atom`.** The part fallback sequence is now:
  1. `smt().`
  2. `smt(<hints>).`
  3. `move: <premises> => />; smt(<hints>).`, skipped when the leaf procedure introduced no
     premise.
  4. (reserved for story 66), else an admit.

  `rewrite !get_set_neqE.` is gone. Each fallback is one sentence and a closing attempt: the
  live page shows `fallback k/3` (`PART_FALLBACKS = 3`; story 66 makes it 4).
- **Premises.** `Prover::premises` holds the premises the leaf procedure introduced, in the
  order of introduction: `hpre` after `auto => &1 &2 hpre.` (`leaf_of`), then each premise of a
  `Step::Premise` that EasyCrypt accepted (`open_step`). `split_part` truncates the list after
  each bullet, so a premise that a bullet introduced is not used in the next bullet.
- **`SmtOutcome`** (`timeout` / `unknown` / `error`), from an answer's `timing.smt`
  (`SmtOutcome::of_answer`): `timeout` if a prover call timed out, else `unknown`, else `error`
  if EasyCrypt refused the sentence. `send` keeps the outcome of the last answer
  (`last_smt`); `atom` gives the last fallback's outcome to the admit (`admit_smt`, taken by
  `send_admit`).
- **`Admit::smt`** (new field) and **`Admit::fields`**: `J1 StateRelation_x;
  domino-verified-ec-failed; smt: timeout`. The claim is shown by its operator name
  (`invariant/` removed) and is empty for the whole leaf (`equal-output+invariant`). `Domino:
  <view>` is shown only for `router`, `stuck`, `seq-post`, `program-mismatch`
  (`AdmitReason::needs_domino_view`). `smt:` is shown only when a part fallback ran.
  `Admit::label` is `(* domino: <fields> *)`; the report's admit lines are `admit <fields>`.
  The report's `goal:` is the front goal at the admit, which is the goal the last fallback got.
- **Session record**: unchanged (`to_record` / `from_record` do not use `smt`; `domino` is
  still written).

### Rejected shape

Passing the outcome as a parameter through `admit_part` → `admit_of_part` → `send_admit`
(every other admit caller would pass `None`). A field that the next admit takes is smaller.
The alternatives in §3.3 of the story were not implemented.

## Tests

- `the_leaf_is_opened_until_only_parts_are_left_and_no_split_is_sent` (changed): on parts that
  no fallback closes, the sentences are `smt().`, `smt(get_setE mem_set emptyE).`,
  `move: hpre hpre => />; smt(get_setE mem_set emptyE).`, then `admit.`; no `get_set_neqE` is
  sent; each admit has `smt: error` (the fake EasyCrypt gives no timing).
- `the_smt_outcome_is_timeout_then_unknown_then_error` (new).
- `the_admit_label_says_dominos_view_only_where_the_reason_does_not` (new): every reason; the
  whole-leaf claim is empty; an old session record reads back without change.
- Changed for the new label/report format: `an_admit_label_names_…`,
  `the_admits_of_a_seal_…`, `the_report_counts_admits_by_reason_…`,
  `each_record_says_why_the_driver_sent_its_sentence`, and the live page test
  `steps_are_attributed_to_their_goal_…`.

Runs: `cargo test --lib` 687 passed, 5 ignored; `cargo clippy --workspace --all-targets`
clean; `cargo build --release --workspace` OK.

## Not done

- `--features cvc5-lib` does not build here (no `cmake` for `cvc5-sys`).
- The before/after table for H2_1 ~ H3_0, H4 ~ H5 and H6_1_1 ~ H7_0 (kept count of each
  fallback, admits) was not measured: the owner asked for no EasyCrypt proof runs in this
  session. The "before" numbers are in the story (2026-10-08).
- In the fake test, both premises are named `hpre` because the fake goal has no hypotheses;
  in EasyCrypt, `fresh_name` gives the second one a new name.
- The CRAP gate was not measured (`sdlc` is not available here). `atom` has CC about 5.
