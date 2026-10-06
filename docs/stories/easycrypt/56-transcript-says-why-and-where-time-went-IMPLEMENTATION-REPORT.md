# Story 56 — Implementation report: each record says why, and the records account for all the time

Domino only. The EasyCrypt clone does not change. The tactics that a run sends do not change.

## What changed

- **`transcript.rs`.** New types `SentenceCtx { oracle, node, role }` and `Role` (the ten
  **Sentence roles**). A fallback role carries its number `n`. A part fallback, and the admit of
  a part, carry the claim label `part`. The type makes these rules true: `n` cannot occur on a
  role that is not a fallback. `ctx` is written as an object in the order of the story:
  `{"oracle", "node", "kind", "role", "n", "part"}`. `oracle` is `null` for a sentence of no
  oracle: the opening of the proof and the `admit.`s between oracles.
  - Each sentence record has `"bytes"`: the length of EasyCrypt's answer line before the cap.
  - New function `event`: `{"file", "ctx", "event", "ms"}`, with `"resends"` for an interrupt.
    An event record has no `sentence` and no `response`.
- **`session.rs`.**
  - `set_context(SentenceCtx)` replaces the string. When the oracle changes, the Domino time
    since the last answer of the old oracle is its last `between` record. Thus `set_context`
    can fail (a failed write under `--ec-transcript full`).
  - `undo_to` sends its `undo` with role `undo`, at the node of the context it takes back.
  - A `Clock` in the transcript sink. Each record's `ms` is cut from one running total, so the
    rounding to whole milliseconds does not add up over many records. A record's `ms` is never
    less than the whole milliseconds of its own time.
  - `between`: Domino's time from one answer to the next send. A gap of 100 ms or more (with
    the short gaps before it) is written before the next sentence, in its context.
  - `interrupt`: from the first interrupt to the answer, or to the end of the grace. The
    sentence record's `ms` now stops at the first interrupt, so the two are not counted twice.
    An interrupt that is never answered gives an `interrupt` record and no sentence record.
  - `record_respawn`: a `respawn` record.
  - New `SessionEvent::EventRecorded { record_bytes }`, so the live page knows the offset of
    the records after it.
- **`tactics/driver.rs`.** `as_role` and `in_context` set the role for the sentences of one
  closing attempt and put the context before back afterwards. The role is set where the driver
  chooses the tactic:
  - quick close: `try_quick_close`;
  - side-goal fallback `n` = 1..4: `fallbacks` (its `reduce_to_ambient` is `reduce`);
  - leaf fallback `n` = 1..3 and `reduce` (the new `reduce_leaf`): `leaf_of`;
  - `split`: everything that `solve_ambient` sends to take the leaf apart;
  - part fallback `n` = 1..3: `atom`;
  - `admit`: `admit` and the new `admit_of_part`;
  - `resume`: `keep_node` (trust and replay);
  - `structure`: the default of a node and of the router prelude.
  - **Bug fixed on the way:** `prove_node` set the context of a child and did not put the
    context of the parent back. The sentences of a parent after its first child were noted with
    the node of the child. Now `in_context` restores it.
- **`tactics/mod.rs`.** The `admit.`s outside the walk (oracles proved before, the base case,
  oracles not asked for, a failed lockstep) get role `admit`. In a respawn, the `respawn` record
  and the sentences sent again have the context of the oracle that left the interrupt
  unanswered, role `resume`. The time of the respawn is added to that oracle's EasyCrypt time.
- **`tactics/live/mod.rs`.** `EventRecorded` moves the line and the byte offset and makes no
  step.
- **`CONTEXT.md`.** The entry **EasyCrypt transcript** says what a record carries now.

## Deviations from the story

- **The `respawn` record holds the kill and the start of the new EasyCrypt only.** The sentences
  sent again have their own records (role `resume`, the same oracle). If the `respawn` record
  also held their time, the sum of the records would count it twice.
- **Before this story, a respawn was not in the oracle's EasyCrypt time.** The oracle is sealed
  (and its time measured) before the respawn. To make the records of the oracle add up to its
  EasyCrypt time, the respawn's time is now added to the EasyCrypt time of that oracle.
- **The Domino time between two oracles** (lockstep execution of the next oracle, for example) is
  a `between` record with `"oracle": null`. It is in no oracle's sum.
- **Story 55's rule `tactic_ms + serialize_ms <= ms` now holds for a sentence that was not
  interrupted only.** For an interrupted sentence, EasyCrypt's work after the interrupt is in the
  `interrupt` record. On H0 ~ H1_0, all records that break the rule have `"interrupts": 1`.

## Rejected alternatives

- The three of the story (a longer `ctx` string, a role guessed from the sentence text, one
  `between` record after each sentence).
- **An `admit(…, part: Option<&Part>)` argument.** Rejected: a flag-like parameter at about 30
  call sites. `admit_of_part` is a second entry point, and `admit` calls it with the whole claim.
- **The role as a field of `Prover` that `send` reads.** Rejected: `undo`s come from the session
  and would not see it, and every early return would have to reset it. The session holds the
  context, and `in_context` restores it on every path.
- **`ms` as `as_millis` of each record.** Rejected: up to 1 ms lost per record, which is more than
  1 % over many short sentences.
- **Drop the Domino time at the end of an oracle.** The first version did this. Small oracles of
  H0 ~ H1_0 then had 50-100 ms (7-14 %) less in the records than in the report.

## Tests

- Baseline: `cargo test --workspace`: 629 passed, 0 failed, 5 ignored.
- New tests:
  - `tactics::tests::each_record_says_why_the_driver_sent_its_sentence`: a fake EasyCrypt that
    refuses every closing tactic, and a tree of two nodes (unreachable, leaf). It checks each
    record's node, role, `n`, `part` and `bytes`: quick close, structure, admit, leaf fallback
    1-3, reduce, split, part fallback 1-3 of each conjunct, admit of a part.
  - `session::tests::domino_time_between_sentences_is_recorded_and_undo_has_its_role`.
  - `session::tests::the_records_account_for_all_the_time_of_an_oracle`: three timed-out
    sentences, gaps, the end of the oracle; the sum is within 2 % of the wall time.
  - `transcript::tests`: `a_capped_record_says_how_long_the_answer_was_before_the_cap`,
    `ctx_writes_n_only_for_fallbacks_and_part_only_for_parts`,
    `an_interrupt_event_says_how_many_signals_were_sent_again`.
  - `live::tests::event_records_are_no_steps_and_every_step_finds_its_record`. Red when
    `EventRecorded` does not move the offset.
  - Changed: the two interrupt tests of `session.rs` check the `interrupt` record (`resends`,
    `ms`). The unanswered one is the test of the third criterion. The real-EasyCrypt test on
    hello-world checks that the records of `UsefulOracle` sum to its EasyCrypt time within 1 %.
- After: `cargo test --workspace`: 636 passed, 0 failed, 5 ignored. `cargo test --lib easycrypt`
  with `DOMINO_EASYCRYPT` set to `easycrypt/_build/default/src/ec.exe`: 455 passed, 1 ignored.
  `cargo clippy --workspace --all-targets`: no warnings.
- **`--features cvc5-lib`:** `cmake` is not on this machine, but `cvc5-sys` does not need it when
  `CVC5_LIB_DIR` points to a prebuilt cvc5. `scripts/setup-cvc5-lib.sh` writes
  `~/.cache/domino/cvc5-lib-env.sh`; with that file sourced, build, clippy (no warnings) and
  `cargo test --workspace --features cvc5-lib` (734 passed, 0 failed, 6 ignored) run. Story 54
  used this file. Story 55 did not source it, so its build looked for `cmake`.
- Flaky, not changed: `session::tests::an_interrupt_never_answered_is_unresponsive_after_six_signals`
  failed once (6 signals expected) in a run of the whole `cvc5-lib` suite while the machine was
  busy, and passed 3 times alone.

## Run on `example-projects/4WHS` (Full4WHS, H0 ~ H1_0)

Release build with `cvc5-lib`, capped transcript: 12 oracles, 100 goals closed, 0 admits,
214.9 s. 258 sentence records, all with `bytes` (largest answer 665,628 bytes), 31 `interrupt`
and 32 `between` records.

| role | sentences |
|------|-----------|
| quick-close | 117 |
| structure | 114 |
| leaf-fallback | 27 |

The report shows the EasyCrypt time to 0.1 s. Every sum is in the rounding interval of the
report (±0.05 s):

| oracle | report | sum of `ms` | of it `between` | of it `interrupt` |
|--------|--------|-------------|-----------------|-------------------|
| Send3 | 48.0 s | 48.034 s | 0.686 s | 1.573 s |
| Send4 | 40.2 s | 40.221 s | 0.651 s | 1.287 s |
| Test | 3.2 s | 3.150 s | 0.403 s | 0 |
| Send2 | 3.9 s | 3.922 s | 0.280 s | 0 |
| Send1 | 3.1 s | 3.056 s | 0.280 s | 0 |
| Send5 | 1.6 s | 1.622 s | 0.076 s | 0 |
| AtMost | 0.9 s | 0.940 s | 0.079 s | 0 |
| Reveal | 0.8 s | 0.772 s | 0.075 s | 0 |
| SameKey | 0.8 s | 0.750 s | 0.082 s | 0 |
| NewKey | 0.7 s | 0.698 s | 0.116 s | 0 |
| AtLeast | 0.5 s | 0.538 s | 0.075 s | 0 |
| NewSession | 0.4 s | 0.405 s | 0.073 s | 0 |

The live page of this run refers to 247 transcript records. All are sentence records, and no
goal text "could not be read".

## Open items

- **The H2_1 ~ H3_0 `Send3` numbers that the criterion asks for are not given.** That oracle
  takes much longer than the 10-minute limit of this task. The table above gives `Send3` of
  H0 ~ H1_0 in its place. A run of `--proofstep 4 --oracle Send3` gives the numbers.
- No respawn and no admit occurred in the H0 ~ H1_0 run. Their records are checked by the unit
  tests only (the respawn path by the existing respawn tests, which still pass).
- An exact check to 1 % on the small oracles needs the EasyCrypt time in milliseconds; the
  report rounds it to 0.1 s. The real-EasyCrypt test on hello-world checks 1 % on the exact
  `Duration`.
