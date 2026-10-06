# Story 57 — Implementation report: the tactics report shows time by role

Domino only. The tactics that a run sends do not change.

## What changed

- **New module `easycrypt/time_by_role.rs`.** `TimeByRole` holds the sums of the records of
  one oracle: per **Sentence role** the count, the time, the failed sentences (status `error`
  or `interrupted`) and the largest `bytes`; the `interrupt` and `respawn` counts and
  times; the `between` time; and the sums of story 55's `timing` (`None` while no answer had
  `timing`). `render` writes the table, one row per role that occurred, in the order of the
  glossary, then the event rows and the `EasyCrypt:` line. When the rows do not sum to the
  oracle's EasyCrypt time within 1 %, it adds a warning line. The data is boxed, so that
  `OracleStats` stays small (clippy `large_enum_variant` on `Lockstep`).
- **`session.rs`.** The `Clock` moved from the transcript sink into the session. Thus each
  record's `ms` is computed also with no sink, and also after a failed capped write dropped
  the sink. The session adds each sentence and each event record to the `TimeByRole` of the
  context's oracle, at the place where it writes the record, with the same `ms`. Records of no
  oracle go in no table. `take_time_by_role(oracle)` gives the table and forgets it.
- **`tactics/driver.rs`.** `OracleStats` has a new field `time`.
- **`tactics/mod.rs`.** At the end of an oracle (the walk has left the oracle's context, which
  wrote its last `between` record), the table goes into the oracle's stats. After a respawn,
  the table of the new session for the sealed oracle (the `respawn` record and the `resume`
  sentences) is merged into it. `EquivalenceTactics::render` writes the table under the
  `goals closed` line. An oracle with an empty table has no table: a resumed oracle, an oracle
  with a problem, and the oracle in flight in a write before its end. The theorem's last line
  does not change.

## Tests

- `time_by_role::tests`: the table text from known sums (rows in glossary order, events,
  no timing); the warning when the rows miss the time by more than 1 %; the `EasyCrypt:` line
  from two answers with `timing`; a merge.
- `tactics::tests::the_report_shows_each_oracles_time_by_role_under_its_goals_closed_line`
  and `an_oracle_without_records_has_no_time_by_role_table`.
- `session::tests::the_time_by_role_is_whole_after_the_transcript_was_dropped`: the capped
  sink fails at its first write; the table still counts every sentence of the oracle.
- Real EasyCrypt (`--features cvc5-lib`, `DOMINO_EASYCRYPT` set): on hello-world the table
  total is equal to the sum of the oracle's records; in the respawn test the sealed oracle has
  the `respawns 1` and `resume` rows.

### Test bugs found and fixed

These tests run only with `--features cvc5-lib` and `DOMINO_EASYCRYPT`. Story 56 did not run
them in that configuration.

- `tagged_sentences` and `sentences` read `sentence` from every record. Event records (story
  56) have none, and the tests panicked. They now skip event records.
- `two_runs_on_an_unchanged_project_write_the_same_file` and
  `the_page_is_the_same_under_a_capped_and_a_full_transcript` compared the page's transcript
  record numbers. A Domino gap of 100 ms or more is a `between` record, so the numbers change
  with the load. The tests now compare the page without these numbers (`stable_page`).
- On hello-world the sum of the records was 1 ms more than the EasyCrypt time once (432 vs
  431 ms): each `ms` is cut from one total over all oracles. The test allows 1 ms.
- `crates/domino/tests`: `stable_stdout` now leaves out the table, whose times change from
  run to run.

## Runs on `example-projects/4WHS` (Full4WHS)

Release build with `cvc5-lib`, two proofsteps at the same time on one machine.

**H0 ~ H1_0** (proofstep 0): 12 oracles, 100 goals closed, 0 admits, 224.6 s. No oracle has
the sum warning. Send3:

```
  Send3: lockstep 9 joint paths, 35 nodes, 0 stuck points (5.4s)
    goals closed: 17, no admit, fallbacks: 0, EasyCrypt time 48.8s (15 attempts undone)
    time by role           count      time   failed   largest answer
      quick close            27     39.3s       15           0.7 MB
      structure              27      6.0s        0           0.7 MB
      leaf fallback           5      1.1s        0           0.5 MB
      interrupts             17      1.7s
      respawns                0        0s
      Domino between          —      0.7s
    EasyCrypt: tactic 43.1s (smt 26.4s: translate 1.7s, prepare 20.5s, prover 4.2s;
               26 calls: 16 valid, 0 timeout, 10 unknown), serialize 3.8s
```

**H4 ~ H5** (proofstep 7): stopped by the 10-minute limit in Send3. Four oracles are done; no
sum warning. Send1:

```
  Send1: lockstep 6 joint paths, 20 nodes, 0 stuck points (5.6s)
    goals closed: 29, no admit, fallbacks: 0, EasyCrypt time 149.2s (27 attempts undone)
    time by role           count      time   failed   largest answer
      quick close            21     22.0s       14           0.5 MB
      structure              26      2.3s        0           0.5 MB
      leaf fallback           9     17.4s        3           2.0 MB
      reduce                  3      1.5s        0           4.3 MB
      split                  27     23.4s        0           4.8 MB
      part fallback          27    1m 19s       10           4.8 MB
      undo                    1      0.1s        0           0.5 MB
      interrupts             10      0.8s
      respawns                0        0s
      Domino between          —      2.1s
    EasyCrypt: tactic 1m 36s (smt 1m 25s: translate 1.5s, prepare 34.1s, prover 50.4s;
               47 calls: 25 valid, 8 timeout, 14 unknown), serialize 26.0s
```

**Which role costs the most:**

- H0 ~ H1_0: the **quick close**. In Send3 it is 39.3 s of 48.8 s (15 of 27 failed), in Send4
  37.6 s of 44.1 s (13 of 27 failed). In the smt time, Why3's `prepare` (20.5 s) is much more
  than the prover (4.2 s).
- H4 ~ H5: the **part fallback**. In Send1 it is 1m 19s of 149.2 s, in Send2 1m 45s of
  180.8 s. Then `split` and the quick close. The answers of `split` and the part fallbacks are
  up to 4.8-5.1 MB, and serialize is 26-28 s per oracle.

## Open items

- **H2_1 ~ H3_0 is not given.** Its Send3 takes much longer than the 10-minute limit (story 56
  had the same problem). The H0 ~ H1_0 and H4 ~ H5 tables are given in its place.
- H4 ~ H5 Send3 and Send4/Send5 were not finished. The check "within 1 % for every oracle of a
  Full4WHS run" is shown for 16 oracles (all with no warning), not for a full run.
- `session::tests::an_interrupt_never_answered_is_unresponsive_after_six_signals` failed once
  in the whole `cvc5-lib` suite (busy machine) and passed 3 times alone (known, story 56).

## Rejected alternatives

- The three of the story (one line per leaf, a separate report file, a table computed from
  the transcript).
- **Sums kept in the transcript sink.** Rejected: a failed capped write drops the sink, and
  with it the sums.
- **Sums kept by the driver (`Prover`).** Rejected: the session writes the interrupt,
  `between` and `undo` records, and the respawn uses a new `Prover`-less session.
- **`Box<OracleEnd>` in `Lockstep::Ended`.** Rejected: clippy then warned about `Walk`. The
  table boxes its own data.
