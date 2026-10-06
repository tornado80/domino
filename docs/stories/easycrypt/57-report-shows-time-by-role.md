# Story 57 — The tactics report shows time by role

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 55 (timing in each answer), 56 (structured `ctx` and event records).
**Blocks:** nothing.

A **report** story, Domino only. The tactics that a run sends do not change.

---

## 1. Why this story exists

The tactics report gives one time per oracle:

```
    goals closed: 31, 24 admits (…), fallbacks: 212, EasyCrypt time 1h 12m 03s (40 attempts undone)
```

(`EquivalenceTactics::render`, `src/easycrypt/tactics/mod.rs:1838-1845`, written to `Eq_<L>_<R>.report.txt`.) To find the cause of a slow
oracle in the Full4WHS analysis, we had to read the transcript with `jq` and `grep`. We found that
failed quick closes were 47–49 % of the time in H1_1 ~ H2_0 and H3_1 ~ H4_0, and that `split.`,
`admit.` and `undo` cost more than the smt calls. The report must show this directly, so that the
owner sees the cause after every run.

Vocabulary (`CONTEXT.md`): **Sentence role**, **Quick close**, **Fallback sequence**,
**Interrupt**, **Respawn**.

## 2. Inherited from earlier stories

- **Story 56:** every sentence record has `ctx.role` and `bytes`. Event records (`interrupt`,
  `respawn`, `between`) hold the time outside sentences. The `ms` of all records of an oracle adds
  up to its EasyCrypt time.
- **Story 55:** each answer has `timing` with `tactic_ms`, `serialize_ms` and, for a prover call,
  `smt.translate_ms`, `smt.prepare_ms`, `smt.prover_ms` and the result counts.
- **Story 35:** the report is written per equivalence (`EquivalenceTactics::render`, `mod.rs:1767`) and per theorem
  (`TheoremTactics::render`, `mod.rs:1876`).
- A resumed run reports only its own time; sentences sent again on resume have role `resume`.

## 3. Work to do

- Collect the sums **while the run sends sentences**, at the place where the transcript record is
  written. Do not read the transcript back: the sums must also exist when the transcript write
  failed (capped mode goes on after a failed write). Keep them in the oracle's stats.
- Under each oracle's `goals closed` line, add a **time by role** table. One row per role that
  occurred, in the order of the glossary, then the rows for the time outside sentences:

  ```
      time by role        count     time   failed   largest answer
        quick close          56    7m 40s      55          1.2 MB
        structure           310    4m 02s       0          0.9 MB
        leaf fallback        88   31m 15s      70          1.4 MB
        split                12    0m 41s       0          1.3 MB
        part fallback       140   18m 20s      96          0.4 MB
        admit                24    0m 30s       0          1.3 MB
        undo                201    2m 10s       0          1.3 MB
        interrupts            9    4m 30s
        respawns              0        0s
        Domino between        —    1m 05s
      EasyCrypt: tactic 58m 12s (smt 51m 40s: translate 2m 10s, prepare 3m 05s, prover 46m 25s;
                 412 calls: 160 valid, 230 timeout, 22 unknown), serialize 0m 48s
  ```

  - `failed`: sentences that EasyCrypt refused or that timed out.
  - `largest answer`: the largest `bytes` of the role.
  - The last line sums story 55's `timing`. If no answer had `timing` (an older fork), print
    `EasyCrypt: no timing in the answers` in its place.
- The rows sum to the oracle's EasyCrypt time within 1 %. Print the sum check only when it fails,
  as a warning line.
- Keep the theorem's last line as it is.

### Rejected alternatives

- **One line per leaf** (time and result of each leaf). Rejected: a Full4WHS equivalence has
  hundreds of leaves, and the report would be too long to read. The transcript has that detail.
- **A separate report file.** Rejected: the owner reads the tactics report after each run; one
  more file is one more place to look.
- **Compute the table from the transcript after the run.** Rejected: a failed transcript write
  would make the table wrong, and the run already has every number in memory.

## 4. Acceptance criteria

- [ ] Each oracle in the tactics report has a time by role table. A unit test renders a report
      from known stats and compares it with the expected text.
- [ ] The rows of the table sum to the oracle's EasyCrypt time within 1 %, for every oracle of a
      Full4WHS run.
- [ ] The EasyCrypt line gives tactic, smt (translate, prepare, prover, result counts) and
      serialize sums. With answers that have no `timing`, the line says so.
- [ ] The table exists when the transcript write failed. A test covers this.
- [ ] The implementation report shows the table for H2_1 ~ H3_0 and H4 ~ H5, and says which role
      costs the most.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --tactics
grep -A16 'time by role' <out>/*/Eq_H2_1_H3_0.report.txt
```
