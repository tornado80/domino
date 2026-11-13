# Story 107 — Hop 12 of Full4WHS closes with the reduction walk

**Epic:** EasyCrypt export: the reduction walk — `docs/stories/easycrypt/epic-the-reduction-walk.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 106.
**Blocks:** —
**ADR:** `docs/adr/0024-a-reductions-oracle-lemma-is-proved-by-a-strict-reduction-walk.md`.
**Decisions:** owner's grilling session of 2026-11-12/13, Question 10 (layer 3).

An **acceptance** story: one manual run on a large project, and an implementation report. A Rust
change only if the run finds a defect, and then with a test on a small fixture first.

---

## 1. Why this story exists

The fixtures of story 106 are small. Hop 12 of Full4WHS (`H7_1 ~ H7_0`, the MAC reduction) is the
case that started this epic: on 2026-11-11 the blind walk took 26 minutes on `Send2` alone and left
one `program-mismatch` admit.

## 2. The facts this story uses

- The project: `domino-lang/domino-amir-easycrypt-export/example-projects/4WHS` (its
  `KX_noprfkey` has `ReverseMac`).
- The blind-walk baseline: `ec4whs/newtranslation/Full4WHS/progress/Red_H7_1_H7_0/*/report.txt`
  (2026-11-11). `Send2`: 200 goals closed, 1 admit, 1560 s of EasyCrypt time, 468 undone attempts.
- A proof file belongs to the program files it was generated with. Do not copy it into another
  translation (2026-11-12: `ni1` against `ni2`).

## 3. What to do

1. `domino easycrypt export` of the project into a fresh directory, then
   `domino easycrypt prove --gamehop 12` in that directory, with the default timeouts.
2. Compile the whole tree with EasyCrypt.
3. Write the implementation report with, for each oracle of `Red_H7_1_H7_0`: admits by reason,
   EasyCrypt time, undone attempts, and the same numbers from the blind-walk baseline.
4. For each admit: its claim, the EasyCrypt goal at that place (`easycrypt llm -upto`), and its
   cause.

## 4. Acceptance criteria

- [ ] All oracle lemmas of `Red_H7_1_H7_0` close with no `admit`, and the tree compiles; or each
      remaining admit has a cause in the report and a follow-up story.
- [ ] `Send2` takes less EasyCrypt time than the baseline (1560 s).
- [ ] The report compares all oracles with the baseline.
