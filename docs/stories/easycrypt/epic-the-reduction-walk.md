# Epic — EasyCrypt export: the reduction walk

**Parent epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Follows:** `epic-reductions-without-an-experiment.md` (stories 101–103).
**Branch:** `amir/easycrypt-export`
**ADR:** `docs/adr/0024-a-reductions-oracle-lemma-is-proved-by-a-strict-reduction-walk.md`
(supersedes ADR 0023 decision 5).
**Glossary:** `CONTEXT.md` — **Reduction walk**, **Assumption guard**, **Exit guard**, **Exit path**,
**Reduction router**, **Leaf**, **Leaf part**, **Quick close**, **Fallback sequence**.
**Algorithm:** `docs/proving-algorithm.md` §10.
**Decisions:** owner's grilling session of 2026-11-12/13, Questions 1 to 11.
**Effort:** M.

---

## 1. Goal

After story 103, a reduction's oracle lemmas are proved by the blind walk. It tries every tactic at
each program head and keeps the first one that EasyCrypt accepts. On `Red_H7_1_H7_0_Send2` of
Full4WHS it took 26 minutes, undid 468 attempts, and admitted a correct `seq` because its only
closer, `auto => /#`, timed out.

After this epic, a **reduction walk** proves these lemmas. It knows the shape: the two sides run the
same code, and the right side adds only the assumption game's assumption guards and tail branches.
It sends one step for each program head, never searches, and admits a goal with a precise reason
when the shape is wrong.

## 2. What the epic delivers

| Piece | Where | Story |
|---|---|---|
| A check that a sampled variable is already in `#pre`, with a `seq-post` admit in both walks | `tactics/goals.rs`, `tactics/driver.rs` (`sampling()`) | 104 |
| The shape recognizers: assumption guard, tail branch, exit guard, mismatch shapes | `tactics/reduction_walk.rs` (pure functions) | 105 |
| The reduction walk, its two admit reasons and its report line | `tactics/reduction_walk.rs`, `tactics/driver.rs`, `tactics/mod.rs` | 106 |
| The acceptance run on hop 12 of Full4WHS | `ec4whs/newtranslation/Full4WHS/` (manual) | 107 |

## 3. Out of scope

- Changes to the blind walk. It stays for its other callers.
- Rewriting a `seq` postcondition when the sampled variable is in `#pre`. Story 104 admits it.
- A fix in translation for an oracle that samples into its own argument (cause 2 of the
  2026-10-30 diagnosis). The owner decides that later.
- Lockstep execution for reductions (ADR 0023).
- A check that a proof file belongs to the program files next to it. Domino is run again in the
  directory where the user works (Question 1 of the grilling).

## 4. Stories

| Order | # | Story | File | Depends on |
|---|---|---|---|---|
| 1 | 104 | A sampled variable that `#pre` mentions gets a `seq-post` admit | `104-a-sampled-variable-in-pre-gets-a-seq-post-admit.md` | — |
| 2 | 105 | The reduction walk recognizes the shape of a program head | `105-the-reduction-walk-recognizes-the-shape-of-a-program-head.md` | — |
| 3 | 106 | The reduction walk proves a reduction's oracle lemmas | `106-the-reduction-walk-proves-a-reductions-oracle-lemmas.md` | 104, 105 |
| 4 | 107 | Hop 12 of Full4WHS closes with the reduction walk | `107-hop-12-of-full4whs-closes-with-the-reduction-walk.md` | 106 |
| 5 | 108 | The reduction walk decides an `if` without guessing and closes a leaf by substitution (follow-up of 107: the walk's cost) | `108-the-reduction-walk-decides-an-if-without-guessing-and-closes-a-leaf-by-substitution.md` | 106, 107 |

Stories 104 and 105 are independent. Story 106 joins them. Story 108 came out of story 107's run
(2026-11-13): the walk closed hop 12, but in about the blind walk's time.

## 5. Done when

- [x] Stories 104–107 are done, each with its implementation report.
- [x] `prove` on `reduction-consts` and on the new fixture `reduction-two-calls` leaves no `admit`, and
      the whole tree compiles.
- [x] On hop 12 of Full4WHS, all oracle lemmas of `Red_H7_1_H7_0` close with no `admit`.
- [x] `docs/proving-algorithm.md` §10 describes the walk as built, and the tables of §1.1, §9.1 and
      §9.2 name the new reasons. `docs/easycrypt-export.md` names the reduction walk, not the blind
      walk.
