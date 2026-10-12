# Story 63 — `sp` only before a two-sided step

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 27, 50.
**Blocks:** 64 (do it first, so that the leaf gets a precondition without extra existentials).

A **tactics** story, Rust only. Translation does not change.

---

## 1. Why this story exists

`step_node` (`src/easycrypt/tactics/driver.rs:1340`) sends `sp k l.` (`sp_front`) before every
node that is not a leaf. That includes a **determined** node, where the next sentence is
`rcondt{i} ^if` or `rcondf{i} ^if`. `rcondt{i} ^if` does not need `sp`: its side goal is a `hoare`
on the code before the `if`, so it reasons about that code itself.

Each `sp` adds `exists x_L` and program-variable equations to the precondition. In H2_1 ~ H3_0,
Send1 J1, the premise became 470 KB with 34 existentials and four copies of the invariant
(`Eq_H2_1_H3_0_Reproved.md` §2.1, §4.5). Every later side goal and leaf carries that premise.

Count in the transcripts of 2026-10-08 (all hops): 1,408 `sp k l.` sentences. **1,018** come right
before `rcondt`/`rcondf` at a determined node. 390 come before a two-sided step: `if.` at a
synchronized node (256), `if{1}.` at a split node or the router (116), `seq` at a sampling (18).

Vocabulary (`CONTEXT.md`): **Joint node**, **Exit guard**.

## 2. Inherited from earlier stories

- **Story 27:** the walk of the joint tree; `determined`, `synchronized`, `split`, `sampling`.
- **Story 52:** the side goal of `rcondt`/`rcondf` gets the quick close in the same sentence
  (`rcondt{i} ^if; 1: auto => /#.`), else the side-goal fallbacks.

## 3. Work to do

- `sp_front` moves out of `step_node` into the steps that need both programs' heads at the same
  place: `synchronized` (`if.`), `split` (`if{1}.` for a two-sided branch) and `sampling` (`seq`).
- `determined` sends `rcondt{i} ^if` / `rcondf{i} ^if` with no `sp` before it.
- The straight-line code that is left stays in the programs until the next two-sided step or the
  leaf. At the leaf, story 64's `auto` (wp) runs over it backwards, which adds no existentials.
- `--no-quick-close` does not change: it turns off only the quick close on program goals, and the
  side goal of `rcondt`/`rcondf` still gets `auto => /#` first.

### Rejected alternatives

- **Keep `sp` before every node.** It is the source of the existentials above.
- **No `sp` at all; `seq` with a computed cut** before each two-sided step. No existentials
  anywhere, but Domino would have to write the assertion of each `seq`. A larger change with
  unknown unknowns.

## 4. Acceptance criteria

- [ ] A unit test of the driver: at a determined node, the first sentence is `rcondt{…}`/`rcondf{…}`,
      not `sp`.
- [ ] A unit test: at a synchronized node, `sp k l.` still comes before `if.`
- [ ] The implementation report gives, for H2_1 ~ H3_0, the number of `sp` sentences and the
      number of `branch-condition` and `side-goal` admits, before (2026-10-08) and after. If the
      side-goal admits go up, the report says at which nodes.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --proofstep 4 --tactics
grep -c '"sentence":"sp ' <out>/progress/Eq_H2_1_H3_0/ec-transcript.jsonl
```
