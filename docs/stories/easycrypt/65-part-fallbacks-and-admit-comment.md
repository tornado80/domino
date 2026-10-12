# Story 65 — The part fallback sequence, and what an admit says

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 55, 64.
**Blocks:** 66.

A **tactics** story, Rust only. Translation does not change.

---

## 1. Why this story exists

### 1.1 The sequence

`atom` (`src/easycrypt/tactics/driver.rs:1691`) tries, on each leaf part: `smt().`, then
`rewrite !get_set_neqE. smt().`, then `smt(<hints>).`, then an admit. The transcripts of
2026-10-08 (all hops):

| Part fallback | Sent | Kept | Time |
|---|---|---|---|
| 1 `smt().` | 3,810 | 2,436 | 35,644 s |
| 2 `rewrite !get_set_neqE.` | 1,374 | **0** | 4,974 s |
| 3 `smt(<hints>).` | 1,374 | 587 | 15,987 s |

Each of the 1,374 `rewrite !get_set_neqE.` answers is "nothing to rewrite". After `sp`, the table
writes are in the premise as equations, not in the goal as `m.[k <- v]`. Each failed answer
also carried the whole front goal (about 4.4 MB).

The Reproved notes (§2.3) found a class of goal that smt cannot close: a hypothesis such as
`(state{1}, msg{1}) = oget (Some ((…), oget (Some ni0{2})))`. Z3, Alt-Ergo and CVC5 all fail
`msg{1} = ni0{2}` (also with `timeout=30`), but `move: h1 => /= [] _ ->` closes it in 0.2 s.
Crush with the premises does this for every hypothesis: it destructs conjunctions, substitutes
`x{1} = e`, reduces `oget (Some …)` and splits tuple equalities. Crush on the part goal alone does
almost nothing, because story 64 already opened it.

### 1.2 The admit comment

Today:

```
admit. (* domino: J1 invariant/Domino_stuff_not_initialized_early; reason: domino-verified-ec-failed; Domino: verified *)
```

For the three Domino reasons, `Domino: …` repeats the reason. The comment does not say why
EasyCrypt failed. Each answer already has `timing.smt` with the counts `valid`, `timeout`,
`unknown` (story 55):

- `timeout`: the goal is too large, or the time is too short;
- `unknown`: the provers stopped without a proof; a lemma is missing, or the claim does not hold
  in EasyCrypt's model.

Vocabulary (`CONTEXT.md`): **Fallback sequence**, **Leaf part**.

## 2. Inherited from earlier stories

- **Story 64:** the parts, and the premises that the opening loop introduced (`hpre`, `hpreN`).
  The driver knows their names.
- **Story 52:** the fallback sequence is fixed and numbered; the live page shows
  `Closing::Fallback { k, of }`.
- **Story 57:** time by role, with `PartFallback { n, part }`.
- `Admit::label` (`driver.rs:113`), `Admit::to_record`, the report's admit lines.

## 3. Work to do

### 3.1 The part fallback sequence

1. `smt().`
2. `smt(<hints>).` (the base lemmas `get_setE mem_set emptyE` and `ssp.toml`'s `smt_hints`)
3. `move: <premises> => />; smt(<hints>).`, where `<premises>` are the premises that the leaf
   procedure introduced, in the order of introduction
4. reserved for the key case split (story 66; until then the sequence has 3 members)
5. otherwise, admit

`rewrite !get_set_neqE.` goes. The live page shows `fallback k of 4` (3 before story 66).

### 3.2 The admit comment and the report line

```
admit. (* domino: J1 StateRelation_stuff_not_initialized_early; domino-verified-ec-failed; smt: timeout *)
```

- The node id, then the claim (the claim operator's name, or nothing for the whole leaf), then the
  reason.
- `Domino: <view>` only when the reason does not already say it (`router`, `stuck`, `seq-post`,
  `program-mismatch`).
- `smt: <outcome>` from the **last** fallback's answer: `timeout` if any prover call timed out,
  else `unknown`, else `error` (EasyCrypt refused the sentence). Omit it when no fallback ran (an
  admit by §3.6).
- The report line has the same fields. Its `goal:` is the goal that the last fallback got (after
  the opening loop), cut to the transcript cap.
- The session record does not change: `domino` is still written, so resume does not change.

### 3.3 Rejected alternatives

- **Crush in every fallback** (`move: P => />; smt().`, then the same with hints). Crush can
  substitute in a direction that hides a fact, so some of the 2,436 parts that `smt()` closes today
  could stop closing.
- **Crush + `smt()` as fallback 2, before hints.** The hints close 43 % of what `smt()` leaves, so
  the known winner comes first.
- **The outcome of every fallback in the comment** (`smt: timeout, hints: unknown, …`). The line
  is long and repeats on most admits; the transcript has the detail.
- **Node and reason only.** No hint why EasyCrypt failed.

## 4. Acceptance criteria

- [ ] A unit test with a scripted session: the sentences of §3.1, in order, on a part that no
      fallback closes. No `get_set_neqE` is sent.
- [ ] A unit test of `Admit::label` for each reason: `Domino:` appears only for `router`, `stuck`,
      `seq-post`, `program-mismatch`; `smt:` shows the last outcome.
- [ ] A session record written before this story is read back without change.
- [ ] The implementation report gives, for H2_1 ~ H3_0, H4 ~ H5 and H6_1_1 ~ H7_0, the kept count
      of each fallback and the admits, before (2026-10-08) and after.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --proofstep 4 --tactics --no-quick-close
grep -o 'smt: [a-z]*' <out>/Eq_H2_1_H3_0*.ec | sort | uniq -c
```
