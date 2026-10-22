# Story 90 — The case split substitutes the binder, merges equal keys, and a timed-out part gets more time

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 66 (the key case split), 89 (each case closed or admitted on its own).
**Blocks:** nothing.
**ADR:** none.
**Decisions:** owner's request of 2026-10-22 ("create a story to fix 1–3" of the H6_1_1 ~ H7_0
investigation, §1). The owner's review of the first draft (same day): the retry is **off by default**
and turned on by passing its timeout, and the timeout goes into the `smt` call itself
(`smt timeout=N wantedlemmas=(…)`), not through the `prover` command, so the prover timeout
never changes. Open questions in §7; §3 uses the recommended answers.

A **tactics** story, Rust only. Translation does not change. Test-first.

---

## 1. Why this story exists

In the `ec4whs` run of 2026-10-22 (commit `5758868`, stories 86–89), H6_1_1 ~ H7_0 went from 81 to
84 admits. The key case split ran on 23 parts and made 64 cases. 26 cases closed and 38 were
admitted, and only 3 parts closed completely. An investigation that took each admitted leaf
on its own (`easycrypt llm -upto`, every other leaf admitted) found three causes:

1. **`->` loses the hypotheses about the binder.** The leaf introduces the part's premises
   (`move => hpre2`, `move => hpre3`) *before* the split, and they mention the binder:
   `hpre3 : d_Fresh{2}.[ctr1] = Some true`. `case (ctr1 = ctr0{2}) => [->|?].` rewrites `ctr1`
   in the **conclusion only** and drops the equation. After it, nothing links `hpre3` to the
   goal. In Send3 J1 the goal can't be proved without `hpre3`: the H7 state holds `Some kmac`,
   and the claim holds only because this session isn't fresh. With `->` this case fails even
   with a 30 s prover timeout. Story 89 §3.2 assumed that "`->` substitutes the binder"; it
   doesn't. `->>` does: it substitutes everywhere, hypotheses included (EasyCrypt `IPSubst`,
   like `subst`).
2. **The split treats equal keys as distinct.** Both games write their map at their own
   counter, so `key_pairs` gives `(ctr1, ctr0{2})` and `(ctr1, ctr0{1})`. The two keys are
   equal (`ctr0{i} = ctr{i}` from `sp`, `ctr{1} = ctr{2}` from `={arg}`), so the case
   `ctr1 <> ctr0{2}, ctr1 = ctr0{1}` is contradictory. It still costs a crush, and with `->` it
   was one more admit.
3. **Many parts need more than smt's 3 s.** EasyCrypt's prover timeout is 3 s (Domino doesn't
   change it, and `--ec-timeout` limits only the sentence). The hypotheses of a Send3 leaf are
   about 400 KB, mostly the `exists` that `sp` adds around the whole precondition.

Measured on the 84 admits of H6_1_1 ~ H7_0, each leaf alone, closing sentence unchanged (Domino's
crush `move: <premises> => />; smt(get_setE mem_set remE mem_rem emptyE).`):

| | 3 s | 30 s |
|---|---|---|
| Case admits, `[->\|?]` (today) | 1 of 38 | — (Send3 J1 still fails) |
| Case admits, `[->>\|?]` | 28 of 38 | **38 of 38** |
| Other admits: equal-output 5, `StateRelation_invariant` 4, `state_equality` 4, `kmac_consistent` 6, `prf_equality` 2 | 0 (they were admitted at 3 s) | **18 of 21** |
| `branch-condition` 19, `side-goal` 6 | 0 | 0 (out of scope, §4) |

So with 1–3 the hop would go from 84 admits to 28. The scripts and output of these measurements
are in the investigation notes (session of 2026-10-22). §6 asks for the same numbers from a real
run.

## 2. What the split and the fallbacks should do

1. The case sentence substitutes: `case (b = k) => [->>|?].`
2. Before the split, keys of one binder that EasyCrypt can prove equal are merged: one `case` per
   class of equal keys, with the equation kept as a named hypothesis.
3. **On demand** (`--smt-retry-timeout <SECONDS>`): a part whose last closing sentence failed with
   `smt: timeout` gets that sentence once more, with the timeout in its `smt` call. This applies
   to the last fallback of `atom` and to each case of the split. Without the option nothing
   changes.

## 3. Work to do

### 3.1 `->>` in `split_cases`

`split_cases` (`driver.rs`) sends `case ({binder} = {key}) => [->>|?].`. Nothing else in the split
changes. In the `=` case the binder is gone from the context, so the remaining pairs of the
same binder are dropped, as today (`equal` filters by `binder`). The case note keeps its text
(` (case ctr1 = ctr0{2})`).

The binder is always a local introduced by the opening loop (`move => ctr1 /=.`), so the
substitution can't be refused for a reason the old `->` didn't share. If EasyCrypt refuses
it, the split is undone as today (story 89 §3.1).

### 3.2 Equal keys are merged

How to tell whether two keys are the same: **ask EasyCrypt, in the leaf's own context, with
no smt.** For each binder whose pairs have two or more keys, and for each two of those keys
`k`, `k'` (in `key_pairs` order), before the first `case`:

```
have <h> : k = k' by move: <premises> => />.
```

`<h>` is `fresh_name(goal, "hk")`, and `<premises>` are the leaf's premises, as in the crush
(`self.premises`). With no premises the sentence is `have <h> : k = k' by done.`

- **Accepted:** the keys are equal. `k'` is dropped from the pairs of this binder (the first key of
  a class is kept), and `<h>` stays in the context. `move:` in later crushes doesn't name it,
  so it stays there and `smt` sees it. In the `<>` case it gives `ctr1 <> ctr0{1}` from
  `ctr1 <> ctr0{2}`.
- **Refused:** the keys are treated as distinct, as today. Nothing is undone: a refused
  sentence leaves no trace.
- The `have` sentences are part of the split: if the split is undone (no case closed, story 89
  §3.3), they're undone with it.

Why this test and not another (rejected alternatives in §4):

- **It's sound.** The merge is kept only if EasyCrypt checked the equation. A wrong merge would
  lose a case, and that can't happen here.
- **It's cheap.** In H6_1_1 ~ H7_0 Send3 J1, `have hc : ctr0{1} = ctr0{2} by move: hpre => />.`
  was accepted in well under a second: the crush substitutes the `sp` equations
  `ctr0{i} = ctr{i}` and the precondition's `ctr{1} = ctr{2}`. No `smt` is called, so it
  can't time out.
- **It uses the information where it already is.** Domino's lockstep knows that the arguments
  are equal, but the keys in the goal are EasyCrypt terms (`ctr0{2}`), and story 66 §1 decided
  not to map them back to SMT names.

At most `MAX_KEY_PAIRS` (6) keys, so at most 15 `have` attempts per part. In the `ec4whs` parts
there's one binder with 2 keys: one attempt.

### 3.3 On demand, a timed-out closing sentence is tried again with more time

A new option of `prove` (also of `--side-inv` and `--pkg-inv`, which use the same driver):

```
--smt-retry-timeout <SECONDS>   Retry a part's closing sentence once, with this smt timeout,
                                after it failed with `smt: timeout`. Off unless given
```

`TacticsOptions` gets `smt_retry_timeout: Option<u32>`, `None` by default, like `leaf_budget`.
Without the option there's no retry, and the proof scripts and transcripts are the same as
today. `--smt-retry-timeout 0` is refused by the argument parser (a value of at least 1 is
required).

Where: the last fallback of `atom` (the crush, or `smt(<hints>).` with no premises), and the
closing sentence of each case in `close_case`. Not in the first fallbacks (`smt().`,
`smt(<hints>).` when a crush follows), not at side goals or branch conditions (§4).

When: only if that sentence failed and `last_smt == Some(SmtOutcome::Timeout)`. A sentence that
failed with `unknown` or `error` isn't retried: more time doesn't help there.

How: one sentence, the same closing sentence with its `smt` call carrying the timeout. The
lemma list moves into the `wantedlemmas` option:

| Closing sentence | Retry |
|---|---|
| `move: <premises> => />; smt(<hints>).` | `move: <premises> => />; smt timeout=<SECONDS> wantedlemmas=(<hints>).` |
| `smt(<hints>).` (no premises) | `smt timeout=<SECONDS> wantedlemmas=(<hints>).` |

- **Why this is the same `smt`.** In EasyCrypt's parser, `smt(l)` is
  `Psmt (SMT.mk_smt_option [`WANTEDLEMMAS l])`. `smt timeout=N wantedlemmas=(l)` goes through
  `smt_info` (`TIMEOUT EQ word`, and `lident EQ smt_option` with a dbhint `paren(dbmap1*)`) to
  `mk_smt_option [`TIMEOUT N; `WANTEDLEMMAS l]`. Only the timeout differs.
- **The prover timeout doesn't change.** `process_smt` (`ecHiGoal.ml`) merges the call's options into
  a copy of the scope's prover settings (`ttenv.tt_provers pi`), for that call only. Nothing
  needs resetting, and nothing depends on undo.
- Checked by hand in `ec4whs` (Send3 J5 of H6_1_1 ~ H7_0, the `ctr1 = ctr0{2}` case with
  `[->>|?]`): `smt(get_setE mem_set remE mem_rem emptyE).` fails at 3 s, and
  `smt timeout=30 wantedlemmas=(get_setE mem_set remE mem_rem emptyE).` closes the goal (19 s
  for the whole compile).
- The retry sentence is built from the same parts as the closing sentence (premises, hint
  list). It isn't made by editing the text of `hint_sentence()`.
- `--ec-timeout` must be at least the retry timeout plus some margin. If `--ec-timeout` <
  `--smt-retry-timeout` + 10, `prove` refuses to start, with a message naming both options.
- The leaf budget (`--leaf-budget`) is checked before the retry, as before a case's crush (story
  89 §3.4). Once it's spent there's no retry.
- `last_smt` after a retry is the retry's outcome, so an admit after a failed retry says
  `smt: timeout` as today.

### 3.4 Reports

- With the option, the report's summary line for an oracle counts retries: `… ; 12 parts
  retried with 30 s, 9 closed`. Without it the line is as today.
- The live page shows the retry as its own attempt: "retry with 30 s prover timeout".
- `Role` gets no new variant: the retry is the same fallback (`PartFallback { n, part }`) with
  `Closing::Fallback { k, of }` unchanged; the transcript tells it apart by its sentences.
- `scripts/proof_statistics.py` counts retries and how many of them closed, per hop and per side
  invariant.

## 4. Rejected alternatives

- **Merge keys by their text**: `x{1}` and `x{2}` with the same variable name. That's a guess:
  in a hop where the games index their tables differently it would drop a real case. It may
  still be a useful *order* in which to try the `have`s, if §7 Q2 shows a cost.
- **Merge keys by asking cvc5** with Domino's path condition. That needs a mapping from EasyCrypt
  terms to SMT names, which story 66 §1 rejected (`src/debug/effect.rs` is human-facing and
  lossy).
- **`have … by smt().`** for key equality. The crush alone proves the `ec4whs` cases with no
  prover. `smt` over a 400 KB context costs up to 3 s per attempt, and up to 15 attempts per
  part.
- **`rewrite -<h>` in the `=` case** (turn `ctr0{2}` into `ctr0{1}` so both reads become
  `get_set_sameE`). It worked by hand, but `->>` plus `<h>` in the context closed every measured
  case without it, and it's one more sentence that can fail.
- **`[hc|hc]`** (name the equation and keep it, no substitution). smt would see `ctr1 = ctr0{2}`,
  but `get_setE` reads would not reduce syntactically, and the crush's `/>` would not use it.
  `->>` gives smt a smaller goal.
- **`prover timeout=N.` before the retry and `prover timeout=3.` after it** (the first draft).
  It works mid-proof, but it changes the prover setting for everything that follows. A failed
  retry would then depend on EasyCrypt's undo restoring the setting, and the reset has to know
  the run's timeout. The `smt` option is local to the call (§3.3).
- **Retry on by default.** The owner wants today's behaviour unless the option is given: the
  retry adds EasyCrypt time to every timed-out part.
- **Raise the prover timeout for the whole run** (`easycrypt -timeout 30`). Every failing `smt` would
  then cost 30 s: H6_1_1 ~ H7_0 had 1,224 failed splits by meaning and 436 failed part fallbacks.
- **Retry `branch-condition` and `side-goal` with more time.** None of the 25 in H6_1_1 ~ H7_0
  closed at 30 s with the side-goal tactics Domino uses elsewhere. They need their own story.

## 5. Tests first

- [ ] Red: the story 66/89 scripted session (`case (c = Comp_H3.M.k{2})`): the case sentence is
      `case (c = Comp_H3.M.k{2}) => [->>|?].`
- [ ] Two pairs of one binder whose keys EasyCrypt proves equal (scripted `have` accepted): one
      `have hk : k = k' by move: <premises> => />.`, one `case`, two cases. No case on `k'`.
- [ ] Same, `have` refused: no `have` in the script, the split on both keys as today.
- [ ] `hk` already taken: the name is `fresh_name` (`hk1`).
- [ ] A split that is undone (no case closed) also undoes the `have`.
- [ ] No premises: `have hk : k = k' by done.`
- [ ] `TacticsOptions::default().smt_retry_timeout` is `None`. Without the option, a crush that
      fails with `timeout` is not retried, and the script is byte-identical to today's.
- [ ] With `--smt-retry-timeout 30`, a crush that fails with `timeout`: the next sentence is
      `move: <premises> => />; smt timeout=30 wantedlemmas=(<hints>).`; on success it's in the
      script, and no `prover` sentence is sent anywhere.
- [ ] No premises: the retry is `smt timeout=30 wantedlemmas=(<hints>).`
- [ ] Retry fails: the retry isn't in the script, and the admit says `smt: timeout`.
- [ ] A crush that fails with `unknown` or `error`: no retry.
- [ ] `smt().` and `smt(<hints>).` before a crush: no retry, even on `timeout`.
- [ ] A case of the split whose crush times out: retried as above, the case closed or admitted
      as story 89.
- [ ] `--smt-retry-timeout 0`: refused by the parser.
- [ ] `--ec-timeout 30 --smt-retry-timeout 30`: `prove` refuses to start, naming both options.
- [ ] Leaf budget spent: no retry.
- [ ] `report.txt` counts retries with the option (§3.4) and is unchanged without it.

## 6. Acceptance criteria

- [ ] All tests of §5 green; `cargo clippy` clean.
- [ ] Measure first, by hand, in `ec4whs`: the retry sentence inside a case bullet after
      `case … => [->>|?].`, then a plain `smt(<hints>).` on a later goal that needs more than
      3 s fails as before (the timeout didn't leak).
- [ ] `ec4whs`, proofstep 11 (H6_1_1 ~ H7_0) with `--force`, **without** the option: report
      admits by type, cases closed and admitted, `have`s accepted and refused, and the change in
      wall and EasyCrypt time of Send3. Target from §1: at most 38 admits (28 of the 38 case
      admits close at 3 s).
- [ ] The same **with** `--smt-retry-timeout 30`: also retries and retries closed. Target from §1:
      at most 28 admits; every case admit of today closes (38 of 38).
- [ ] Proofsteps 8 and 10 (H5 ~ H6_0, H6_1_0 ~ H6_1_1) with `--force`, without and with the option:
      the same numbers. No hop gets more admits than in the run of 2026-10-22.
- [ ] `--side-inv H6` and `H7` with `--force`, with the option: the same numbers (the side tree
      has one memory, `ctr0{hr}`, so no `have` is expected). Measured by hand on the 8 `H7`
      game-invariant admits of the run of 2026-10-21 (each leaf alone, the crush
      `move: hpre … hpre4 => />` unchanged): `smt(<hints>)` closes 0 at 3 s, and
      `smt timeout=30 wantedlemmas=(<hints>)` closes 7, in 4–15 s of smt each. The eighth (Send1
      J1, `fresh_sid_authenticated_by_mac2`) fails at 120 s. With
      `case (ctr1 = ctr{hr}) => [->>|?]` its `<>` case closes at 3 s. Its `=` case needs the
      old `early_fresh_session_has_no_complete_transcript` at the written key `ctr{hr}`, which
      smt doesn't find even at 30 s, but which closes in 2 s when given explicitly (`have := hef
      ctr{hr}`). That is a follow-up (instantiate the old invariant at the written key), not this
      story.
- [ ] `Proof_Statistics.md` in `ec4whs` updated, with the retries counted.

## 7. Open questions

1. **Which value to pass for `ec4whs`?** The option has no default (§3.3). Recommended for the
   §6 runs: 30. Every measured leaf that closed did so in under 60 s of EasyCrypt time per leaf,
   setup included, under 6–8 parallel jobs. The ones that failed at 30 s were the 25 side goals
   and branch conditions, which a longer time didn't change.
2. **Try the `have` for every two keys, or only for keys of the same variable at both memories
   (`x{1}`, `x{2}`)?** Recommended: every two keys. The cost is one crush with no smt per pair,
   and it doesn't guess. Revisit if §6 shows a cost.
3. **Retry the first fallbacks too (`smt().`, `smt(<hints>).`)?** Recommended: no. The crush is
   the last fallback and has the most help (`/>`). A retry of each would triple the cost of a
   failing part.
