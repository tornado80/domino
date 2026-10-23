# Story 90 — The case split names or substitutes the key equation, merges equal keys, and a timed-out part gets more time

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 66 (the key case split), 89 (each case closed or admitted on its own).
**Blocks:** nothing.
**ADR:** none.
**Decisions:** owner's request of 2026-10-22 ("create a story to fix 1–3" of the H6_1_1 ~ H7_0
investigation, §1). The owner's review of the first draft (same day): the retry is **off by default**
and turned on by passing its timeout, and the timeout goes into the `smt` call itself
(`smt timeout=N wantedlemmas=(…)`), not through the `prover` command, so the prover timeout
never changes. Amended on 2026-10-23 at the owner's request ("amend the stories"), after measuring
the hand proofs of commit `bd8901f` in `ec4whs` (§1.1). In the side tree, the split first tries
one sentence with named cases (§3.5). An index that is a term over a binder, not only a binder,
gets a key pair (§3.6). Open questions in §7; §3 uses the recommended answers.

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

### 1.1 The side tree wants the opposite (measured 2026-10-23)

Commit `bd8901f` in `ec4whs` (`SideInv_H7_{Send1,Send2,Send4,Send5}_Lotta.ec`) closes every
admit of `--side-inv H7` by hand. Six of them, all game-invariant parts, are closed with one
sentence:

```
case (ctr0{hr} = ctr1) => cteq; smt(get_setE).
```

The equation is **named and kept**, nothing is substituted, there's no crush, and one `smt` after
`;` closes both cases. One of the six cases is on a term, not a binder:
`case (ctr0{hr} = oget d_First{hr}.[sid0]) => cteq; smt(get_setE).` (Send5 J3). Each leaf was
measured alone, at EasyCrypt's default 3 s:

| Leaf | Attempt | Result |
|---|---|---|
| The six hand-proved side leaves | the named split as written in the `_Lotta` files | all close (2–5 s per compile) |
| `SideInv_H7_Send1.ec` J1, first conjunct after `do split` (where Domino puts it) | `case (ctr0{hr} = ctr1) => cteq; smt(get_setE).` | closes (2.3 s) |
| same | same, with Domino's five hints | closes |
| same | `case (ctr1 = ctr0{hr}) => [->>\|?]`, then the crush in each case (§3.1) | **fails** |
| The 23 split parts of H6_1_1 ~ H7_0 (38 case admits, 3 parts closed today) | named split, `smt(get_setE)` | **0 of 23**. It also fails on the 3 parts Domino closes today. |
| same | named split, Domino's five hints | 0 of 23 |
| same | named split, then the crush | 11 of 23 parts (16 of 38 case admits) |
| same | `[->>\|?]` and the crush in each case (§1) | 28 of 38 case admits |

So no single case sentence works in both trees. In a hop, smt needs the crush to open the
`exists` that `sp` wraps around the 400 KB precondition, and substitution beats a named
equation. In the side tree, the context is small and the crush hurts. Send1 J1, which story 91
was written for, closes with the named split and no invariant instance.

## 2. What the split and the fallbacks should do

0. In the side tree (and in the package-invariant tree, which has the same one-memory shape), the
   split first sends **one** sentence with named cases that closes every case with `smt(<hints>)`
   (§3.5). If it's accepted, the part is closed. Otherwise the split goes on as below.
1. The case sentence substitutes: `case (b = k) => [->>|?].` (A key pair whose index is a term,
   not a binder, gets named cases, §3.6.)
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
- The summary line also counts parts closed by the named split (§3.5): `… ; 6 parts closed by a
  named split`.

### 3.5 In the side tree, a named split first

Only in the trees with one memory (`--side-inv`, `--pkg-inv`: `hoare` lemmas at `{hr}`), as the
first attempt of the key case split (part fallback 4), after the equal keys are merged (§3.2):

```
case (<b1> = <k1>) => <h1>; case (<b2> = <k2>) => <h2>; smt(<hints>).
```

- One `case … => <hi>;` per key pair, in `key_pairs` order. `<hi>` is `fresh_name(goal, "hc")`, and
  then `hc1`, … for the later pairs. The pairs come after the merge, so a merged key gets no
  `case`.
- `;` sends each `case` to every goal of the one before it, and `smt(<hints>)` to every case. It's
  one sentence. Either all cases close and EasyCrypt accepts it (the goal count drops), or it's
  refused and leaves nothing.
- `<hints>` is the part's hint list, as in `smt(<hints>)`. Measured: `get_setE` alone and the five
  hints both close Send1 J1 (§1.1).
- No crush and no `move:`: the premises stay where the leaf put them. In the hand proofs they're
  still in the conclusion. Where Domino places it, after `move => hpre3`, they're in the
  context. Both close (§1.1).
- Only for parts with at most 2 key pairs (`MAX_NAMED_PAIRS` = 2), so at most 4 `smt` calls in the
  sentence and at most 12 s at the default timeout. A part with more pairs goes straight to the
  per-case split (§7 Q5).
- Not retried with `--smt-retry-timeout`: a retry would give each of up to 4 calls the long
  timeout. The per-case split that follows has the retry.
- The leaf budget is checked before it, as before a case's crush.
- If it's refused, the split goes on as in §2 steps 1–3: per-case bullets, each closed or
  admitted on its own (story 89). The per-case split is what tells a hand prover which case is
  hard.

Not in hops: there it closed 0 of 23 parts (§1.1) and would only add up to 4 failing `smt` per
split part (§7 Q4).

### 3.6 A key pair on a term index

Today `collect_key_pairs` (`goals.rs`) makes a pair only when the read index is a binder:
`index.kind == "local"` and in `binders`. In `SideInv_H7_Send5.ec` J3 and J9 the read is
`d_State.[ctr0 <- v].[oget d_First.[sid0]]`. The index is a term over the binder `sid0`, so
there's no pair and no split. Both are closed by hand with a split on
`ctr0{hr} = oget d_First{hr}.[sid0]` (§1.1; story 91 §1 for J9).

- A read whose index is not a binder, but is a term that mentions a binder from `binders` (as a
  free local), gets a pair `(index term, key)`. `KeyPair` gets `index: String` and
  `binder: Option<String>`, which is `Some` only when the index is a binder.
- The term is printed by a new `term_text` in `goals.rs`, an extension of `atom_text`: atoms,
  `oget t`, a map read `t.[u]`, and a tuple projection ``t.`n``, printed with the operator paths
  as `atom_text` prints program variables. For any other shape it returns `None`, and that read
  gets no pair, as today. The printed term must re-parse in the leaf. A unit test compares it
  with the text EasyCrypt prints for the measured index.
- The named split (§3.5) treats both kinds alike.
- In the per-case split, a pair with `binder == None` can't be substituted: `->>` needs a variable.
  Its case sentence is `case (<index> = <k>) => [<h>|<h>].` (named in both cases). A pair with a
  binder keeps `[->>|?]`. The filter on later pairs in the `=` case (§3.1) applies only to pairs
  of the same binder. A named equation removes nothing.
- The case note prints the term as the case sentence does (` (case oget … .[sid0] = ctr0{hr})`).

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
- **Named cases (`[hc|hc]`) instead of `->>` in hops.** The first draft rejected them because
  `get_setE` reads don't reduce syntactically. In the hops that holds: named cases close 0 of 23
  parts, or 16 of 38 case admits with the crush, against 28 of 38 with `->>` (§1.1). In the side
  tree it's the other way round, so §3.5 uses named cases there, as a first attempt.
- **The named split in every tree.** It closed nothing in the hops (§1.1), including the 3 parts
  closed today. There it would only cost up to 4 failing `smt` per split part.
- **The named split instead of the per-case split in the side tree** (no bullets). When it fails,
  it doesn't say which case is hard. Story 89 keeps the closed cases and admits only the hard
  one, and story 91 works on the `=` case alone.
- **A ladder in each case of the per-case split** (`smt(<hints>)` on a named case, then the crush).
  It costs a failing `smt` in every case of every hop part, and the side tree is served by the
  one-sentence attempt before the bullets.
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
- [ ] Side tree, one key pair, scripted accept: the first split sentence is
      `case (ctr1 = ctr0{hr}) => hc; smt(<hints>).`, and no bullet is sent.
- [ ] Side tree, two pairs: `case (…) => hc; case (…) => hc1; smt(<hints>).`. `hc` taken:
      `fresh_name` gives the next name.
- [ ] Side tree, named split refused: the per-case split follows, with `[->>|?]`, as in the hop.
- [ ] Side tree, three pairs: no named split.
- [ ] Hop tree: no named split, the first split sentence is `case … => [->>|?].`
- [ ] Named split with `--smt-retry-timeout`: the named split isn't retried.
- [ ] `key_pairs`: a read `m.[k <- v].[oget d_First.[sid0]]` with `sid0` in `binders` gives the pair
      `(oget d_First.[sid0], k)` with `binder == None`. A term index with no binder in it gives
      no pair. A term `term_text` can't print gives no pair.
- [ ] Per-case split, term pair: the case sentence is `case (<index> = <k>) => [hc|hc].`, and in the
      `=` case the later pairs are kept.

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
      J1, `fresh_sid_authenticated_by_mac2`) fails at 120 s. With `[->>|?]` its `=` case fails,
      but the named split of §3.5 closes it at 3 s (§1.1).
- [ ] `--side-inv H7 --force`, **without** the option: the parts the hand proofs of `bd8901f` close
      with a named split (Send1 J1, Send4 J1, J2, J6, Send5 J3) close by §3.5 and §3.6. Report
      the parts closed by a named split, those refused, and the change in EasyCrypt time.
- [ ] `--side-inv H2` and `H6` with `--force`, without the option: the same numbers. No side
      invariant gets more admits than in the run of 2026-10-22.
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
4. **The named split in hops too?** Recommended: no (§1.1: 0 of 23). Revisit if a hop with a small
   precondition shows otherwise.
5. **`MAX_NAMED_PAIRS` = 2?** Every measured side-tree split has one pair. Recommended: 2, to keep
   the sentence under `--ec-timeout` at the default prover timeout. Raise it if §6 shows parts
   with three pairs that the per-case split doesn't close.
