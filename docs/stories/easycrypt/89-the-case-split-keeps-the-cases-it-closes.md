# Story 89 — The case split keeps the cases it closes

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 65 (part fallbacks), 66 (the key case split), 88 (the split sees reads under
projections; without it the split reaches only 12 parts of `ec4whs`).
**Blocks:** nothing.
**ADR:** none.
**Decisions:** owner's request of 2026-10-22: "admit one case and go to the other cases, and if
that fails we also admit but don't remove the casing", and "use the move as the only fallback
for each case". Open questions in §7. §3 uses the recommended answers; §7 Q1 is where the
recommendation differs from the request.

A **tactics** story, Rust only. Test-first.

---

## 1. Why this story exists

Part fallback 4 (`key_case_split`, `driver.rs`) splits a part on `case (b = k) => [->|?].` for each
key pair, each case a bullet, and ends each case with `smt(<hints>)`. It is kept only if **every**
case closes: `split_cases` stops at the first case that fails, and `key_case_split` undoes the whole
split and admits the part as it was.

In the `ec4whs` runs of 2026-10-21 (commit `952a168`) the split ran 12 times (Send3 of H5 ~ H6_0: 3,
of H6_1_1 ~ H7_0: 9, all `StateRelation_relation_state_equality`). Each time EasyCrypt accepted the
`case`, the first case (`ctr1 = ctr0{i}`, substituted) failed its `smt`, and the split was undone.
**The second case (`ctr1 <> ctr0{i}`) was never tried.** So we do not know how many of these parts
are half provable, and the admit says nothing about which case is hard.

The two cases are not equally hard. In the `<>` case the update `m.[ctr0 <- v].[ctr1]` reduces to
`m.[ctr1]` (`get_setE`), and the claim is the old relation at `ctr1`, which is in the premise. In
the `=` case the claim is about the value just written, the part that needs the program's
reasoning. Keeping the closed case and admitting only the hard one leaves a smaller, more precise
admit for the hand proof.

With story 88 the split also reaches the 108 side-invariant parts that fail fallbacks 1–3, all of
the shape `(oget State.[ctr0 <- state].[ctr1]).`k …`, where the same reasoning applies.

### 1.1 What a case is closed with

Today a case gets one sentence, `smt(<hints>).` (story 66 §3). It never gets the crush of part
fallback 3, `move: <premises> => />; smt(<hints>).`, which in the side invariants is the fallback
that works: 515 parts closed there against 1,863 by `smt(<hints>)` alone, and the parts that reach
the split are those where `smt(<hints>)` already failed on the whole part. In the 12 hop attempts
the one `smt` of the first case took 4.1 s on average, about the prover timeout.

## 2. What the split should do

For a part with key pairs:

1. Send the `case` sentences as today (each a bullet, story 66 order).
2. In every case, send the crush `move: <premises> => />; smt(<hints>).` as the only closing
   sentence (`smt(<hints>).` when the leaf introduced no premises). If it fails, **admit that
   case** and go on to the next case instead of stopping.
3. At the end:
   - every case closed: the part is closed (as today);
   - at least one case closed: keep the split, with the failed cases admitted;
   - no case closed: undo the split and admit the part once, as today (§7 Q1).

## 3. Work to do

### 3.1 `split_cases` admits a case it cannot close

`split_cases` returns a `CaseTally { closed, admitted }` instead of `bool`. At a leaf (no pair
left), the case's closing sentence is sent (§3.2); on a failure the case is admitted with
`admit_part(node, pair, part, note)`.
`note` names the case path: ` (case ctr1 = ctr0{2})`, ` (case ctr1 <> ctr0{2})`, nested cases
joined with `, `. Both bullets are always walked (no `&&` short-circuit).

If EasyCrypt refuses a `case` sentence, or it does not give exactly two goals (`count() != before +
1`), that is not a case to admit: the whole split is undone as today.

### 3.2 A case is closed with the crush

`key_case_split` gets the case's closing sentence from `atom` instead of `hints`: the fallback 3
sentence `move: <premises> => />; <hints>` when `self.premises` is not empty, else `hints`. It is the
only closing attempt of a case: no `smt().` and no `smt(<hints>).` before it.

- The crush runs after the `case`, on each case's goal. The premises keep their names through the
  split: `->` substitutes the binder (`ctr1`) by the key, and `?` adds the disequality as an
  unnamed hypothesis. The disequality stays in the context, where `smt` sees it; `move:` does not
  move it.
- The case is closed when EasyCrypt accepts the sentence and the goal count drops, as in
  `try_close`.
- `last_smt` is the outcome of the crush's `smt`, so a case admit shows it (story 65 admit comment).

### 3.3 `key_case_split` keeps or undoes

- `admitted == 0`: closed, as today.
- `closed > 0 && admitted > 0`: keep. The part's outcome is "partly closed": each admitted case is
  an admit of the part with its note.
- `closed == 0`: roll back to the snapshot and admit the part once, with the last `smt` outcome, as
  today.

The reason of a case admit is the part's own (`pair_view(p, part)`): a case is the part's goal
under one more hypothesis, so a part Domino verified is verified in each case.

### 3.4 The leaf budget

Today an attempt costs one `case` and at most one `smt`. After §3.1 it costs up to `2^pairs`
crushes (at most 64 with `MAX_KEY_PAIRS` = 6), one `smt` each. With one pair, as in all the parts of
§1, that is 2: about 8 s for a part whose cases both fail (4.1 s per `smt`, §1.1), about 900 s over
the 108 side-invariant parts. Before each case's crush, check `self.deadline`; once it has passed,
admit the remaining cases without sending anything, with the note ` (case …, leaf time budget
spent)`, and decide keep or undo as in §3.3.

### 3.5 Reports

- The admit lines of `report.txt` carry the case note (they show the claim label already).
- The oracle summary line counts admitted cases apart: `12 admits (… ; 4 of them cases of 3 parts)`.
  An admit count can grow when a part becomes several admitted cases, and the statistics must be
  able to tell a weaker proof from a finer one.
- The live page shows part fallback 4 as "case split: k of n cases closed".

## 4. Rejected alternatives

- **Keep the split even when no case closes** (the owner's wording, §7 Q1). Then one part admit
  becomes `2^pairs` case admits with nothing proved, and the proof file grows by the `case`
  sentences and bullets.
- **Try the `<>` case first.** It is more often the closable one (§1), but trying both is needed
  anyway once failures no longer stop the split; the order only matters for the leaf budget.
  Possible follow-up if §6 shows budget overruns.
- **A ladder in each case** (`smt(<hints>).`, then the crush). The owner chose the crush alone:
  `smt(<hints>)` already failed on the whole part, and a second attempt doubles the cost of a
  failing case.
- **Unfold `get_setE` in the case instead of `smt`.** That is a tactic change for each map
  operation; `smt(<hints>)` already carries `get_setE`.

## 5. Tests first

- [ ] Red: a scripted session (as the story 66 tests in `tests.rs`, the `case (c = Comp_H3.M.k{2})`
      script) where the `=` case's crush fails and the `<>` case's closes. Today: both rolled back,
      one part admit. After: the script keeps the `case` sentence and both bullets, the first with
      `admit.` (note ` (case c = Comp_H3.M.k{2})`), the second with the closing crush.
- [ ] A case's only closing sentence is `move: hpre … => />; smt(<hints>).`; no `smt().` or bare
      `smt(<hints>).` is sent in a case. With no premises, the case's sentence is `smt(<hints>).`
- [ ] Two pairs, 3 of 4 cases close: one admit, with the nested note.
- [ ] No case closes: the script is as today (no `case`, one part admit with the last `smt`
      outcome).
- [ ] Every case closes: as today.
- [ ] A refused `case` sentence: undone, one part admit, as today.
- [ ] The leaf deadline passed after the first case: the remaining cases are admitted without
      crush, with the budget note.
- [ ] The admit reason of a case is the part's (`domino-verified-ec-failed` for a verified part).
- [ ] `report.txt` counts admitted cases apart (§3.5).

## 6. Acceptance criteria

- [ ] All tests of §5 green; `cargo clippy` clean.
- [ ] Measure first (before the implementation, by hand): in `ec4whs`, in one of the 12 parts of §1
      (`Eq_H6_1_1_H7_0_Send3.ec`), replace the part's `admit.` with `case (ctr1 = ctr0{2}) =>
      [->|?]; [admit | move: <premises> => />; smt(get_setE mem_set remE mem_rem emptyE)].`, with
      the premises of the part's fallback 3 sentence in the transcript, and compile. Record in
      the story whether the `<>` case closes, and whether the `=` case closes with the crush.
- [ ] `ec4whs`, proofsteps 8 and 11 with `--force`: report for the 12 parts how many cases close and
      the change in EasyCrypt time of Send3.
- [ ] With story 88: `--side-inv H6`, `H2`, `H7` with `--force`: the same numbers for the 108 parts.
- [ ] No proof file gets an admitted case without a closed case beside it (§3.3).
- [ ] `Proof_Statistics.md` in `ec4whs` counts admitted cases as §3.5 shows.

## 7. Open questions

1. **Keep a split in which no case closes?** The request says yes ("admit but don't remove the
   casing"). Recommended: no. A split with every case admitted proves nothing more than the one
   part admit, and has more admits and more lines (§4). It only shows the cases for a hand proof,
   and the hand prover can write the `case` themselves.
2. **Count a part with an admitted case as one admit or as one per case?** Recommended: one per
   case in the `admit` count (each is an `admit.` EasyCrypt sees), and the "cases of parts" count
   beside it (§3.5).
3. **Lower `MAX_KEY_PAIRS` now that every case is tried?** Recommended: keep 6, use the leaf
   budget (§3.4), and look at the §6 numbers.
