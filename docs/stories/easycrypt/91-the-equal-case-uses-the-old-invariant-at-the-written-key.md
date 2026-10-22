# Story 91 — The `=` case of a key split uses the old invariant at the written key

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 66 (the key case split), 69 and 77 (side invariants, `side_inv_<C>`), 89 (each case
closed or admitted on its own), 90 (`[->>|?]`; the retry with a longer smt timeout).
**Blocks:** nothing.
**ADR:** none.
**Decisions:** owner's request of 2026-10-22 ("create a story for instantiating the old invariant at
the written key"), after the H7 side-invariant measurements of story 90 §6. Open questions in §7;
§3 uses the recommended answers.

A **translation** change (one lemma per game invariant in `Comp_<C>.ec`) and a **tactics**
change (`close_case`, `driver.rs`). Test-first.

---

## 1. Why this story exists

A side-invariant leaf proves a game invariant `forall ctr, … d_State.[ctr] …` after a write
`d_State.[k <- v]`. The key split (story 66, with story 90's `->>`) leaves two cases:

- **`<>` case** (`ctr1 <> k`): the read reduces to the old `d_State.[ctr1]`, and the claim is the
  old invariant at `ctr1`. smt usually closes it.
- **`=` case** (`ctr1 = k`, substituted): the claim is about the **new** value `v`. It often
  holds because of what the **old** state said at `k`: the program read `oget d_State.[k]`,
  changed a few fields and wrote it back. Some old invariant at `k` (often a different one
  from the claim) rules out the bad values. The fact is in the premise `side_inv_<C> s`, but
  folded: an op over a record, then a conjunction of ops, each a `forall` over a binder. smt
  doesn't find the instance.

Evidence: the one game-invariant admit of `--side-inv H7` that story 90's retry doesn't close
(run of 2026-10-21, `SideInv_H7_Send1.ec` J1, `fresh_sid_authenticated_by_mac2`). Each leaf was
taken alone (`easycrypt llm -upto`, every other leaf admitted):

| Attempt | Result |
|---|---|
| Today's crush `move: hpre … hpre4 => />; smt(<hints>).` | fails at 3 s, 30 s and 120 s |
| `case (ctr1 = ctr{hr}) => [->>\|?]`, crush in each case | `<>` closes at 3 s; `=` fails at 3 s and 30 s |
| `=` case, with `side_inv_H7` unfolded in the goal | fails at 3 s and 30 s |
| `=` case, instance of the old `early_fresh_session_has_no_complete_transcript` at `ctr{hr}`, the old value substituted (§3.2) | **closes, 3 s for both cases** |
| `=` case, instances of all four invariants that index `d_State` by their `int` binder | fails at 3 s and 30 s |

The `=` case's claim needs `oget sid = (d_U, d_V, ni0, oget nr, …)` for the session at `ctr{hr}`.
Before `Send1` that session is a fresh initiator with `mess = 0`, and
`early_fresh_session_has_no_complete_transcript` says that such a session has `nr = None` and
`sid = None`. That contradicts the premises `nr{hr} <> None`, `sid{hr} <> None`.

Two things follow from the last two rows: the instance must be given **one invariant at a time**
(§3.3), and the old value must be substituted into it (§3.2).

How much this buys is not known beyond this leaf. It's the last game-invariant admit of H7 once
story 90 is in. Since stories 88–89 the split reaches many more side-invariant parts (108 parts
of H2, H6 and H7 in the run of 2026-10-21). §6 measures.

## 2. What the `=` case should do

When the closing sentence of an `=` case fails (and before story 90's retry, if that's on):

1. Crush without smt: `move: <premises> => />.`, then introduce the remaining premises with fresh
   names.
2. From the goal, find the old side invariant (`side_inv_<C> …`), the no-abort hypothesis, and an
   equation that gives the old value at the key (`t = oget m.[k]`).
3. For each game invariant of `<C>` whose binder indexes the written map, in `side_inv_<C>`
   order, try **one** sentence: instantiate it at the key, substitute the old value, `smt`.
   Stop at the first that closes the case.
4. If none closes, undo 1–3 and go on as today (story 90's retry, then the case admit of story 89).

## 3. Work to do

### 3.1 Translation: one projection lemma per game invariant

In `Comp_<C>.ec`, after `op side_inv_<C>`, for each game invariant `GameInv_<p>_of_<C>` that
`side_inv_<C>` lists:

```
lemma side_inv_<C>_<p> (s : <C>_side) :
  side_inv_<C> s => !s.`<C>_abort_flag => GameInv_<p>_of_<C> s.
proof. by rewrite /side_inv_<C> => h /h />. qed.
```

Checked: all twelve lemmas of `H7` compile with this proof (scratch copy of `Comp_H7.ec`, under a
second for the file). The name `side_inv_<C>_<p>` uses the invariant's escaped name `<p>`, as
`GameInv_<p>_of_<C>` does. No `links_<C>` lemma: it has no binder.

This is a byte change of every `Comp_<C>.ec` with game invariants. Export tests that compare
`Comp_*.ec` get the new lemmas.

### 3.2 Tactics: the instance attempt

In `close_case`, only for a case whose path ends in an `=` entry (`binder = key`), only in the
side tree (a `hoare` lemma `SideInv_<C>_<O>`, memory `{hr}`), when the closing sentence failed:

1. Send `move: <premises> => />.` (the crush without its `smt`). Read the full front goal. Its
   conclusion is a chain `P1 => … => Pn => Q`. Send `move=> hw1 … hwn.` with fresh names
   (`goals::fresh_name`).
2. Read the hypotheses and find:
   - `hinv`: a hypothesis whose head is the op `Comp_<C>.side_inv_<C>`;
   - `habort`: a hypothesis `!Comp_<C>.Game_<C>.abort_flag{hr}`;
   - `heq` (optional): a hypothesis `t = oget m.[k]`, where `m.[k]` is the written map (same
     operator path and memory as in the update the split was made on) read at the case's key
     `k`.

   Without `hinv` or `habort` there's no attempt. Go to step 4.
3. For each candidate invariant `<p>` (§3.3), send one sentence:
   ```
   have := Comp_<C>.side_inv_<C>_<p> _ hinv habort; rewrite /Comp_<C>.GameInv_<p>_of_<C> /= => /(_ <k>); (try rewrite -heq); smt(<hints>).
   ```
   Leave out `(try rewrite -heq);` when there's no `heq`. Without it the instance keeps
   `oget m.[k]` in its projections, and the measured case doesn't close. `try` because not
   every instance contains `oget m.[k]`: one that reads only `m.[k] = None` gets "nothing to
   rewrite".

   A rejected sentence leaves nothing, so the next candidate starts from the same goal. The first
   accepted sentence closes the case.
4. If no attempt closed the case, roll back to before step 1. The case goes on as today: story
   90's retry if `--smt-retry-timeout` is given, else the case admit of story 89.

Checked by hand on `SideInv_H7_Send1.ec` J1 (`<k>` = `ctr{hr}`, `heq` the premise
`(d_U{hr}, false, …, 0) = oget d_State{hr}.[ctr{hr}]`): the sentence of step 3 with
`<p>` = `early__fresh__session__has__no__complete__transcript` closes the `=` case, and with the
crush on the `<>` case both cases close in 3 s.

### 3.3 Which invariants are candidates

A game invariant of `<C>` is a candidate if its body, as Domino translated it, is
`forall (b : T), …` with **one** outermost binder `b` whose type `T` is the type of the key, and
the body reads the written map at `b` (`m.[b]`, also under `let`). Take it from the translation
(the invariant's EasyCrypt AST), not from the goal: in the goal the invariants are folded.

In `H7`, for writes to `d_State` at `ctr`, that gives four of twelve:
`sessions_above_counter_empty`, `session_key_is_defined`,
`session_freshness_matches_honesty`, `early_fresh_session_has_no_complete_transcript`.

They're tried **one at a time**, in `side_inv_<C>` order. All four at once doesn't close the
measured case, even at 30 s (§1). Each attempt costs one sentence with one `smt` at the run's
timeout.

### 3.4 Leaf budget and reports

- The leaf budget (`--leaf-budget`) is checked before each attempt, as before a case's crush
  (story 89 §3.4).
- The case's closing role is still `PartFallback { n: PART_FALLBACKS, … }`. The live page shows
  the attempt as "old `<p>` at `<k>`".
- `report.txt`: the oracle summary line counts the cases closed this way: `… ; 3 = cases closed
  by an old invariant at the key`. A closed case keeps its sentences in the proof file, so a hand
  prover sees which invariant was used.
- `scripts/proof_statistics.py` counts them per side invariant.

## 4. Rejected alternatives

- **Give smt all candidate instances at once.** It fails in the measured case at 3 s and 30 s
  (§1), and one at a time costs at most one `smt` per candidate.
- **Unfold `side_inv_<C>` in the goal and let smt instantiate.** Measured: fails at 3 s and
  30 s. The unfolded invariants are `forall`s over the whole state, and smt doesn't pick `k`.
- **Destructure the invariant by position** (`have [#] _ _ _ _ _ _ _ _ hef _ _ _ _ := hinv habort.`,
  how the measured case was first closed by hand). It depends on the conjunction's order and
  length. The projection lemma names the invariant.
- **Give smt the projection lemmas as hints** (`smt(side_inv_H7_<p>)`). smt would have to
  instantiate both the record `s` and the binder. Explicit `have := … _ hinv habort` fixes
  `s` by unification, and `/(_ <k>)` fixes the binder.
- **Instantiate in the `<>` case too, at the binder.** The `<>` cases measured so far close
  without it (story 90 §1, §6). Possible follow-up.
- **Hops.** In an `Eq_*` leaf the precondition's `side_inv_<C>` are already unfolded (`rewrite …
  in hpre`), and the relation's conjuncts are ops over two records. The same idea needs other
  lemmas and another way to find the hypothesis. Out of scope (§7 Q2).

## 5. Tests first

- [ ] Export: `Comp_<C>.ec` of a fixture composition with two game invariants has two lemmas
      `side_inv_<C>_<p>` after `op side_inv_<C>`, with the proof of §3.1.
- [ ] A composition with no game invariant gets no lemma.
- [ ] Red: a scripted side-tree session in which the `=` case's crush fails. After: `move: … =>
      />.`, `move=> hw1 … hwn.`, then the step-3 sentence for the first candidate. Scripted
      accept: the case is closed and the script keeps the three sentences.
- [ ] First candidate rejected, second accepted: the script has only the second's `have`
      sentence.
- [ ] All candidates rejected: the script is as before the attempt (crush failed → story 90
      retry or case admit). `move: … => />.` and `move=> hw…` are rolled back.
- [ ] No `side_inv_<C>` hypothesis, or no abort hypothesis: no attempt, no `have` sent.
- [ ] No `heq`: the sentence has no `try rewrite -heq`.
- [ ] Candidates: an invariant whose `int` binder indexes `d_State` is a candidate for a write to
      `d_State`; an invariant that reads only `d_First`, one with two binders, and one whose
      binder has another type are not.
- [ ] `<>` cases and hop leaves (`Eq_*`): no attempt.
- [ ] Leaf budget spent: no attempt.
- [ ] `report.txt` counts the cases closed this way.

## 6. Acceptance criteria

- [ ] All tests of §5 green; `cargo clippy` clean.
- [ ] `ec4whs`: `--side-inv H7 --force`, with `--smt-retry-timeout 30` (story 90): `SideInv_H7_Send1.ec`
      J1 closes; report the H7 admits (target 0 game-invariant admits), how many `=` cases close
      this way, attempts sent and rejected, and the change in EasyCrypt time.
- [ ] The same for `--side-inv H2` and `H6`, with and without the retry.
- [ ] All side-invariant files compile with the new `Comp_<C>.ec` lemmas; every hop that
      `require`s `Comp_<C>` still compiles (the lemmas add names, no op changes).
- [ ] `Proof_Statistics.md` in `ec4whs` updated.

## 7. Open questions

1. **Stop at the first instance that closes, or try them all and keep the cheapest?**
   Recommended: the first. The order is `side_inv_<C>`'s, and each attempt costs one `smt`.
2. **Hops.** Recommended: a later story, once §6 shows how much the side tree gains. It would need
   projection lemmas for `inv` (the relation's conjuncts) and for the unfolded `side_inv_<C>` in
   `hpre`.
3. **Also try instances at the keys of the other writes in the same leaf** (a leaf that writes
   `d_State` and `d_First`)? Recommended: no, only the case's key, to keep the attempts at one per
   candidate.
