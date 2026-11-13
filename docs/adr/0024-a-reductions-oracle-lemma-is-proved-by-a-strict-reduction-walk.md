# A reduction's oracle lemma is proved by a strict reduction walk

**Status:** accepted. Supersedes ADR 0023 decision 5 ("with the blind walk"). The rest of ADR 0023
stays. Implemented by `docs/stories/easycrypt/epic-the-reduction-walk.md` (stories 104 to 107).
Grilling of 2026-11-12/13, Questions 1 to 11.

ADR 0023 proves a reduction's oracle lemmas with the blind walk (`prove_blind`). The blind walk
expects no shape: at each program head it tries `rcondt`/`rcondf` on each side, `if`, `if{1}`,
`if{2}` and `seq`, and it keeps the first trial that EasyCrypt accepts. On hop 12 of Full4WHS
(`Red_H7_1_H7_0_Send2`), this took 26 minutes, with 468 undone attempts, and it admitted a correct
step: the `seq` at `key <$ dbits_n` failed only because its one closer, `auto => /#`, ran out of
time, and `auto => />` closes it. A trial that EasyCrypt accepts can also be the wrong step, and the
blind walk then finds the error far from its cause.

But the two sides of a reduction's oracle lemma have a known shape. They run the same code. The
right side only adds, around each call that the reduction router forwards to the assumption game,
the assumption game's **assumption guard** `if (!<A>.Game_<A>.abort_flag)` and its **tail branch**
`if (r = None) { <A>.Game_<A>.abort_flag <- true }`, plus copies of arguments and results. The
invariant `game_abort = red_abort /\ (assm_abort => red_abort) /\ (equal states)` makes the guard
true.

We decided:

1. **A new reduction walk** proves the oracle lemmas of a reduction hop. It is a module of its own,
   with one entry point, that the driver calls for `Judgement::Reduction` only. `prove_blind` stays,
   unchanged, for its other callers (the hoare prelude, and a joint-tree step that does not apply).
2. **The walk is strict.** It reads the shape of each program head from EasyCrypt's goal JSON and
   sends the one step that the shape calls for:
   - an assumption guard on the right: `rcondt{2}`;
   - a tail branch of the assumption game on the right: `rcondf{2}`, else `rcondt{2}`;
   - a pair of exit guards: decide each side with `rcondt`/`rcondf`, else `if.`;
   - any other pair of `if`s: `if.`;
   - a pair of samplings: `seq 1 1 : (#pre /\ x{1} = y{2})`;
   - two empty programs: the leaf (quick close, then the leaf procedure).
   Any other shape is a **mismatch**. The walk admits that goal with the reason
   `reduction-mismatch`, does not search, and continues with the other open goals.
3. **The shape decides the step, and EasyCrypt decides the side goal.** The walk sends the
   structural tactic alone and closes its side goal with `auto => />` and then the side-goal
   fallback sequence. A side goal or a leaf part that does not close is admitted alone with the
   reason `reduction-ec-failed`, and the walk continues under it.
4. **Domino has no view of a reduction.** Both new reasons use `DominoView::NotApplicable`. Admit ids
   are the path of `if.` arms from the root (`R`, `R.t`, `R.t.e`).
5. **A sampled variable that `#pre` mentions** (a local, or a global whose module's `glob` is in
   `#pre`) gets a `seq-post` admit, with no `seq`. The same check runs in the equivalence path
   (`sampling()`). EasyCrypt renames an inlined local only on a name clash, so a variable that is
   sampled again keeps its name.

## Considered options

- **Keep the blind walk** (ADR 0023). Slow, and it can accept a wrong step without a warning.
- **A strict mode flag on `prove_blind`.** The callers must know the walk's internal mode, and the
  rules of two algorithms mix in one function.
- **Full lockstep execution of the reduction.** Rejected again for the reasons of ADR 0023.
- **`rcondt{2}` by trial** when the heads do not match, instead of recognizing the assumption
  guard. A wrong `if` that happens to be true is then accepted without a warning.
- **`if{2}` on the tail branch.** It doubles the subtrees, and an arm that cannot occur fails only
  at its leaf.
- **Admit the whole oracle, or the whole job, at a mismatch.** One mismatch per run, and the proved
  arms are lost; the oracles are independent (ADR 0013).
- **One sentence per step with a short closer list.** A timeout on a correct step then loses the
  whole subtree, and the closers are kept in two places.
- **Always `if.`**, or **cheap trial decisions for every pair of `if`s.** The first walks arms that
  cannot occur; the second costs four failed tries at each real decision.
- **Reuse `program-mismatch` and `domino-verified-ec-failed`.** The second says that Domino verified
  the claim, which is false for a reduction. **One reason `reduction` for all admits** hides the
  difference between "the code has the wrong shape" and "the proof needs work".
- **Rewrite the `seq` postcondition** when the sampled variable is in `#pre`. A large feature for a
  case that the current translation avoids; it can come later.
- **Ask EasyCrypt for different names.** Not possible: the names are correct for the code EasyCrypt
  has. A name that looked wrong (`ni1` against `ni2`, 2026-11-12) came from a proof file copied into
  a different translation.

## Consequences

- The report of a reduction says `reduction walk`, with the admits counted for each reason.
- `BLIND_BUDGET` goes away. The reduction walk needs no budget: each step removes at least one
  statement, and a loop is a mismatch.
- `close_side_goal` and the leaf procedure choose `reduction-ec-failed` by themselves when the
  judgement is a reduction. No caller passes a reason.
