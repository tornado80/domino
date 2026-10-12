# A table write with an unknown value is a branch, not a conditional expression

**Status:** accepted. Amends the "Tables" row of `docs/stories/easycrypt/00-overview.md` §3 (first
design session, 2026-09-16) and story 03 §3.4. Implemented by
`docs/stories/easycrypt/70-table-write-is-a-branch.md`.

A Domino table write `T[k] <- e` with `e : Maybe(V)` sets the entry to `e`: `None` removes it.
EasyCrypt's `fmap` has no operator that sets a key to an option, only `m.[k <- v]` and `rem m k`.
When `e` is not syntactically `Some(_)` or `None`, translation emitted one assignment with a
conditional expression: `T <- if e = None then rem T k else T.[k <- oget e];`. That is sound, but
it hides a real decision from the listing, from lockstep and from the leaf goals.

We decided:

1. **`easycryptify` rewrites the write into a branch**, Domino to Domino:
   `if (not (e == None)) { T[k] <- Some(Unwrap(e)) } else { T[k] <- None }`, which the writer
   translates to `if (!(e = None)) { T.[k] <- oget e; } else { T <- rem T k; }`.
2. **Where the facts of `guard_unwraps` prove `e` is `Some`, there is no branch:**
   `T[k] <- Some(Unwrap(e))`. The facts also come from the else-branch of `if (e == None)`.
3. **The branch is a plain branch.** Lockstep decides it with its normal rules. It has no marker.
4. **`remE` and `mem_rem` join the base `smt` hints**, beside `get_setE` and `mem_set`.

## Considered options

- **Keep the conditional expression and only add hints.** This is the form that EasyCrypt's own
  `simplify if` produces, because `wp` over many undecided `if`s grows exponentially. Rejected:
  the debugger never shows the two cases, and a case that the path already decides stays a
  conditional map term in every leaf goal. In our proofs lockstep decides each branch before the
  leaf, so the `wp` blow-up only applies to branches that it cannot decide.
- **A helper operator `set_opt T k e` in `Types.ec`**, with a generated, proved lemma. Closest to
  Domino's `store`, with no branch. Rejected: it hides the branch inside an operator, `smt` needs
  the new lemma, and the key case split of story 66 does not see it.
- **The rule in the writer and in the lowering separately.** Rejected: two copies of one rule (the
  bug class of story 53), and no access to the facts.
- **Always a branch, with no use of the facts.** Rejected: `NewKey` would keep a branch that the
  path already decides, and a proof would pay one `rcondt` for it.
- **A marked branch kind.** Rejected: no consumer needs to know where the branch came from.

## Consequences

- No exported file has `then rem`. In Full4WHS, `NewKey`'s write becomes the hand-written
  `d_LTK.[kid_] <- oget ltk;`, and `NewSession`'s becomes a branch.
- An undetermined, unsynchronized write splits a joint path into up to 4 cases. Several such
  writes in one oracle multiply. Full4WHS has at most one for each oracle.
- The evidence for the change is weak in admits (2 of 840 admits in the 2026-10-08 transcripts have
  `rem` in the goal). The change is for a listing that shows the decision and for simpler leaf
  terms. Story 70's report measures the effect.
- Saved joint trees from before the change no longer match the listing, and restart (ADR 0008).
