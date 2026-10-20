# Side invariants are hoare lemmas of the composition, joined with `conseq`

**Status:** accepted; partly superseded by ADR 0016 (package invariants and start lemmas) and by ADR 0019
(point 1: the lemmas now take one binder for each game constant that a game invariant can read). Supersedes ADR 0010. Implemented by
`docs/stories/easycrypt/69-side-invariant-lemmas.md` and
`docs/stories/symbolic-execution/25-one-sided-execution.md`.

ADR 0010 put the package and game invariants inside `inv`, under the `!abort` guard, and rejected
separate `hoare` lemmas "for now". It said to come back when one game is used in many equivalences,
or when the one-sided conjuncts make leaf goals too large. Both now hold, and ADR 0013 already makes
each oracle a lemma of its own, so a new lemma kind costs much less.

We decided:

1. **A side-invariant lemma for each oracle of each composition**, `SideInv_<C>_<O>.ec`:
   `hoare[<C>.<O> : side_inv_<C> ==> side_inv_<C>]`, where `side_inv_<C>` is `!abort =>` all of the
   composition's package invariants and its game invariant. `SideInv_<C>.ec` joins the oracles. The
   lemmas say nothing about the composition's parameters, so they hold for every value. In the
   translation the parameters are module globals that each equivalence fixes with `params_inv`.
2. **`inv` keeps only** `params_inv`, the abort equality and `!abort => StateRelation_invariant`.
3. **The oracle lemma assumes both sides' side invariants and proves only `={res} /\ inv`.** Only
   the equivalence's file joins them: `by conseq Eq_X_<O> SideInv_<L>_<O> SideInv_<R>_<O>.` (tested
   on the fork). So an oracle lemma does not need the `SideInv_` files, and a whole-theorem run can
   prove compositions and equivalences in parallel.
4. **A side-invariant job proves one composition** (`prove --side-inv <C>`). It follows the side tree
   of one-sided execution, the way a proof job follows the joint tree. A proof job never proves
   side invariants. `prove --proofstep <eq>` stops with a warning if a `SideInv_` file of its
   compositions is missing.

## Considered options

- **Lemmas for each equivalence.** Rejected: a composition used in several equivalences would be
  proved several times.
- **Lemmas for each game instance.** Rejected: package and game invariants hold for the
  composition with any parameters (`CONTEXT.md`), so a game instance is the wrong owner.
- **Game invariants only.** Rejected: two mechanisms for one kind of claim.
- **`conseq` inside each oracle lemma.** Rejected: each oracle lemma would then need the
  `SideInv_` files, so a whole-theorem run would have to finish a composition before it starts its
  equivalences.
- **A blind one-sided walk from EasyCrypt's program shape.** Rejected by the owner in favour of
  one-sided execution, which gives Domino verdicts for admits and decides branches in advance.

## Consequences

- Leaf goals of an oracle lemma no longer contain the one-sided invariants, so they are smaller.
- The one-sided invariant operators are defined one time for each composition, so that every file
  that uses them refers to the same operator.
- A project whose side invariant does not hold for some parameter values gets admits in
  `SideInv_<C>_<O>.ec`, even if the equivalences only use values where it holds.
