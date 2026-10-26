# One-sided invariant checks name their owner, not a theorem

**Status:** accepted. Implemented by `docs/stories/symbolic-execution/30-prove-game-invariants-of-a-composition.md`,
`31-claim-selects-an-invariant-by-name.md`, `32-debug-a-composition-on-the-domino-listing.md` and
`33-debug-a-package-on-the-domino-listing.md`. Grilling of 2026-10-21/22, Questions 1, 2, 3 and 10.

`domino prove --package P` proves a package invariant on its own, with free parameters and open
calls (story 75 of the EasyCrypt epic). A game invariant has no such check. `domino prove` proves it
only inside an equivalence, for the two game instances, with their constants bound. That is a weaker
claim than the side-invariant lemma `SideInv_<C>_<O>` needs (ADR 0014: "for every value of the
composition's parameters"). `domino debug` has no one-sided run at all; only `domino easycrypt
debug` has one, and it needs `--theorem`.

We decided:

1. **`--game C` names a composition, never a game instance.** The composition declares the game
   invariant, as the package declares a package invariant. The check is for every value of C's
   parameters, the same claim that `SideInv_C_<O>` makes.
2. **No theorem.** `domino prove --game C` and `domino debug --game C` build the free composition
   from C alone, as `--package P` builds its one-game theorem. They refuse `--theorem` and
   `--gamehop`. The theorem's constants only give names to free parameters and its assumptions are
   not SMT facts, so a theorem would change nothing in the check.
3. **`--game C` checks only C's game invariants.** It assumes the package invariants of C's
   instances, as the side tree does since story 77 of the EasyCrypt epic (ADR 0016). The package
   invariants are proved with `--package P`. The report names the package invariants that it
   assumes.
4. **Plain `domino prove` does not change.** It still proves every package invariant that the
   selected theorems need, and the game invariants only inside the equivalences. `--game C` is an
   opt-in check, for the stronger claim that the EasyCrypt export needs.

## Considered options

- **The game instance name.** It gives a second, weaker meaning to the same claim, and it needs the
  theorem, because instance names are unique only in one theorem. ADR 0014 rejected the game
  instance as the owner.
- **`--theorem T` required, as `domino easycrypt … --game C` needs `--theorem`.** The same shape
  on both sides, but the theorem changes nothing in the SMT check. The EasyCrypt commands need the
  theorem only for their export tree.
- **`--game C` also proves the package invariants of C's packages.** One command answers "is C safe
  on its own", but a package in many compositions is proved many times (ADR 0016 rejected this), and
  `--game` must then know the package-invariant driver.
- **Plain `prove` also runs `--game` for each composition it uses.** It finds the problem early, but
  it changes the meaning and the exit code of the most used command: a project whose game invariant
  holds only for the constants it uses would fail, but its theorem is correct.
- **Plain `prove` runs `--game` and only warns.** A section that cannot fail the run is a status that
  nobody acts on.

## Consequences

- `domino prove --game C` can say "verified" while a package invariant of C is false. The report says
  which package invariants it assumes.
- Plain `prove` and `easycrypt prove --game C` can still disagree: an equivalence can verify for
  its constants while `SideInv_C` gets admits. `domino prove --game C` is the way to see this before
  EasyCrypt runs.
- The EasyCrypt commands kept their own names for these two flags. **Amended by story
  EC 95:** all commands now use `--package P`, `--game C` and `--theorem`. `easycrypt prove --game C`
  proves the game invariants of C and takes its package invariants from the lemmas of
  `--package`, as `prove --game C` assumes them.
