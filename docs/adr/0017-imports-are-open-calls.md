# A package's imports are open calls, one unknown outcome for each call site

**Status:** accepted. Replaces the virtual package of branch `amir/check-package-invariants-once`
(PR 426). Implemented by `docs/stories/easycrypt/75-open-calls-in-the-solver-check.md`,
`docs/stories/symbolic-execution/29-the-package-tree.md` and
`docs/stories/easycrypt/76-package-lemmas-and-the-package-invariant-job.md`. Grilling of
2026-10-12/20, Questions 5 and 5b.

To prove a package invariant one time for each package, the package needs an environment that
covers everything a real environment can do. PR 426 builds a *virtual game*: the package next to a
virtual package `P$Env` with one `Bits(*)` state and one uninterpreted function for each import,
which returns `Maybe((state, value))`. That model is general, but the listing then has code that no
EasyCrypt lemma has, and the solver gets one more state and one function for each import.

We decided:

1. **An import call is an open call.** Its outcome is unknown: `None` (the import aborted) or
   `Some v` with any `v`. It cannot touch the calling package's state.
2. **Each call site has its own outcome, independent of every other call site**, so two calls of the
   same import may return different values. After loop unrolling every call site is different, so
   one call site runs at most once in one oracle call.
3. **The solver check** (`domino prove`, `domino prove --package`) encodes each oracle of the package
   as an SMT function with one more argument, a **call-result record**: a datatype, like the game
   state, with one field for each import call site, of that call's `Maybe` return type. Each call
   site reads its own field and nothing else. The claim is proved for every value of the record.
4. **The debugger** walks the package oracle on the EasyCrypt listing and gives each import call a
   fresh value of its option type (the package tree). **EasyCrypt** quantifies over the import
   module and uses `call (_: true)` (ADR 0016). All three see the same freedom.

## Considered options

- **The virtual package of PR 426.** As general, but `P$Env`'s body (the uninterpreted call, the
  `Bits(*)` state, the unwrap) is in the listing and not in the EasyCrypt lemma, so the package tree
  and the EasyCrypt goals would not align.
- **One uninterpreted function for each import, without a state.** Two calls with the same
  arguments would have to return the same value, which a stateful environment does not guarantee.
  That is not sound.
- **A separate argument for each call site.** As general as the record, but an oracle with many
  call sites gets a long argument list. The record keeps one argument, like the game state.

## Consequences

- `src/package_invariant/virtualgame.rs` of PR 426 is replaced. PR 426's CLI, its choice of which
  packages a theorem needs, its error types and its verify driver stay.
- A package's invariant cannot depend on what an import returns across calls. That is correct: the
  invariant is about the package's own state.
- A loop that `loopunroll` cannot unroll and that calls an import cannot be checked this way. Today
  such loops are already rejected by the debugger.
