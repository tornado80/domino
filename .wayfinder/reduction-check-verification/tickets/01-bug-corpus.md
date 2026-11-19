---
title: Bug corpus of unsound reductions
type: wayfinder:task
status: closed
assignee: Amir Rajabi
blocked_by: []
---

## Question

Which concrete reductions does the current (or a past) check accept, although they are not
valid? Collect each one as a small SSP project (construction games, assumption games, theorem
file) with a short reason why it is unsound. Sources: the fix in PR #442 (exports that cross into
the assumption), the git history of `src/parser/reduction.rs`, cases that the user knows, and
suspects in the current code. Suspects include: `zip` over the unmapped package instances (lists of
different length), no check that the reduction parts of left and right are equal, recursion over
edges without a cycle guard, and the hybrid path. For each suspect, record "confirmed unsound",
"rejected by the check", or "not a bug". This ticket is part AFK, part HITL: the agent collects
the cases, and the user adds the cases that they know.

## Resolution

Done. The corpus is in [assets/bug-corpus](../assets/bug-corpus/README.md): 17 items with verdicts,
defect classes and a list of obligations for the soundness theorem.

Facts for later tickets:

- The current check (commit `7bf2632b`) **accepts 7 unsound hops**: the 5 cases of PR #2 of
  `grittygrease/domino` (context oracle, context instance sharing, mapped wiring, exports, an import
  wired twice), the user's `Soundness.ssp` case (mapped destination oracle), and one probe (a cross
  edge that enters a different assumption instance on the right).
- It **panics** on 3 items (`reduction.rs:342`, `:893`, `:928`). A panic is a rejection, but it is
  not a diagnostic.
- The PR #442 case is rejected correctly. All 6 controls are accepted.
- Defect classes, which are the obligations of the theorem: W1 (well-formed composition), M1, M2
  (mapped part), R1 (one context, bijection), X1, X2 (context and cross edges), E1–E3 (exports). See the
  README.
- Not bugs: the `zip` over unmapped assumption instances (dead code), the `debug_assert!` on cross edge
  signatures.
- Not examined: the hybrid path, cycles in compositions, and the fixed branch of PR #2 against this
  corpus (the external code was not run).
- The corpus is not in `test-projects/`, because CI runs every project there. The user's untracked
  `test-projects/test-new-reduction-soundness-test-project` makes CI fail until it moves.
