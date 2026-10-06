# EasyCrypt's answers carry only the front goal

**Status:** accepted. Implemented by `docs/stories/easycrypt/54-answers-carry-only-the-front-goal.md`.
Changes the protocol of story 25 from `domino-json/1` to `domino-json/2`.

A tactics run sends EasyCrypt one sentence at a time and reads one JSON answer per sentence. In
version 1, each answer holds **every** open goal, and every node of every formula and expression
tree carries its own `pp` string. A node's `pp` repeats the text of all its subnodes, so one goal
costs about O(size × depth) to print.

The Full4WHS runs showed that this answer, not smt, is where the time goes. At a leaf with 16–17
open goals one answer is 25–28 MB. Tactics that do almost nothing (`split.`, `admit.`, `undo`)
take 10–40 s. The final `Eq_H4_H5.ec` compiles in batch mode in 515 s; the same sentences took
about 4,366 s over JSON.

Domino reads very little of the answer. It reads the first open goal in full, the number of open
goals, and whether the second and third goals are program judgements. It reads `pp` only on
statements, conditions, lvalues and the root of the conclusion.

We decided that each answer carries **the front goal in full, and the kind of every open goal**
(`program` or `formula`). The number of open goals is the length of the kind list. `pp` stays
only where Domino reads it. EasyCrypt does the work for the goal that the next tactic works on,
and nothing more.

## Considered options

- **The first K goals in full.** Rejected: Domino reads only one goal in full, so every goal after
  the first costs time for nothing.
- **The count, and a command to fetch any goal on demand.** Rejected: the driver's shape checks
  need the kinds of the next goals at most steps, so on-demand fetches add a round trip at most
  steps and a command to the protocol.
- **The front goal and the count only.** Rejected: the shape checks before `if.` and before a
  two-sided step cannot be made without the kinds.
- **All goals, with `pp` cut.** Rejected: it removes the O(size × depth) cost, but a leaf answer
  still carries 16 full goals.

Other provers do the same. EasyCrypt's own `llm` mode prints only the current goal unless the user
asks for `GOALS ALL`. Isabelle limits the goals it prints with `goals_limit` (often set to 1 by
tools). Lean bounds its pretty-printer with `pp.maxSteps` and `pp.deepTerms`. SerAPI has an open
item to limit the goals it returns.

## Consequences

- An EasyCrypt binary that speaks only `domino-json/1` no longer works with Domino. The error
  names both versions and `DOMINO_EASYCRYPT`.
- Domino cannot show the other open goals on the progress page or in the transcript. If a later
  story needs them, it adds a command or a pragma that asks for them, and pays for it only then.
- `--ec-transcript full` writes the answer verbatim, as before. The answer is now small, so the
  full transcript is affordable.
- A tool that reads `pp` on a formula subnode must print the subnode itself.
