# Story 105 — Implementation report: the reduction walk recognizes the shape of a program head

Prover story. Branch `amir/easycrypt-export`, ADR 0024 (decision 2). Implementation in the commit
"Story 105: the reduction walk recognizes the shape of a program head" (1a4d6e51), review fixes in
876eff45.

## What was built

**The recognizers** (`src/easycrypt/tactics/reduction_walk.rs`, new, pure functions, `pub(crate)`):

- `classify(left: &[Instr], right: &[Instr], assumption: &str) -> Head`: the 12 rules of §3 in
  order. `assumption` is the theory, e.g. `Comp_MAC`.
- `Head { Leaf, AssumptionGuard, TailBranch, ExitGuards, Branches, Samplings { x, y },
  Mismatch(Mismatch) }`; `Samplings` carries the two lvalues' `pp`.
- `Mismatch { LeftOnlyIf, RightOnlyIf, OneSidedSampling, Loop, Heads { left, right } }` with
  `claim()`: `left-only-if`, `right-only-if`, `one-sided-sampling`, `loop`, `heads <l>/<r>`. An empty
  program has the kind `none`.
- `is_assumption_guard(instr, A)`, `is_tail_branch(instr, A)`, `is_exit_guard(instr)`, read from
  `cond.pp` after `<:…>` annotations and outer parentheses are dropped.

The module carries `#![allow(dead_code)]` until story 106 calls it.

## Decisions and deviations

- **The fixtures are hand-made, not captured.** The story asks for `Want::Full` answers of a live
  EasyCrypt on a reduced copy of `Red_H7_1_H7_0_Send2`. The exported Full4WHS files lie outside the
  worktree (access was denied) and big projects are not exported here. The six goals under
  `testdata/easycrypt/reduction-walk-goals/` are in the `domino-json/3` shape and use the statement
  texts quoted in §2; the README says so and asks for replacement by captured answers. Risk: spacing
  or `Top.` forms EasyCrypt prints that §2 does not quote.
- `<A>.Game_<C>.abort_flag` is also accepted with `Top.` in front, and `!(…)` with parentheses.
- An exit guard may contain parentheses as well as `!`, `=`, `<>`; a bare `abort_flag` counts as an
  abort flag. A `<:` annotation that never closes is kept as text, so the condition is not an exit
  guard (fail closed).
- Tail branch: the right-hand side must be exactly `None` after annotations are dropped.

## Tests run

| Command | Result |
|---|---|
| `cargo test -p sspverif --lib reduction_walk -- --test-threads=1` | 15 passed |
| `cargo clippy -j 2 --workspace --all-targets` | clean (without `-j 2` clippy-driver crashed with `WouldBlock`, a resource limit of the machine) |
| `.sdlc-workspace/crap-coverage.sh reduction_walk` | coverage ingested |
| `sdlc crap gate . --since-ref dab42450 --threshold 15` | not run: `bwrap: loopback: Failed RTM_NEWADDR` |

## Written, not run

None. Capturing the live goals of `Red_H7_1_H7_0_Send2` is left open (see above).

## Epic §5 "Done when"

- [ ] Stories 104–107 done with reports — 104 and 105 done.
- [ ] `prove` on `reduction-consts` and `reduction-two-calls` leaves no admit — story 106.
- [ ] Hop 12 of Full4WHS — story 107.
- [ ] `docs/proving-algorithm.md` — §10 and the new reasons with 106.
