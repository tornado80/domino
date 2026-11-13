# Story 105 — The reduction walk recognizes the shape of a program head

**Epic:** EasyCrypt export: the reduction walk — `docs/stories/easycrypt/epic-the-reduction-walk.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** —
**Blocks:** 106.
**ADR:** `docs/adr/0024-a-reductions-oracle-lemma-is-proved-by-a-strict-reduction-walk.md`
(decision 2).
**Decisions:** owner's grilling session of 2026-11-12/13, Questions 3, 4, 5, 7 and 10.

A **prover** story: a new file `src/easycrypt/tactics/reduction_walk.rs` with pure functions only,
saved EasyCrypt goals under `testdata/easycrypt/reduction-walk-goals/`, and unit tests. No EasyCrypt
at test time. Test-first.

---

## 1. Why this story exists

The reduction walk (story 106) sends one step for each program head, chosen from the head's shape.
The shape rules are the part that can be wrong in silence, so they are pure functions with their own
tests, on goals that EasyCrypt really printed for Full4WHS.

## 2. The facts this story uses

- `json.rs`: a `Side` has `stmt: Vec<Instr>`. An `Instr` has `kind` (`asgn`, `rnd`, `call`, `if`,
  `while`, …), `cond: Option<Node>` for an `if`, `then`/`else` blocks, and `lvalue` with `pp`.
  **A condition is a `Node { kind, pp }`: only EasyCrypt's printed text, not a structured formula.**
  The recognizers therefore read `cond.pp`.
- What EasyCrypt prints in `Red_H7_1_H7_0_Send2` after `proc; inline *.` (2026-11-12):
  - assumption guard (right only): `if (!Comp_MAC.Game_MAC.abort_flag) { … }`;
  - tail branch of the assumption game (right only):
    `if (ec_result4 = None<:unit>) { Comp_MAC.Game_MAC.abort_flag <- true; }`;
  - exit guards (both sides): `if (!ec_done0)`, `if (ec_r10 <> None<:bits_n>)`,
    `if (ec_result = None<:bits_n * bits_n>) { <router>.abort_flag <- true }`, and the router guards
    `if (!Comp_H7.Game_H7.abort_flag)` (left) and `if (!Red_H7_1_H7_0.abort_flag)` (right);
  - real decisions (both sides): `if (hon)`, `if (Comp_….MAC.d_Keys.[handle1] = None<:bits_n>)`,
    `if (key0 <> None<:bits_n>)`. The last one has the `<> None` form, but `key0` is a package
    variable, not a translation local.
- Translation names its own locals with the prefix `ec_` (done flags, call results, results). A
  package variable never has it.
- `driver.rs:464` `exit_decisions`: the order of `rcondt`/`rcondf` for an exit `if`.

## 3. What to build

In `reduction_walk.rs`, with the assumption theory `<A>` (for example `Comp_MAC`) as an input:

1. `is_assumption_guard(instr, A)`: an `if` whose condition is `!<A>.Game_<C>.abort_flag` for some
   `<C>`.
2. `is_tail_branch(instr, A)`: an `if` whose condition is `<x> = None…` and whose *then* block is
   exactly one assignment `<A>.Game_<C>.abort_flag <- true`, with an empty *else* block.
3. `is_exit_guard(instr)`: an `if` whose condition reads no name other than translation locals
   (`ec_…`), abort flags (`….abort_flag`), `None`, `true`, `false` and the operators `!`, `=`, `<>`.
   Type annotations `<:…>` are dropped before the names are read.
4. `classify(left, right, A) -> Head`: the shape of the two first statements, with the rules in this
   order (the first rule that matches wins):

   | Order | Left head | Right head | `Head` |
   |---|---|---|---|
   | 1 | none | none | `Leaf` |
   | 2 | any | assumption guard | `AssumptionGuard` |
   | 3 | any | tail branch of `<A>` | `TailBranch` |
   | 4 | `while` | any | `Mismatch(Loop)` |
   | 5 | any | `while` | `Mismatch(Loop)` |
   | 6 | `if`, exit guard | `if`, exit guard | `ExitGuards` |
   | 7 | `if` | `if` | `Branches` |
   | 8 | `rnd` x | `rnd` y | `Samplings { x, y }` |
   | 9 | `if` | not `if` | `Mismatch(LeftOnlyIf)` |
   | 10 | not `if` | `if` | `Mismatch(RightOnlyIf)` |
   | 11 | `rnd` | not `rnd` (or the other way) | `Mismatch(OneSidedSampling)` |
   | 12 | anything else | | `Mismatch(Heads { left, right })` with the two kinds |

   Assignments are not heads: the walk runs `sp` before it classifies, and `sp` removes them. A
   head that is still an assignment after `sp` is rule 12.
5. `Mismatch` has a claim text for the admit: `left-only-if`, `right-only-if`, `one-sided-sampling`,
   `loop`, `heads <left kind>/<right kind>`.

Nothing outside `reduction_walk.rs` reads `Head` or the recognizers.

## 4. Tests first

The goals come from a live EasyCrypt on the reduced copy of `Red_H7_1_H7_0_Send2` (the method of the
memory note "EC leaf experiments": copy the files, admit the earlier closers, and stop with `-upto`).
Save the JSON answers of `Want::Full` under `testdata/easycrypt/reduction-walk-goals/`, with a README
that says from which line and which code they come.

- [ ] Root (after `proc; inline *.`): rule 6, the router guards are exit guards on both sides.
- [ ] The nonce (line 53 of the 2026-11-11 file): rule 8 with `x = y = ni1`.
- [ ] After `if (hon)` (*then* arm): rule 2 on the guard around `Init`.
- [ ] After `rcondt{2}` and the `Init` body: rule 3 on `if (ec_result4 = None<:unit>)`.
- [ ] Inside `Mac`: rule 7 on `if (key0 <> None<:bits_n>)` (a real decision, not rule 6).
- [ ] `if (Comp_H7.Cloned_Pkg_PRF.PRF.d_H.[kid1] <> None<:bool>)`: not an exit guard.
- [ ] Hand-made variants of a saved goal (one statement removed or added in the JSON): rules 4, 9,
      10, 11 and 12, each with its claim text.
- [ ] `is_tail_branch` is false for the reduction router's own tail branch (its *then* block sets
      `Red_<L>_<R>.abort_flag`, not `<A>.Game_<C>.abort_flag`).

## 5. Acceptance criteria

- [ ] All tests of §4 green, with filtered test runs only. `cargo clippy` clean.
- [ ] Complexity: every function within budget (`.sdlc-workspace/crap-coverage.sh <filter>`).

## 6. Rejected alternatives

- **Recognize `rcondt{2}` by trial** (Question 3): a wrong `if` that happens to be true is accepted.
- **An exit guard is any `<x> <> None`**: `key0 <> None` is a real decision of the MAC package.
- **A structured condition from EasyCrypt** (`cond` as a `Form`): it needs a change to EasyCrypt's
  JSON. The printed text is enough for these shapes.
- **Replay full goal sequences in `FakeEasyCrypt`** (Question 10): each change to EasyCrypt or to
  translation breaks them all.
