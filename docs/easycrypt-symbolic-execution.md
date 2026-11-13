# EasyCrypt debugging and symbolic execution

This document describes how `domino easycrypt debug` executes an oracle symbolically, how it
decides each branch and sampling, and how `domino easycrypt prove` turns those decisions into
tactics. It describes the code in `src/debug/` and `src/writers/easycrypt/lower.rs`.
[proving-algorithm.md](proving-algorithm.md) describes the proof walk itself: fallbacks, leaves
and admits. This document covers what comes before that walk and how the walk uses it.

## 0. Synchronized `if` or `rcondt`/`rcondf`: which comes first

**Symbolic execution checks first whether a branch is determined (`rcondt`/`rcondf`).** It
tries a synchronized `if` only when neither side's branch is determined.

The order is fixed in `Engine::decide_branch` (`src/debug/lockstep.rs`). At a joint node where
at least one side stands at a branch, these rules are tried in order:

| # | Rule | Solver queries (under `A ∧ pc`) | Node kind | Tactic |
|---|---|---|---|---|
| 1 | Left branch determined | `c_L` and `¬c_L`, one of them `unsat` | `determined` | `rcondt{1} ^if` or `rcondf{1} ^if` |
| 1 | Right branch determined | `c_R` and `¬c_R`, one of them `unsat` | `determined` | `rcondt{2} ^if` or `rcondf{2} ^if` |
| 2 | Both at branches, conditions equivalent | `c_L ≠ c_R` is `unsat` | `synchronized` | `if.` |
| 3 | Anything else | none to decide; each child's feasibility is checked | `split` | `if{1}.` then `if{2}.`, or `if{s}.` |

Rule 1 runs on the left side, then the right side. The first side found determined moves alone,
and the node ends there. If both of a side's queries are `unsat`, the node is `unreachable`.

Some consequences of this order:

- **Equivalent and determined conditions give `rcondt`, not `if`.** Suppose both sides stand at
  `if (x = None)` and the path condition already implies `x = None`. Rule 1 matches on the left,
  giving `determined` (`rcondt{1}`). At the next node the right side is still at its `if`, and
  rule 1 matches again (`rcondt{2}`). The proof gets two `rcondt`s and no `if.`
- **One determined node moves only one side.** When both sides are determined, the joint tree
  has two `determined` nodes in a row, left first.
- **`synchronized` needs both conditions undetermined.** Each condition can go either way, but
  the two always go the same way.
- **Branches come before samplings.** If one side is at a branch and the other at a sampling,
  the branch is decided first (rule 1 or a one-sided `split`). Samplings are decided only when
  neither side is at a branch.
- **A done-flag guard is always determined.** The EasyCrypt listing gives the guard
  `if (!ec_done)` the literal condition `true`, so `¬true` is `unsat` and the guard is
  `rcondt`.

EasyCrypt does not take part in this choice. The solver decides the node kind during symbolic
execution, and the prover sends the tactic for that kind. EasyCrypt tries `rcondt` and
`rcondf` in a fixed order only in two places: the blind walk (section 9.3), when the tree's step
did not apply, and the exit-path stage of a leaf (section 9.4).

## 1. The pipeline

```text
Domino project
  │  EasyCryptTransform (…, tableinitialize, easycryptify)
  ▼
easycryptified Domino oracles ──► Comp_*.ec, Eq_*.ec …              (domino easycrypt export)
  │  inline_oracle_ec (src/writers/easycrypt/lower.rs)
  ▼
InlinedOracle: the EasyCrypt listing + the IR the executor walks
  │  run_lockstep (src/debug/lockstep.rs), one SideExec per side, cvc5 incremental
  ▼
joint tree (LockstepOutcome): nodes, J<n> joint paths, S<n> stuck points
  │                                    │
  ▼                                    ▼
domino easycrypt debug:           domino easycrypt prove:
page, trace.json, models,         walk the tree beside a live EasyCrypt session,
failing queries                   one tactic per node (src/easycrypt/tactics/driver.rs)
```

`domino easycrypt debug` stops after lockstep execution and writes its artifacts. `domino
easycrypt prove` runs the same engine, saves the tree under `session/`, and walks it.

## 2. The EasyCrypt listing

### 2.1 Single-exit shape

EasyCrypt procedures have one exit. `easycryptify` (`src/transforms/easycryptify.rs`) rewrites
each oracle body into that shape. After it runs, each body has:

- no `abort`, and exactly one `return`, which is the last statement;
- that `return` returns the local `ec_result`;
- the return type `Maybe(T)` instead of `T`, where `None` means abort.

The continuation after a statement that may exit is **moved** into the branch that survives,
not copied into both branches as `treeify` does. When two live paths join, the code after the
join is wrapped in an `if (!ec_done) { … }` guard.

### 2.2 Lowering to the IR

`inline_oracle_ec` takes the easycryptified game instance and builds two things in one pass:

- the **listing**: the router procedure with every package procedure inlined in place, as
  EasyCrypt text, one statement per line;
- the **IR** (`InlinedOracle`): the statements the executor walks, built from the Domino
  statements and not parsed back from EasyCrypt.

Each IR node has a **label**, which is its line number in the listing. Joint-tree nodes refer
to listing lines through these labels.

The control-flow variables of the single-exit shape do not become places in the IR:

| EasyCrypt code | IR |
|---|---|
| `ec_result <- Some e` | `Return e` (entry frame) or the callee's `Some e` |
| `ec_done <- true` (where a guard reads it) | `Abort` |
| `if (!ec_done) { … }` | Branch with exit guard `DoneFlag`, condition `true`, no else |
| `if (!(ec_rN = None)) { … } else { … }` | Branch with exit guard `CallResult` (a real condition) |
| `x <- oget e` under its `None` guard | Plain `Assign` (the guard is the branch) |
| Frame falls off its end (`ec_result` still `None`) | `Abort` |
| Router prelude `if (!abort_flag)` and tail `if (ec_result = None)` | Not in the IR |

Because `oget` cannot fail in EasyCrypt, every branch in the EasyCrypt IR is a plain `if` with
`then`/`else` decisions. Domino's `assert-*` and `unwrap-*` decisions appear only on the Domino
listing (`domino debug --lockstep`).

The router's prelude and tail stay out of the IR on purpose: Domino has no abort flag to decide
them with. The prover handles them itself (the prelude in
[proving-algorithm.md §4](proving-algorithm.md), the tail in section 9.4 below).

### 2.3 The executor runs against the Domino game

The oracle is lowered from the EasyCrypt pipeline but **executed against the Domino
(`DebugTransform`) game instances**. State places, sample ids and entry returns therefore match
what the claims are written over, so verdicts on the EasyCrypt listing can be compared with
`domino prove`'s.

## 3. Symbolic execution of one side

`SideExec` (`src/debug/exec.rs`) walks the IR of one side with no solver involved.

- **Straight-line code is consumed eagerly.** Assignments, call entry and exit, and callee
  returns run without stopping. A side stops only at a **decision point**: a branch, a
  sampling, or a terminal.
- **Dynamic single assignment.** Each assignment declares a fresh constant
  `v!<side>!<n>!<name>` and asserts `(= v!… <rhs>)`. A local is renamed per frame
  (`<inst>#<frame>::<name>`). Package state is keyed `(inst, field)` and is shared across
  frames, which gives the same semantics for re-entrant calls as the SMT writer.
- **Calls stay nested.** A callee `return` binds the call's result and resumes the caller
  after the `Call` node. An `abort` at any depth ends the whole oracle.
- **Samplings** bind `(__sample-rand-<gi>-<ty> <pos> <ctr>)` and increment the counter, as the
  prover's encoding does.
- **Terminals** fold the package states and the advanced randomness counters into the new game
  state and set the oracle's return slot (`return_constraint`).

Each path's SMT is a **plain conjunction**: declarations, then definitions and path conditions
in order, then the return constraint. Adding a branch only adds a conjunct. So if a prefix is
`unsat`, every extension of it is `unsat` too. This is why it is sound to prune on `unsat`. It
is also why **only `unsat` prunes**: `unknown` and timeouts are always explored, never treated
as verified.

## 4. The base frame `A`

Before the root node, the solver holds the assumptions `A` at level 0 (`shared_base_frame` in
`src/debug/lockstep_run.rs`):

- declarations and the game definitions of both sides;
- the invariants on the old states: main, per game and per package;
- the randomness-mapping condition and `emit_auto_randomness`;
- the oracle arguments, the same constants on both sides.

On the EasyCrypt listing **no project lemma is assumed**, because EasyCrypt does not have them.
Each claim's own dependencies are asserted only at the terminal pair (section 7).

## 5. Lockstep execution: the joint tree

`run_lockstep` keeps one executor per side and walks the **joint tree** depth first. Each joint
node is explored in its own solver scope (`push`, then `pop`). On entry it asserts what both
sides produced since the last node (`assert_pending`).

At a node, both sides have advanced to their next decision point. `Engine::decide` picks the
first case that fits:

```text
both sides at terminals         → terminal pair          (section 7)
some side at a branch           → decide_branch          (section 5.1)
otherwise (samplings, or one
  sampling and one terminal)    → decide_sampling        (section 6)
```

### 5.1 Branches

Section 0 lists the rules. Here is what each rule produces:

```text
decide_branch(node):
    for side in [left, right]:                      # rule 1
        if side is not at a branch: continue
        (first, second) = decisions of the branch   # then, else
        p1 = ask "<side>-<first>-possible"   [c]    != unsat
        p2 = ask "<side>-<second>-possible"  [¬c]   != unsat
        if !p1 and !p2: return unreachable          # no children
        if p1 and !p2:  return determined, one child: side takes <first>
        if !p1 and p2:  return determined, one child: side takes <second>
        # both possible: try the other side

    if both sides at branches:                      # rule 2
        if ask "branches-differ" [¬(c_L = c_R)] == unsat:
            return synchronized, children (then,then), (else,else)

    # rule 3
    if both sides at branches:
        return split, children (then,then) (then,else) (else,then) (else,else),
               each checked for feasibility before it is explored
    else:
        return split, children: the branching side's then and else,
               each checked for feasibility; the other side waits
```

- **Children of `determined` and `synchronized`** are not checked again for feasibility: the
  queries that chose the rule already showed they are possible.
- **Children of `split`** run one `combination-feasible` query each. An `unsat` combination is
  recorded as *pruned* and is not explored.
- **Order of children.** Then before else, left before right. This also fixes the numbering of
  `J<n>` joint paths and `S<n>` stuck points, so an unchanged project gives the same ids.
- Every query a node makes is stored on the node (`answers`), in order, for the viewer.

### 5.2 Why this order

pRHL lets one program step alone. A determined branch costs EasyCrypt one `rcondt`/`rcondf`
and an easy side goal, and it does not double the tree. Taking it first keeps the other side's
branch free to be matched with its partner later, as a `synchronized` node or a one-sided
`split`. A synchronized `if.` costs one condition-equivalence side goal and gives two children.
A `split` gives up to four children and relies on the solver to prune the impossible ones, so
it comes last.

## 6. Samplings

Samplings are decided only when neither side is at a branch (`decide_sampling`):

```text
decide_sampling(node):
    if both sides at samplings of matching types:
        if ask "draws-differ" [¬(draw_L = draw_R)] == unsat:
            return sampling-synchronized, both draw

    for side in [left, right]:
        if side is not at a sampling: continue
        classify(side):
            premises = pairings of the randomness mapping that could pair this draw
            none                                    → independent
            ask "<side>-pairing-possible" [∨ premises] == unsat → independent
            for each premise i:
                ask "<side>-pairing-<i>-possible" [premise]
                    unknown → stuck: pairing-unknown
                    sat     → ask "<side>-pairing-<i>-valid" [¬premise]
                                unsat → valid (the pairing always holds)
            no premise live                         → independent
            some answer unknown                     → stuck: pairing-unknown
            valid and other side already ended      → stuck: no-partner-reachable
            valid                                   → stuck: partner-not-at-head
            otherwise                               → stuck: pairing-sat-not-valid
        if independent: return sampling-independent, this side draws alone

    return stuck at the first stuck side (left first); that side draws anyway
```

- The mapping's text is never read. Only its premises are asked about, so a mapping that
  depends on the state and the arguments works.
- **A stuck point does not stop execution.** It is recorded as `S<n>`, and the draw is still
  the game's `rand` term, so the mapping keeps constraining it on the rest of the path.
  Exploration continues below the stuck node, so `domino easycrypt debug` still reports what
  Domino concludes there. The prover admits the whole subtree with reason `stuck` and the
  worst Domino view below it.

## 7. Terminal pairs

When both sides reach a terminal, the joint path gets the next `J<n>` (or the run stops at
`--max-paths`). In a scope of its own (`check_pair`):

1. Both paths' remaining SMT and their return constraints are asserted.
2. **Vacuity check**, which always runs: if the result is `unsat`, the pair cannot happen.
   Every claim is then `unreachable` (pair infeasible). That is a different verdict from
   verified.
3. Each claim is checked with `check_claim`: its own declared dependencies plus its negated
   goal, in one `push` / `check-sat` / `pop`. `sat` writes a model to
   `models/<J>.<check>.smt2`.

On the EasyCrypt listing there are two claims:

| Claim | Goal | Dependencies |
|---|---|---|
| `equal-output` | `equal-aborts` and `same-output` together | None |
| `invariant` | The `invariant` goal on the new states | `no-abort` |

When the invariant is not verified, each `define-state-relation` is also checked on its own.
These relations are the conjuncts of the EasyCrypt `inv` operator, so an admit can name the
relation that failed. `invariant` depends on `no-abort` because EasyCrypt's `inv` guards the
relations with `!abort_flag`.

## 8. One-sided execution: side trees and package trees

`hoare` lemmas (side-invariant and package-invariant lemmas) have one program. Their trees come
from one-sided execution (`src/debug/side.rs`, `side_run.rs`, `package_run.rs`). It works the
same way with one column:

| Situation | Node kind |
|---|---|
| Branch with `c` or `¬c` `unsat` | `determined` (both `unsat`: `unreachable`) |
| Any other branch | `split`, both arms explored |
| Sampling | `sampling-independent` |
| Terminal | `terminal-pair` with no right side; the package and game invariant claims are checked |

There is no `synchronized` kind here, because there is no second side to synchronize with. A
side tree runs with the composition's parameters free (`domino easycrypt debug --game C`). A
package tree treats each import call as an open call (`--package P`).

## 9. From the tree to tactics

### 9.1 What the prover does at each node

This summarizes [proving-algorithm.md §3](proving-algorithm.md):

1. If every terminal below the node fails in Domino: admit `domino-fails`.
2. Quick close: `auto => /#.` under a short timeout (not on terminal pairs).
3. Dispatch on the node kind. The structural step (9.2) uses only the kind and the child steps
   recorded in the tree. Counts and names come from EasyCrypt's goal JSON (ADR 0002).
4. If the step did not apply (refused, or the wrong number or kind of goals), the node is
   undone and the **blind walk** runs (9.3).

### 9.2 Node kind to tactic

| Node kind | `equiv` (oracle lemma) | `hoare` (side and package lemmas) |
|---|---|---|
| `determined` | For each side that moved: `rcondt{i} ^if; 1: auto => /#.` (`rcondf` for `else`); if refused, `rcondt{i} ^if.` and the side goal on its own | `rcondt ^if; …` / `rcondf ^if; …` |
| `synchronized` | `sp`, then `if.`: condition side goal, then both children | n/a |
| `split`, both sides | `sp`, then `if{1}.`, and in each arm `if{2}.`: four children | n/a |
| `split`, one side | `sp`, then `if{s}.`: two children | `sp`, then `if.`: two children |
| `sampling-synchronized` | `sp`, then `seq 1 1 : (#pre /\ x{1} = y{2}); 1: <close>.` | n/a |
| `sampling-independent` | `sp`, then `seq 1 0 : (#pre); …` or `seq 0 1` | `sp`, then `seq 1 : (#pre); …` |
| `stuck` | Admit `stuck` | Admit `stuck` |
| `unreachable` | `exfalso; smt().`, else admit | Same |
| `terminal-pair` | Leaf procedure (proving-algorithm.md §6) | Same |
| Pruned child | `exfalso; smt().`, else `auto => /#.`, else admit | Same |

`determined` is the only kind that does not send `sp` first. Each `sp` adds existentials to the
precondition, and the `rcondt` side goal would have to reason about them. The straight-line code
left in front is taken by the next two-sided step's `sp` or by the leaf.

### 9.3 The blind walk

The blind walk (`prove_blind`) runs when a node's step does not apply, when the skeleton
alignment fails (9.5), and for reduction lemmas, which have no tree. It is the trial procedure
of `BranchingAlgorithm.pdf`, with no solver. EasyCrypt itself decides whether each tactic is
accepted. At each program head, after the quick close and `sp`, it tries in this order:

1. `rcondt{1} ^if; 1: auto => /#.`, then `rcondf{1}`, then `rcondt{2}`, then `rcondf{2}`, for
   each side whose head is an `if`;
2. `if.`, when both heads are `if`s;
3. `if{1}.`, then `if{2}.`;
4. `seq 1 1` with equal draws when both heads sample, else `seq 1 0` or `seq 0 1`;
5. Otherwise, admit `program-mismatch`.

Each trial is undone if it fails. The depth budget is 64. **Here too `rcondt`/`rcondf` comes
before `if.`**, the same priority lockstep execution uses, but proved by EasyCrypt instead of
predicted by the solver.

### 9.4 The exit path of a leaf

At a terminal pair, the programs may still contain `if`s that the IR does not have: done-flag
guards after the terminal, and the router tail `if (ec_result = None)`. Before `auto` reduces
the leaf to a formula, `decide_exit_path` decides them one at a time, side 1 first. Each is
decided with `rcondt{i} ^if; 1: by auto.` or `rcondf{i} …`, in the order `exit_decisions`
gives:

| `if` | First | Then |
|---|---|---|
| Router tail `ec_result = None`, side's terminal is an abort | `rcondt` | `rcondf` |
| Anything else (done-flag guard, router tail on a return, unknown terminal) | `rcondf` | `rcondt` |

If neither is accepted, the stage stops and `auto`'s `wp` takes that `if` into the formula.

### 9.5 Skeleton alignment

After `proc; inline.` the prover compares two **decision skeletons**, programs with their
straight-line code erased (`src/easycrypt/skeleton.rs`, `align.rs`). One comes from EasyCrypt's
goal JSON and the other from the IR. Equal kinds match, and branches recurse. An IR terminal
matches whatever EasyCrypt has left at that level, such as exit guards and the router tail. On a
mismatch the walk resynchronizes at the next pair of sub-skeletons that agree. If the skeletons
do not align, the guarded body is proved by the blind walk instead of the tree.

## 10. Running it

```text
domino easycrypt debug --theorem T [--gamehop N] [--oracle O] [--timeout MS]
domino easycrypt debug --theorem T --game C       # side trees
domino easycrypt debug --theorem T --package P    # package trees
domino easycrypt prove --theorem T [--gamehop N] [--oracle O] …
```

`debug` writes `<out>/<theorem>/!debug!/<left>-<right>/<oracle>/`: `index.html` (the joint-tree
viewer), `trace.json` (the tree with its fingerprint), `summary.txt`, `inlined.txt` (the
EasyCrypt listing the labels index), `smt/` (the base frame and the runnable queries of what
failed) and `models/`. It exits non-zero if any joint path fails `equal-output` or
`invariant`. `--timeout` is the per-query cvc5 limit. A timeout counts as `unknown`: the path is
explored, and its claim is never reported as verified.

`domino debug --lockstep` runs the same engine on the **Domino** listing. There each claim
keeps its own declared dependencies, and `assert`/`unwrap` decisions appear.

## 11. Where the code is

| Concern | File |
|---|---|
| Single-exit lowering | `src/transforms/easycryptify.rs` |
| EasyCrypt listing and IR | `src/writers/easycrypt/lower.rs` (`inline_oracle_ec`) |
| IR types, exit guards | `src/debug/ir.rs` |
| Per-side symbolic execution | `src/debug/exec.rs` |
| Joint tree, rule order | `src/debug/lockstep.rs` (`decide_branch`, `decide_sampling`, `classify`) |
| Base frame, claim sets, artifacts | `src/debug/lockstep_run.rs`, `lockstep_report.rs` |
| Claims at a terminal pair | `src/debug/claims.rs` |
| One-sided execution | `src/debug/side.rs`, `side_run.rs`, `package_run.rs` |
| Skeletons and alignment | `src/easycrypt/skeleton.rs`, `src/easycrypt/align.rs` |
| Tree to tactics, blind walk, exit path | `src/easycrypt/tactics/driver.rs` (`step_node`, `determined`, `synchronized`, `split`, `prove_blind`, `exit_decisions`) |
