# Story 32 — `domino debug --game C`: the side tree on the Domino listing

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 30, 25, 22.
**Blocks:** 33.
**ADR:** 0021; 0014; 0011 (a debug index renders the records on disk).
**Decisions:** grilling of 2026-10-21/22, Questions 4–8, 14, 15.

A **debugger** story, Rust only. Test-first.

---

## 1. Why this story exists

When `domino prove --game C` (story 30) fails, the owner gets one verdict for each oracle. The side
tree of story 25 shows which path breaks which game invariant, but only on the **EasyCrypt listing**
(`domino easycrypt debug --side-inv C --theorem T`). `domino debug` has no one-sided run. The
glossary says that `domino debug` walks the Domino listing, so the owner must today read the
EasyCrypt code to debug a Domino game invariant.

After this story:

```
domino debug --game C [--oracle O] [--claim <name>]
```

runs one-sided execution of each oracle of C on the **Domino listing**, with no theorem.

Vocabulary (`CONTEXT.md`, already updated): **One-sided execution** ("like a strategy, it walks
either listing"), **Listing**, **Side tree**, **Debug index**.

## 2. Inherited

- Story 25: `src/debug/side.rs` (`run_side`), `src/debug/side_run.rs` (`run_side_command`,
  `execute_one_sided`, `OneSidedInputs`, `StateOwner`, `one_sided_entry`), the one-column viewer, the
  result record `one-sided_result.json`.
- Story 30: `src/game_invariant/`, the free composition from C alone, and its `EquivalenceContext`.
- `src/debug/lockstep_run.rs:676`: `ListingKind::{Domino, EasyCrypt}`, and the Domino listing from
  `inline_oracle` (`src/debug/ir.rs:351`) on the `DebugTransform` of the instance.
- Story 22: `src/debug/index.rs` (`Level`, the indexes at each level), `src/debug/layout.rs`
  (`DOMINO_DEBUG_DIR`, `claim_dir`, `ALL_CLAIMS_DIR`).

## 3. Work to do

### 3.1 The listing

- One-sided execution takes the listing kind from the command, as lockstep execution does:
  `domino debug` gives `ListingKind::Domino`; `domino easycrypt debug/prove` gives
  `ListingKind::EasyCrypt`. The engine, the claims, the base frame and the artifacts are the same for
  both. Only the inlined oracle differs.
- On the Domino listing the free instance `C` goes through `DebugTransform` and `inline_oracle`. The
  parameters are free, so no branch on a parameter folds.
- The EasyCrypt side does not change: its trace, base frame and fingerprint are byte-identical.

### 3.2 The CLI

- `Debug` gets `--game <C>`. Help text: "One-sided execution of each oracle of this composition (as in
  `games/C.comp.ssp`; not a game instance) on the Domino listing, with its parameters free. Needs no
  theorem. Checks the game invariants; assumes the package invariants. The start check is
  `domino prove --game C --invariant-start`."
- Accepted with `--game`: `--oracle`, `--claim`, `--timeout`, `--max-paths`, `--smt`, `--transcript`,
  `--progress`, `--out`, `--path`. They go into `LockstepDebugOptions` as for a lockstep run.
- Refused with `--game` (clap `conflicts_with_all`): `--proof`, `--proofstep`, `--claim-set`,
  `--lockstep`, `--no-check-left`, `--no-check-right`, `--first-failure-per-claim`.
- `--claim <name>` is the **exact** declared name of one game invariant of C, as `--claim` on a
  two-sided `domino debug` run is exact. The run checks only that invariant at each terminal; the
  paths are the same. An unknown name is an error that lists the game invariants of C.
- The same errors as story 30 for an unknown composition, a composition with no game invariant, and
  an unknown oracle.
- Without `--oracle`, every exported oracle of C runs, one after another.
- The exit code is non-zero when a check fails or the run stops early, as for `domino debug`.

### 3.3 Output and index

- The run directory is `<root>/!game!/<C>/<O>/<claim-dir>/`, where `<root>` is `--out` or
  `_build/debug`, and `<claim-dir>` is `claim_dir(claim, false)`: `<name>` with `--claim`,
  `!all-claims!` without. `!` is not in the `identifier` rule of `ssp.pest`, so `!game!` cannot clash
  with a theorem name.
- In the run directory: the artifacts of a one-sided run (`index.html`, `trace.json`, `summary.txt`,
  `models/`, `smt/` as `--smt` says, and `one-sided_result.json`).
- A new index level `Level::Game { composition }`, directory `<root>/!game!/<C>/`, parent
  `Level::Project`. The project index lists one row `game  <C>` for each composition with a run on
  disk, after the theorems. The index shows what is on disk (ADR 0011).
- The result record names the composition as its owner, as on the EasyCrypt side. The synthetic
  theorem name (`<C>$Invariant`) is not shown in the index.
- The viewer's one-column mode says "game invariants of `<C>`", and the summary says which package
  invariants it assumes (as story 30).

## 4. Rejected alternatives

- **The sequential driver with no right side** (Question 6): a mode flag in `driver.rs`, the
  largest module, that each part must check; with one oracle, all walks give the same tree.
- **Refuse `--claim`** (Decision 7, changed by Question 14): the owner wants to choose one
  invariant in `debug` too.
- **`--claim` as a wildcard in `debug`** (Question 14): a pattern is a bad directory name, and
  two-sided `debug` takes an exact name.
- **`_build/debug/SideInv_<C>/`** (Question 8): a theorem can have that name, and the glossary keeps
  EasyCrypt names off the Domino listing.
- **`_build/debug/<C>/`** (Question 8): a theorem and a composition can have the same name.
- **A start-check run in `debug`** (Question 15): `init` has no branches; a one-node run kind is a
  special case in the index, the layout and the record.

## 5. Tests first

- [ ] Red: `testdata/debug/se25`, `debug --game S --oracle O`: the root is a `Split` on `n > 0`,
      there are four terminals, the two with `x < 0` fail `main`, the other two verify. The labels
      are lines of the Domino listing.
- [ ] Agreement: the verdict of each terminal is the same as in `easycrypt debug --side-inv S`
      (same number of terminals, same failing paths).
- [ ] `testdata/debug/se25-name-taken`: `debug --game S` executes the free instance, not the
      theorem's instance `S` (`n: 1`): the root is still a `Split` on `n > 0`.
- [ ] The directory is `_build/debug/!game!/S/O/!all-claims!/`; with `--claim main` it is
      `…/O/main/`; with `--out X` it is under `X`.
- [ ] `--claim nope` gives the error with the list `main`.
- [ ] The project index lists `game  S` and links `!game!/S/index.html`; that index lists `O`.
- [ ] clap refuses `--game` with each flag of the refused list.
- [ ] The EasyCrypt side tree of `se25` is byte-identical before and after (trace claims, base
      frame, fingerprint).
- [ ] A two-sided `domino debug` run does not change (an existing test).

## 6. Acceptance criteria

- [ ] All tests of §5 green.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 7. How to verify

```bash
cd testdata/debug/se25
$D debug --game S && open _build/debug/!game!/S/O/!all-claims!/index.html
$D debug --game S --claim main
```
