# Story 25 — Implementation report: one-sided execution

`domino easycrypt debug --side-inv <C>` runs one-sided execution of each oracle of the composition
`C` (or of `--oracle O`) on the EasyCrypt listing. The parameters of `C` are free. Each run writes a
**side tree** under `<out>/<theorem>/!debug!/SideInv_<C>/<O>/`. The theorem's debug index lists the
runs.

## What changed

### The walk (`src/debug/side.rs`, new)

- `run_side` walks one side with the `SideExec` of lockstep execution. The rules are the one-sided
  part of lockstep execution:
  - a branch whose guard the solver decides is `determined`. If both arms are impossible, the node
    is `unreachable`. Otherwise the node is a `split` with both arms. Only `unsat` prunes.
  - a sampling is a draw with no pairing (`sampling-independent`).
  - exit guards are marked on the node view, as in lockstep execution.
  - at a terminal: the vacuity check, then each claim with `check_claim`.
- The output is a `LockstepOutcome`. So the side tree has the JSON shape of the joint tree. The
  right side of each node is `SideView::absent()` (new `HeadKind::Absent`). The right side of each
  terminal is `PairSide::absent()`. Terminals are `J<n>`, depth first, then before else.

### The composition with free parameters (`src/debug/side_run.rs`, new)

- `free_theorem` adds two game instances of `C` to a copy of the theorem: `C` and `C$side`. Each
  parameter is a theorem constant that nothing constrains. This is the theorem's constant of that
  name and type, or else a new constant `<C>_<param>`. `Bits(<param>)` in other parameter types is
  rewritten, as the theorem parser does.
- Because the instance is named `C`, the claims and the invariant definitions are named
  `package-invariant!<C>-<PkgInst>!` and `game-invariant!<C>!`.
- The SMT vocabulary comes from an `EquivalenceContext` of `C` against `C$side`. Only `C` is
  executed and asserted. The copy is in the base frame as declarations and definitions only.
- The base frame: the declarations and definitions that `prove` uses, then each package and game
  invariant of `C` on the old state (`EquivalenceContext::emit_left_side_invariants_old`, new).
- The claims: each package invariant of `C`, then its game invariant, on the new state. Each one
  depends on `left-no-abort`. At a terminal that aborts, `check_claim` gives `unreachable`
  (dependency false) with no solver call. This is "an abort has nothing to check".
- `run_side_command` writes `trace.json`, `summary.txt`, `index.html`, `models/` and the result
  record `one-sided_result.json`. `LockstepMeta` has two new fields: `one_sided` and
  `fingerprint` (ADR 0008: `all` and the five parts; `Fingerprint::of_side`, new). Both are left
  out of a joint tree's `trace.json`.

### Claim names (`src/writers/smt/contexts/equivalence/emit.rs`)

- `package_invariant_claim_name(owner, pkg_inst)` and `game_invariant_claim_name(owner)` take the
  owner of the state: a game instance in lockstep execution, a composition in one-sided execution.
  The names of lockstep execution do not change.
- `smtrewrite.rs` built the same names with its own `format!`. It now calls the two owners.

### CLI and index

- `domino easycrypt debug` has `--side-inv <C>` (conflicts with `--proofstep`). It calls
  `easycrypt::debug::debug_side_invariants` (new). That function runs every selected oracle and then
  refreshes the theorem-level index.
- `ResultRecord` and `SweepEntry` have a new field, `composition`. The index has a new level,
  `Level::SideInv` (`<theorem>/!debug!/SideInv_<C>/`). The theorem index shows one row
  `side-inv  <C>` for each composition, after the proofsteps, and links to its index.

### Viewer (`src/debug/lockstep_viewer.html`)

- With `one_sided`, the viewer hides the right listing, the right column of the path table and the
  right effect column. The header says "side invariants of `<C>`".

### Bug fix found on the way (`src/util/smtsolver/process.rs`)

- After `get-model`, the newline after the model stayed in the read buffer. The next `check-sat`
  then never matched `sat\n`, so the process backend waited forever. The answer predicate now skips
  leading whitespace. Lockstep execution with `IncrementalCvc5Backend` had the same hang after a
  failing check.

## Tests

- `debug::side_run::tests` (cvc5 process, `testdata/debug/se25`, new fixture: composition `S`
  with parameter `n`, package `P` with invariant `k >= 0`):
  - `a_side_run_checks_the_composition_claims_and_fails_only_the_breaking_path`: the root is a
    `split` on `n > 0` (the parameter is free, although both instances in the theorem fix `n = 1`).
    There are four terminals. The package invariant fails on the two `x < 0` terminals and is
    verified on the others. The game invariant is verified everywhere. The artifacts exist.
  - `claim_names_are_of_the_composition_from_the_one_owners`.
  - `the_theorem_index_lists_the_side_runs_and_links_their_index`.
  - `the_side_debug_dir_is_under_side_inv`.
- `debug::side_run::full_4whs::h6_on_full_4whs_writes_a_side_tree_for_each_oracle` (`#[ignore]`,
  about 2 minutes): H6 on Full4WHS, all 10 oracles. Every oracle wrote `trace.json` and
  `index.html`, and every side tree is ok. No EasyCrypt was run.
- Full `cargo test --lib`: 740 passed, 0 failed, 6 ignored. `cargo clippy --workspace`: no warnings.
  `cargo build --release --workspace`: succeeds.

## Deviations and open issues

- `--features cvc5-lib` cannot build in this environment (no cmake). So the CLI path of
  `--side-inv` (which, like all of `easycrypt debug`, needs `cvc5-lib`) was compiled only without
  that feature. It is not built or run. The library path was tested with the cvc5 process backend.
- The side run does not refresh its page while it runs and writes no `smt/` files for each path.
  It writes the page at the start and at the end.
- The index rows of the EasyCrypt listing's lockstep runs are not in the index (they write no
  result record, as before). Only side runs are listed under `_build/easycrypt/<theorem>/`.
- The viewer change was not checked in a browser.
