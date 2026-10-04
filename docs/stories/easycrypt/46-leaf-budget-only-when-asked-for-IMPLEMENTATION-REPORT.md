# Story 46 `leaf-budget-only-when-asked-for` — implementation report

## What changed

- **`crates/domino/src/cli.rs`**: `EcProve.leaf_budget` is now `Option<u64>` with no default.
  The help text says: the seconds one leaf may spend being split by meaning before its remaining
  parts are admitted. Off unless given. Each sentence is still bounded by `--ec-timeout`.
- **`crates/domino/src/main.rs`**: maps the flag to `Option<Duration>` (`Duration::from_secs`).
- **`src/easycrypt/tactics/mod.rs`**: `TacticsOptions.leaf_budget` is `Option<Duration>`. The
  `Default` is `None` (it was 300 s).
- **`src/easycrypt/tactics/driver.rs`**
  - `Prover.leaf_budget` is `Option<Duration>`.
  - New pure function `leaf_deadline(budget, now) -> Option<Instant>`. It gives `None` when there
    is no budget, and `now + budget` when there is one. A budget of `0` gives `now`, so every part
    of the split is admitted at once. `0` has no special meaning.
  - `Prover::leaf_of` sets `deadline` from `leaf_deadline` before `solve_ambient` and clears it
    after. `solve_ambient` is unchanged: it already accepts `deadline: None`.
- **`src/easycrypt/tactics/tests.rs`**
  - `a_leaf_has_no_deadline_unless_a_budget_is_given`: `None`, `Some(5 s)` and `Some(0)`.
  - `the_leaf_budget_is_off_by_default`: `TacticsOptions::default().leaf_budget == None`.
  - The `Prover` in `the_fallback_proves_an_oracle_without_the_joint_tree` now has
    `leaf_budget: None`. That test does not depend on a budget.
- **`src/debug/sweep.rs`** (not in the story): a nested `if` is collapsed into one `if`. This
  removes the only `cargo clippy` warning in the workspace. Behaviour does not change.

## Verification

- Tests were written first. They did not compile (red) before `leaf_deadline` and the
  `Option` type existed. Then they passed (green).
- `cargo test --workspace`: 600 passed, 0 failed, 5 ignored (baseline: 598 passed; the 2 new tests
  make 600).
- `cargo clippy --workspace --all-targets`: 0 warnings.
- `domino easycrypt prove --help` shows the new help text for `--leaf-budget`.
- **Not done**: `--features cvc5-lib`. The `cvc5-sys` build script needs `cmake`, and `cmake` is
  not installed on this machine. This is an environment problem, not a code problem.
- **Not done**: the kem-dem run of §5. It needs EasyCrypt and takes a long time. The unit test
  on `leaf_deadline` covers the acceptance criterion on the deadline.

## Deviations and notes

- The story asks for a unit test of the deadline "around `solve_ambient`". A `Prover` needs a live
  EasyCrypt session, so the test is on the pure seam `leaf_deadline` that `leaf_of` calls.
  Rejected shape: a test that drives `leaf_of` through a real session. It needs EasyCrypt and
  it is slow.
- Implement-skill steps not done, because they apply only to the dotnet Sdlc repository: the
  `sdlc` index and CRAP gate, `/update-live-backlog`, the merge and push to main. The changed
  functions are small (`leaf_deadline` has CC 1; `leaf_of` has no new branch). The CRAP score
  is UNMEASURED.
- ADRs, earlier stories and earlier reports are not changed.

## State handed to the next story

- A tactics run has no leaf budget unless `--leaf-budget N` is given. Without it, the note
  `(leaf time budget spent)` cannot occur.
