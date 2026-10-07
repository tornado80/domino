# Story 21 — Implementation report: each check has its own verdict, and a failing invariant is broken down

The claim checker now owns the breakdown of `invariant` into its parts. Both strategies get the
breakdown from `check_claim`, in all-claim runs and in single-claim runs. The parts are checked
inside the dependency frame of the claim. Both pages use one shared Verdicts renderer. No page on
the Domino listing shows an EasyCrypt operator name.

## What changed

### The claim checker (`src/debug/claims.rs`)

- `ClaimQuery` has a new field:

  ```rust
  /// The named parts of the goal, each negated; empty for every claim but `invariant`.
  pub parts: Vec<(String, SmtExpr)>,
  ```

  - **Domino listing:** `ClaimQuery::of` fills `parts` for the claim `invariant`: each state
    relation except `invariant`, named `state-relation <name>` (`state_relation_part`).
  - **EasyCrypt listing:** `easycrypt_invariant_query` (`lockstep_run.rs`) fills `parts` with
    `Domino_<r>` for each state relation except `invariant` (`relation_op_name`), then the
    `PkgInv_<l|r>_<Inst>` and `GameInv_<GameInst>` operators of `side_invariant_ops` that have
    a claim.
- `check_claim` returns a `ClaimVerdict`. When the verdict is goal-fails or inconclusive, the
  new function `check_parts` checks each part inside the dependency frame of the claim: `push`,
  the negated part, `check-sat`, `pop`. The model of a failing part goes to
  `models/<pair>.<claim>.<part>.smt2`. A space in the part name becomes `-` in the file name
  (`1.1.invariant.state-relation-rel_ctr.smt2`), so the page can link the file.
- `check_negated` is the one function that asserts a negated goal and classifies the answer. The
  claim goal and each part use it.
- `ClaimGoalView { claim, dependencies, smt, parts: Vec<PartGoalView { name, smt }> }` is the
  rendered form of a check. `ClaimQuery::view()` makes it. Both traces carry it.
- `no_dependency_claim` and `state_relation_parts` moved here from `lockstep_run.rs`.

### Verdicts (`src/debug/driver.rs`)

- `ClaimVerdict.relations` is now `ClaimVerdict.parts: Vec<PartVerdict>`. `ClaimVerdict` also
  has `model: Option<String>` (the model text of a failing check).
- `PartVerdict { name, verdict, model: Option<String> }`. `model` is the model text.
- On a pair where the claim is verified or unreachable, `parts` is empty.
- `--first-failure-per-claim`: a skipped claim is not checked, so its parts are not checked.
- A single-claim sequential run records its claim verdict in `RightPath.claims` only when the
  verdict has parts. Otherwise `claims` stays empty, as before.
- `GoalBlock` has `parts`. `GoalBlock::render` writes one check of an `smt/` file in the order
  the solver got it: `push`, dependencies, `push`, negated goal, `check-sat`, `pop`, each part
  with a verdict, `pop`. The sequential and the lockstep `smt/` writers both use it.
- `DebugRun.checks: Vec<ClaimGoalView>`: the checks of the run, for the page.
- `ClaimVerdict::failing_checks` gives `invariant → state-relation rel_ctr` for each failing
  part. `summary.txt` uses it in its failure blocks, and the per-path tree lists the parts under
  their claim.
- `render_tree` was over the complexity budget. Its right-path body is now `write_right_path`.
  The failure blocks of `report::render_summary` are now `failing_pairs`.

### Lockstep (`src/debug/lockstep.rs`, `lockstep_run.rs`)

- `LockstepEngine::check_pair` has no state-relation loop and no `check_goal`. It calls
  `check_claim` for each claim. `RelationGoal`, `RelationVerdict`, `LockstepTerms::relations`
  and `LockstepTerms::side_invariants` are deleted.
- `PairRecord::relations()` is now `PairRecord::parts()`.
- `GoalsView` has only `claims: Vec<ClaimGoalView>`. The part goals are in each claim.
- On the EasyCrypt listing, the negated goal of `invariant` is the negation of the whole
  conjunction: the `invariant` relation and each package and game invariant claim, on the new
  states. A verified `invariant` thus means that every part is verified.
- `easycrypt_check_names` (the `claims` part of the fingerprint) lists `equal-output`,
  `invariant`, then the part names. A tree saved before this story is stale, and it is still
  used.

### The tactics run (`src/easycrypt/tactics/`)

- `pair_view`, for `Part::Relation(r)` and `Part::SideInvariant { op, .. }` (new function
  `part_view`):
  - `invariant` verified or unreachable: the part has that view.
  - else: the view of its own part verdict (by EasyCrypt operator name: `relation_op_name(r)` or
    `op`), with the rule for aborting pairs;
  - else (no part verdict, for example a tree saved before this story): `Inconclusive`. It is
    never the `invariant` verdict when `invariant` failed.
- `side_invariant_view` is deleted.
- `WalkedTree.relations` comes from `EquivalenceReport.state_relations`, which comes from the
  new field `InvariantFile.state_relations` (the SMT names of every translated
  `define-state-relation`, `invariant` too). `SavedTree.relations` stays and gets the same
  value. The unfold list therefore still holds `Domino_invariant`.

### The pages (`src/debug/report.rs`, `lockstep_viewer.html`)

- **The shared Verdicts renderer** is `VERDICTS_JS` and `VERDICTS_CSS` in `report.rs`, next to
  `GRID_CSS` and `LISTING_JS`. Both pages splice it in at `__VERDICTS_JS__` and
  `__VERDICTS_CSS__`. It has:
  - `verdictsList(claims, checks, opts)`: one row for each check. The part rows are under their
    claim. A part with no verdict says `not checked: invariant verified` (or the verdict that
    the claim has). Each failing check has its own collapsed model text.
  - `checkBlocks(checks, claims)`: one block for each check, in the order the solver got them.
  - `checksQueryText(checks, claims)`: the same sequence as SMT-LIB text.
  - `failingChecks(claims)`: the text for the tree rows.
- **Sequential page:** a tree row shows `GOAL FAILS [invariant → state-relation rel_ctr]`. The new
  Verdicts section replaces the Model section. The Claim assertion section has one block for
  each check. "Copy runnable query" copies the base frame, both paths, the vacuity `check-sat`,
  then each check as the solver got it.
- **Lockstep page:** the Verdicts and Claim assertion sections use the shared code. The names
  come from the trace. The page has no `Domino_` prefix of its own.

### Schema numbers

- `TRACE_SCHEMA` (`driver.rs`): 9 → **10**.
- `LOCKSTEP_TRACE_SCHEMA` (`lockstep_run.rs`): 12 → **13**.

## Test project

`testdata/debug/story21/`: theorem `T`, oracle `Bump`. `invariant` is `rel_ctr ∧ rel_seen`. On
the left side a positive argument increments `ctr`. On pair `#1.1` (`J1`), `rel_ctr` fails and
`rel_seen` holds. Pair `#2.1` (`J2`) is verified.

## Tests

New:

- `debug::claims::tests::on_a_solver::the_parts_are_checked_under_the_claims_dependencies`
  (cvc5-lib): `invariant` depends on the lemma `x > 5`. The part `x > 3` is verified, because it
  is checked with the lemma. The old lockstep loop failed it.
- `debug::claims::tests::on_a_solver::a_verified_claim_checks_no_part` (cvc5-lib).
- `debug::driver::story21_tests::a_sequential_run_breaks_a_failing_invariant_down_by_state_relation`
  (cvc5-lib): the parts on `#1.1`, no parts on `#2.1`, a model for each failing check, no
  `Domino_` on the page.
- `debug::driver::story21_tests::a_single_claim_run_on_invariant_has_the_breakdown_too` (cvc5-lib).
- `debug::lockstep_run::tests::a_lockstep_run_on_the_domino_listing_breaks_a_failing_invariant_down`
  (cvc5-lib).
- `debug::lockstep_run::tests::the_one_sided_parts_are_checked_only_where_invariant_is_not_verified`
  (cvc5-lib, replaces story 58's `every_pair_has_a_sub_verdict_for_each_one_sided_invariant_claim`):
  the `invariant` goal holds the four one-sided claims; the parts are `PkgInv_l_C`,
  `PkgInv_r_C`, `GameInv_L`, `GameInv_R`; they have verdicts only where `invariant` is not
  verified.
- `writers::easycrypt::invariant::side::tests::the_unfold_list_from_the_invariant_files_relations_holds_domino_invariant`.
- `easycrypt::tactics::tests::a_part_on_a_pair_with_invariant_verified_is_verified`.

Changed:

- `a_failing_invariant_is_broken_down_by_state_relation` is now
  `a_failing_invariant_is_not_a_part_of_itself` (the `rules` project has only `invariant`).
- `a_joint_path_smt_file_reproduces_the_recorded_verdicts` replays the `smt/` file line by line
  and checks each claim and each part.
- `a_one_sided_invariant_part_has_the_view_of_its_own_part_verdict` and
  `dominos_verdicts_steer_per_claim_and_per_relation`: the new `pair_view` rule. A part with no
  verdict where `invariant` failed is `inconclusive`.
- The schema numbers, the fingerprint hash, and the saved-tree fixture (`parts`, not
  `relations`).

## Verification

- Baseline before the change: `cargo test --workspace`: 657 passed, 0 failed, 5 ignored (lib).
  With `--features cvc5-lib`: 756 passed, 1 failed (`an_interrupt_never_answered_is_unresponsive_after_six_signals`,
  a timing test), 6 ignored (lib).
- After: `cargo test --workspace`: 659 passed, 0 failed, 5 ignored (lib); all other test
  binaries pass. With `--features cvc5-lib`: 762 passed, 2 failed (lib). The two failures are
  the interrupt-timing tests `an_interrupt_never_answered_is_unresponsive_after_six_signals`
  and `an_unanswered_interrupt_seals...`. Both pass when they run alone.
  `debug_announces_translation...` failed one time in the full run, because a time (`[0.2s]`)
  is in its stdout. It passes alone 3 times out of 3.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: 0 warnings.
- Story §5 on `testdata/debug/story21` (the example project has no failing `invariant` with two
  state relations): `grep -c Domino_` on both viewers gives 0.
- "Copy runnable query" of pair `#1.1`, taken from the page in headless Chrome, given to
  `cvc5 --incremental --produce-models`: `sat` (vacuity), `unsat` (equal-aborts), `unsat`
  (same-output), `sat` (invariant), `sat` (state-relation rel_ctr), `unsat`
  (state-relation rel_seen). These are the recorded verdicts.
- Story §7: on the story-58 project `OneSided` `Inc` (1 joint path) the lockstep time is below the
  0.1 s resolution of the report, before and after.

## Screenshots

`21-screenshots/` (headless Chrome, `--force-prefers-reduced-motion`):

- `1600-sequential-1.1.png`, `800-sequential-1.1.png`: the sequential page on `#1.1`, the detail
  pane scrolled to the Verdicts section.
- `1600-lockstep-J1.png`, `800-lockstep-J1.png`: the lockstep page on `J1`.

## Left open

- The complexity gate (`sdlc crap gate`) is **UNMEASURED**: `sdlc` is not installed here. As a
  proxy, `clippy::cognitive_complexity` with threshold 14 names no function that this story
  added or changed.
- A claim that is unreachable because the solver finds a dependency false: the runnable query
  has the goal check and the `check-sat` of the dependencies, but not the search for the false
  dependency (`dependency_false_here`).
- A saved tree from before this story has no part verdicts. Its parts are `Inconclusive` where
  `invariant` failed. The fingerprint already marks such a tree as stale.
- Owner-run: a tactics run on `Simple4WHS` `Hybrid1 ~ Hybrid2` to compare the leaves that admit
  a `PkgInv_`/`GameInv_`/`Domino_` part with the run before this story.
