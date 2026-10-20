# Story 29 — Implementation report: the package tree

`domino easycrypt debug --theorem <T> --pkg-inv <P>` runs one-sided execution of each oracle of
package `P` (or of `--oracle O`) on the EasyCrypt listing of the package procedure alone. Each import
call is an **open call** (ADR 0017). The package parameters are free. Each run writes a **package
tree** under `<out>/<theorem>/!debug!/PkgInv_<P>/<O>/`. The theorem's debug index has one row
`pkg-inv  <P>` for each package, after the `side-inv` rows.

## What changed

### Open calls are found from the import interface (no flag)

- `transforms/resolveoracles.rs`: an import that the composition does not wire keeps
  `edge: None`. This is an open call. A name that the package does not import is still an error.
  A parsed game wires every import, so only a package alone (the game of the package check) has
  open calls.
- `transforms/easycryptify.rs`: the type of an open call comes from the package's import
  signature (`Lowerer::callee_type`).
- `transforms/sample_max_counter_extractor.rs`: an open call samples nothing of the game.
- `debug/ir.rs`: new statement `InlStmt::OpenCall { label, bind, ty }`. Only the EasyCrypt
  lowering makes it. It is not a decision point.
- `writers/easycrypt/lower.rs`: an `invoke` with no edge is lowered by `lower_open_call` to
  `ec_r<N> <@ O.<import>(args);` and an `OpenCall`. It is not inlined.
- `debug/exec.rs`: an `OpenCall` binds a fresh SMT constant with no definition. The call-result
  guard after it is a normal branch: the solver prunes an arm only when it is impossible.
- `easycrypt/skeleton.rs`: an `OpenCall` is an `Unknown` node, as EasyCrypt shows the `call`.

### The listing of the package procedure

- `writers/easycrypt/lower.rs`: new `package_oracle_ec`. It lays out the package's own
  procedure (`ProcShape::Package`): no router prelude, no abort flag, state variables not
  qualified, the fall-through `return ec_result;` is the abort. `inline_oracle_ec` is unchanged
  (`ProcShape::Router`). The listing has the text of `Pkg_<V>.ec`.

### The package tree (`debug/pkg_run.rs`, new)

- `run_pkg_command` checks that the theorem uses `P`, builds the `PackageInvariantContext` of the
  package check of story 75, and walks the listing of `open_theorem()` (the same one-game theorem
  with the imports open, so the SMT names are equal).
- `PackageInvariantContext` (new methods): `open_theorem`, `emit_tree_base_frame` (the
  declarations of the package check, the walked oracle's return value left to the walk, each named
  invariant on the old state), `tree_claim_queries` (each named invariant on the new state, under
  `no-abort`). `emit_oracle_claim_assert` now uses the same helpers. The claim names come from the
  context, so they are `package-invariant!<name>!<P>!`.
- `pkg_listing` gives the listing (for the alignment test and for EC 76).

### Shared one-sided code (`debug/side_run.rs`)

- `StateOwner` (`Composition` or `Package`) is the owner of the state. `execute_one_sided` does
  the part that is the same for a side tree and a package tree (meta, solver, `run_side`, files,
  result record). `run_one_sided_command`, `one_sided_oracles`, `one_sided_debug_dir` and
  `one_sided_entry` select by the owner. `side_entry` is replaced by `one_sided_entry`.
- `easycrypt::debug::debug_side_invariants` is replaced by `debug_one_sided(owner, …)`.

### Index, records, viewer, CLI

- `ResultRecord` and `SweepEntry` have a new field `package`. The index has a new level
  `Level::PkgInv` (`!debug!/PkgInv_<P>/`, title "package invariants of `<P>`").
- `LockstepMeta.subject`: "side invariants of `<C>`" or "package invariants of `<P>`". The
  viewer header shows it.
- `domino easycrypt debug --pkg-inv <P>` (conflicts with `--proofstep` and `--side-inv`).

### Fixed on the way

- `debug/view.rs`: a loop that is not unrolled was always printed as `a <= i <= b`. It now
  prints the comparisons that the loop declares (`0 <= i < n`). This is the debugger code that
  copied the old `loopunroll` range.

## Tests

- `debug::pkg_run::tests` (`testdata/debug/se29`, new fixture: package `Ctr` with invariant
  `ctr >= 0` and imports `Get`, `Put`):
  - `the_call_result_guard_splits_the_none_arm_aborts_and_the_some_arm_verifies` (`Step`).
  - `a_path_that_breaks_the_invariant_fails_and_the_claim_is_named_by_its_owner` (`Bad`).
  - `the_tree_has_the_decision_skeleton_of_the_exported_package_procedure`: for `Step`, `Bad`
    and `Ping`, the skeleton of the listing equals the skeleton of `d_<O>` in the exported
    `Pkg_Ctr` module (the EasyCrypt AST, not a run of EasyCrypt).
  - `the_theorem_index_lists_the_package_trees_and_links_their_index`.
  - `a_package_the_theorem_does_not_use_is_an_error`, `the_package_debug_dir_is_under_pkg_inv`.
- `transforms::resolveoracles::tests` (new): an unwired import is an open call; an unknown name
  is an error.
- `debug::view::tests::a_loop_keeps_its_declared_comparisons` (`testdata/debug/view-loop`).
- The story-25 tests of `side_run` pass unchanged.

## Deviations and open issues

- The base frame declares the closed oracles' return values (with the call-result record
  argument) for the oracles that are not walked. The walked oracle's return value is not defined
  by its oracle function; the walk defines it.
- The `--pkg-inv` run does not use the package variant: the listing is of the package with free
  parameters, which is the same code for every variant. The check "the theorem uses `P`" is the
  only use of the theorem.
- The page was not checked in a browser.
