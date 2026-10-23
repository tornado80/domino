# Story 93 — Implementation report: invariant selection keeps the conjuncts that share a table

Rust only. No ADR. This change uses the seams of story 92: `drop_ops`, `pruned_crush_sentence`,
`try_pruned_crush` and `fallback(...)`.

## What changed

### The conjuncts and their footprints (`src/writers/easycrypt/invariant/side.rs`, `invariant.rs`)

- New private `conjuncts(game, name, ctx, ops)`: the conjuncts of `side_inv_<C>` in the order of
  its body (package wrappers, `links_<C>`, game invariants). Each conjunct has its operator, the
  item that defines it, its footprint and its part (package or game). `composition_items` now
  builds `side_inv_<C>`, `pkg_inv_<C>` and `game_inv_<C>` from this list. Thus the list and the
  body cannot get out of order (§3.1).
- New `ModuleVars`: a map from a side-record projection (`<C>_pkg_<I>`, `<P>_<f>`) or
  (`<C>_params_<I>`, `<P>_param_<p>`) to the module variable `Comp_<C>.Pkg_Inst_<I>.<var>`.
  - The footprint of a game invariant and of the links: the projections of the translated body.
  - The footprint of a package wrapper: the projections `s.<f>` and `p.<p>` of the template body
    (from `package_templates`), in the fields of its instance.
- New `module_var_path` (`invariant.rs`). `proof.rs` `module_var` (the precondition's record
  literal) now uses it too. Thus the footprint and the precondition use the same function.
  `game::instance_mangled_names` is now `pub(super)`, for the same instance names.
- New public `SideConjunct { op, footprint }`, `SideConjuncts` (a map keyed by
  `Comp_<C>.side_inv_<C>`) and `side_conjuncts(theorem, project, comps)`.
- New `EcExpr::children` (`ast.rs`): the direct sub-expressions, for the walk of the footprint.

### The invariant selection (`src/easycrypt/tactics/goals.rs`)

- New pure function `selection_sentence(goal, drop_ops, conjuncts) -> Option<String>` (§3.2).
  Deviation from the spec signature: it takes the `Goal`, as `pruned_crush_sentence` does,
  because the names must be fresh against the hypotheses.
- The tables of the conclusion are its global program variables without memory (new
  `global_var`; `atom_text` now uses it). A `side_inv` premise is kept when:
  its record reads a memory of the conclusion, a premise
  `!Comp_<C>.Game_<C>.abort_flag{m}` of that memory exists (the negation is `[!]` or `!`), and
  one or more conjuncts have a footprint that meets the tables.
- The kept premise is `hs<k>`; each selected conjunct is `g<k>_<j>` (`j` is the index of the
  conjunct), every other conjunct is `_`. The `[#]` pattern has one item per conjunct. The g
  names take the place of `hs<k>` in `move:`. Other `side_inv` premises get `_`.
- Example (scripted test):
  `move=> h0 hs1; have := hs1; rewrite /Comp_H.side_inv_H /= => /(_ h0) [#] g1_0 _; clear hs1;
  move: h0 g1_0; rewrite /Comp_H.GameInv_b_of_H /=; smt().`

### The fallback sequence (`src/easycrypt/tactics/driver.rs`, `mod.rs`)

- `FALLBACKS` is 5. New `pruned_fallbacks`: fallback 4 (pruned crush), then fallback 5
  (`invariant selection` on the live page) on the goal that the pruned crush read. There is no
  new read sentence. The open `move=> /> <mems>.` is undone unless one of them closes the goal.
- `try_pruned_crush` now undoes only the pruned sentence when it fails, and gives the opened goal
  to the caller. New `try_selection`.
- New `Prover::conjuncts: &SideConjuncts`. `mod.rs` fills it with `side_conjuncts` for the same
  compositions as `drop_ops` (none for a package-invariant job).

## Tests

Ran, filtered, `--test-threads=1`, under `systemd-run -p MemoryMax=6G`. No test starts
EasyCrypt or cvc5. All green. Last runs: `tactics::goals` 27 of 27, `side_goal` 6 of 6,
`fallback` 5 of 5, `selection` 4 of 4, `pruned` 7 of 7, `crush` 14 of 14, `time_by_role` 7 of 7,
`transcript` 19 of 19, `tactics::live` 25 of 25.

New in `invariant/side.rs` (translation of the new fixture `testdata/easycrypt/story93`, no
export):

- `the_conjunct_list_has_the_order_of_the_side_invariant_body` (§5 test 1): package invariant,
  links and two game invariants, in the order of the body of `side_inv_C`.
- `the_footprint_of_a_conjunct_holds_the_module_variables_it_reads` (§5 test 2):
  `GameInv_tables_of_C` has `Comp_C.Pkg_Inst_P.keys` and `Comp_C.Pkg_Inst_P.seen`.

New in `goals.rs` (pure):

- `the_selection_names_only_the_conjuncts_that_read_a_table_of_the_conclusion` (§5 test 3).
- `without_an_abort_premise_a_table_or_a_selected_conjunct_there_is_no_selection` (§5 test 4).
- `a_branch_condition_that_reads_only_memory_2_keeps_only_the_side_invariant_of_2` (§5 test 5).

New in `tactics/tests.rs` (scripted fake EasyCrypt, §5 test 6):

- `after_a_failed_pruned_crush_the_selection_closes_the_side_goal_without_a_new_read`.
- `a_failed_selection_is_rolled_back_and_the_side_goal_is_admitted`.

Note on the order of work: the tests of each slice were written before the code, but the code of
the translation slice and of the driver slice was compiled together with its tests. Thus a red
run was seen only for the `goals.rs` slice.

Note: one filtered run (`side::tests::the_`) also ran some existing tests of `side.rs` that
export small test projects in Rust (no EasyCrypt, no cvc5) and one that parses
`example-projects/4WHS`. They passed (12 of 12). This was not intended; the later runs were
filtered more exactly.

### Written, not run (deferred until the proofstep 11 job finishes)

- `the_footprints_name_the_module_variables_of_the_exported_precondition` (`invariant/side.rs`,
  §5 test 2 against the export). It exports `testdata/easycrypt/story93`. Command:
  `systemd-run --user --scope -p MemoryMax=6G timeout 900 cargo test -j 4 --lib the_footprints_name_the_module_variables -- --test-threads=1`
- Story 92's `the_drop_list_of_an_equivalence_holds_both_side_invariants_of_the_precondition`
  stays deferred. Command:
  `systemd-run --user --scope -p MemoryMax=6G timeout 900 cargo test -j 4 --lib the_drop_list_of_an_equivalence -- --test-threads=1`

## Acceptance criteria not done here

- The owner's check on `ec4whs` (the runs of story 92 §6 with this story): at most 14
  `branch-condition` and `side-goal` admits, the 5 goals of §1.1, no new oracle admit, and the
  row for fallback 5 in the per-hop table. Big project: not run. The owner runs them.
- The risk of §3.3 (module variables, not bare field names) can only be seen in those runs.
- Complexity: UNMEASURED (no Rust recipe for `sdlc crap`). By hand, each function in the diff
  has a cyclomatic complexity under 15. `EcExpr::children` is one flat `match` with 9 arms.

## Clippy

`cargo clippy --all-targets`: clean. `cargo fmt --check`: clean.

## Issues

- Found and fixed: none in the code around the change.
- Changed behaviour: when the pruned crush fails, the driver now undoes two times (the pruned
  sentence, then the open). `attempts_undone` counts one more undo for such a goal.
- Open: §7 question 1 (the selection for leaf parts).
