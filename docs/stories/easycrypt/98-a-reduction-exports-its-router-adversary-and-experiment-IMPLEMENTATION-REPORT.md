# Story 98 — Implementation report: a reduction exports its router, adversary and experiment

Branch `amir/easycrypt-export`, implementation commit `46423dfa`. ADR 0022 (decisions 1–3, 8).

## What was built

### `src/writers/easycrypt/reduction.rs` (new)

`compute_reduction_files(theorem, interfaces)` writes one `Red_<L>_<R>.ec` for each top-level
`GameHop::Reduction`, in `theorem.game_hops` order. Each file has:

- **The router** `Red_<hop> (O : Interfaces.Iface_<Assm>) : Interfaces.Iface_<G>`, built from
  the left game's reduction packages with their instance names: `clone Pkg_<V> as
  Cloned_Pkg_<m>`, an import adapter `Pkg_Imports_<m> (O : ...)` for each reduction package with
  imports, and `Pkg_Inst_<m> (O : ...) = Cloned_Pkg_<m>.<V>(Pkg_Imports_<m>(O))` (no `O` for a
  package without imports). An import or an export that reaches a mapped package calls
  `O.d_<e>`, where `e` is the assumption game's export that reaches the same oracle of the
  partner package. `init` takes the non-width composition constants that a reduction package
  reads, sets `abort_flag <- false`, and initializes the reduction packages.
- **The adversary** `B_<hop> (A : Adv_<G>) (O : Iface_<Assm>)`: one `var` for each theorem
  constant that a router `init` argument resolves to; `setup(<c>0 ...)` stores them; `run`
  calls `Red_<hop>(O).init(..)` with these vars and literals, then `A(Red_<hop>(O)).run()`.
- **The experiment(s)** `RedExp_<hop>` (one, when the two assumption games are the same
  composition) or `RedExp_<hop>_L`/`_R`. `run(<B's constants>, <Exp_<Assm>.run args>)` calls
  `B_<hop>(A, Comp_<Assm>.Game_<Assm>).setup(..)` and returns
  `Comp_<Assm>.Exp_<Assm>(B_<hop>(A)).run(..)`. A clashing argument name gets `_a`.
- A header that names, for each side, the assumption game, the experiment and the assumption
  argument values, and the pairing of the reduction packages.

`ReductionFile` also carries `package_pairs` and `sides: [ReductionSide; 2]` (assumption game,
experiment name, assumption argument values) for story 99.

### Shared code in `game.rs` (no output change)

`import_adapter` (adapter with functor parameters and a call target per edge) and
`guarded_export_proc` (the abort-flag wrapping) are extracted; the game file and the reduction
router both use them. `EcItem::ModuleAlias` gets `params`.

### The pairing

Stored in `Reduction` (`package_pairs()`), collected by `compare_reduction` while the parser
checks the hop. hello-world: `[("fwd2", "fwd")]`.

### Export report and CLI

A reduction is no longer in `skipped`. `ExportedTheorem::reductions: Vec<ReductionReport>`
(proofstep, left, right, assumption name, file). `domino easycrypt export` prints
`reduction   Red_<L>_<R>.ec (assumption <A>)` after the `equivalence` lines.
`docs/easycrypt-export.md` "Translating reductions" now describes the modules.

### Fixture

`testdata/easycrypt/reduction-consts/` (theorem `RedConsts`): theorem constant `b : Bool`;
reduction package `Mod(flip: b)` over mapped `Key(ideal)`; the assumption's two games are the
same composition `KeyGame`.

## Tests

New, all green:

- `reduction::tests::hello_world_reduction_has_two_experiments_and_uses_the_left_names`
- `reduction::tests::kem_dem_exports_three_reductions_with_one_experiment_each` (`O.d_GET`, no
  `var`, `init(false)`)
- `reduction::tests::the_third_kem_dem_reduction_takes_the_assumption_arguments_of_its_own_sides`
- `reduction::tests::reduction_consts_adversary_stores_the_theorem_constant`
- `export::tests::reductions_are_reported_in_hop_order_and_not_skipped`
- `export::tests::reduction_consts_full_tree_compiles`; `assert_tree_compiles` now compiles every
  `Red_*.ec`, so `hello_world_full_tree_compiles` and
  `kem_dem_cca_ssp_full_tree_compiles_in_dependency_order` compile them too (live, green).

Commands run (memory cap 6G, `DOMINO_EASYCRYPT` set, no proving job running):

- `cargo test --lib writers::easycrypt -- --skip 4whs --skip 4WHS --test-threads=1`: 325 passed.
- `cargo test --lib reduction -- --skip 4whs --skip 4WHS --test-threads=1`: 17 passed, 1 ignored.
- `cargo test -p domino easycrypt -- --skip 4whs --skip 4WHS --test-threads=1`: all passed.
- `cargo clippy --workspace --all-targets`: clean.

Written, not run (4WHS, per the owner's rule):
`simple_4whs_reports_the_reduction_hop_and_the_composition_names` now expects `skipped` empty,
`Red_Hybrid2_Hybrid3.ec`, and `proc setup(b0 : bool)` (acceptance criterion 3). Run with
`cargo test --lib simple_4whs_reports_the_reduction_hop -- --test-threads=1`. The 4WHS
full-tree compile tests now also compile `Red_Hybrid2_Hybrid3.ec`.

Not done: the CRAP gate (`crap_scope`) was not run. TDD note: the unit tests were written with
the module in one pass and passed on the first run; there was no separate red step.

## Deviations

- As in story 97: the experiment calls `B_<hop>(A, Comp_<Assm>.Game_<Assm>).setup(..)`, not
  `B_<hop>(A).setup(..)`.
- Literals are hard-coded (kem-dem `dem_idealization` is `false` in `init`), as story 98 says;
  the story-97 prototype stored it.
- Clones use `Pkg_<V>`, never `PkgInv_<V>`.
- Requires list `Comp_` of both hop games and both assumption games (story 99 needs them).

## What story 99 must know

- Use `ReductionFile::sides[i]` for the lemma of side `i`: `experiment` is the `RedExp` to put
  on the right, `assumption_args` are the values for `RedExp.run`'s assumption arguments (after
  B's constants). With one experiment both sides use the same module with different values.
- `RedExp.run`'s first arguments are B's stored constants, named as the theorem constants.
- The router's module names are `Red_<hop>`, `Pkg_Inst_<m>` and `Cloned_Pkg_<m>.<V>` of the
  left instance names; use `package_pairs` to pair right-side packages with them.
- The router's state is `Red_<hop>.abort_flag` and `glob Cloned_Pkg_<m>.<V>`.

## What story 100 must know

`ExportedTheorem::reductions` lists the reductions with their `proofstep`, in hop order.
Reductions inside hybrid hops are not exported.
