# Story 98 — A reduction exports its router, adversary and experiment

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 97 (the module shapes that compile).
**Blocks:** 99.
**ADR:** `docs/adr/0022-a-reduction-is-a-router-an-adversary-and-an-experiment.md` (decisions 1–3, 8).
**Decisions:** owner's grilling session of 2026-11-04/05, Questions 1, 2 and 7. The terms are in
`CONTEXT.md`: **Reduction**, **Mapped package**, **Reduction package**, **Reduction router**,
**Reduction adversary**, **Reduction experiment**.

A **writer** story: a new builder in `src/writers/easycrypt/`, the export report, tests.
Test-first. This story writes the **modules** of a reduction. Story 99 adds the lemmas to the same
file.

---

## 1. Why this story exists

Translation skips every reduction hop (`skip_kind_and_reason`, `src/writers/easycrypt/export.rs:171`:
`"reductions are not translated"`). The proposition lemma (story 100) needs one bound lemma for each
reduction, and a bound lemma needs the modules that this story writes.

## 2. The facts this story uses

- `GameHop::Reduction(Reduction)` (`src/gamehops/reduction.rs`) gives `left()`, `right()` (each a
  `ReductionMapping`) and `assumption_name()`. A `ReductionMapping` gives
  `assumption_game_instance_name()`, `construction_game_instance_name()` and `entries()`; each entry
  pairs `assumption()` with `construction()` package instance names (`src/parser/reduction.rs:1124-1149`).
  **A map can pair the assumption's left game with the hop's right game** (kem-dem's third
  reduction maps `Game_CCA_KEM_Ideal` to the hop's left side).
- The `Reduction` does **not** store the pairing of the reduction packages between the two sides.
  The parser computes it while it checks the hop: `compare_reduction` (`src/parser/reduction.rs:67`)
  walks the call graph of both game instances from the exports, edge by edge, and stops at mapped
  packages. In hello-world the left reduction package is `fwd2` and the right one is `fwd`.
- Each composition's file already has the parts this story needs: clones of each package
  (`clone Pkg_Fwd as Cloned_Pkg_Fwd2.`), import adapters (`build_import_adapter`,
  `src/writers/easycrypt/game.rs:336`), and a router with the abort-flag wrapping
  (`router_module_and_flag`, `game.rs:433`). `game.rs` is 1022 lines.
- `Exp_<C>.run(params)` takes exactly the composition constants that are not width-only
  (`composition_const_needs_arg`, `game.rs:278`). Width-only integers and function constants need no
  argument.
- `Interfaces.ec` shares one interface between compositions with the same exports
  (`(* Iface_SmallComposition/Adv_SmallComposition also cover: MediumComposition *)`).
- Story 97's prototype files and `docs/research/reduction-proof-script.md` show modules that
  compile.

## 3. What to build

A new module `src/writers/easycrypt/reduction.rs` (not more code in `game.rs`). For each
`GameHop::Reduction` of the theorem, it writes `Red_<L>_<R>.ec`, where `<L>` and `<R>` are the hop's
game instance names (ADR 0022, decision 8; the same pattern as `Eq_<L>_<R>.ec`). The file has:

1. **The pairing.** Compute the pairing of the reduction packages between the two sides as
   `compare_reduction` does: from each export of the hop's game, follow the edges of both game
   instances together, and stop at a mapped package. Put the walk in one function that the parser
   and this builder both use, or store its result in `Reduction` when the parser checks the hop.
   Choose the one that keeps both modules within budget.
2. **The reduction router** `Red_<hop> (O : Interfaces.Iface_<Assm>) : Interfaces.Iface_<G>`, built
   with the **left** game instance's reduction packages and instance names. It reuses the import
   adapters and the router wrapping of `game.rs` through a shared function, not a copy:
   - an import that reaches a reduction package calls that package's clone;
   - an import that reaches a mapped package calls `O.d_<name>`, where `<name>` is the assumption
     game's export that reaches the same oracle of the paired assumption package;
   - an export of the hop's game that reaches a mapped package directly is forwarded to `O`;
   - `init(<params>)` sets `abort_flag <- false` and initializes the reduction packages.
3. **The reduction adversary** `B_<hop> (A : Interfaces.Adv_<G>) (O : Interfaces.Iface_<Assm>)`:
   - one `var` for each theorem constant (a boolean or an integer that is not width-only) that a
     reduction package's parameter uses;
   - `proc setup(<those constants>)` stores them;
   - `proc run()` calls `Red_<hop>(O).init(..)` with the stored constants and the literals, then
     returns `A(Red_<hop>(O)).run()`.
4. **The reduction experiment(s).** `RedExp_<hop> (A : Interfaces.Adv_<G>)` with
   `proc run(<B's constants>, <the assumption experiment's arguments>)` that calls
   `B_<hop>(A).setup(..)` and then returns `Exp_<Assm>(B_<hop>(A)).run(..)`. When the two
   assumption games are different compositions, write `RedExp_<hop>_L` and `RedExp_<hop>_R`, each
   with its own `Exp_<Assm>`. Write a reduction experiment for **every** reduction, also when `B_<hop>`
   stores no constants (ADR 0022, decision 3).

The export report:

- A reduction is no longer in `skipped`.
- `ExportedTheorem` gets `reductions: Vec<ReductionReport>` (hop index, left, right, assumption
  name, file name), in `theorem.game_hops` order.
- `domino easycrypt export` prints one `reduction` line for each, next to the `equivalence` lines
  (`crates/domino/src/main.rs:910`).

Docs: replace "Let's skip translating reductions for now!" in `docs/easycrypt-export.md` with a short
section that names the three modules and points to ADR 0022.

Reductions inside a `hybrid` hop stay skipped (ADR 0022, decision 7).

## 4. Tests first

- [ ] A new fixture `testdata/easycrypt/reduction-consts/`: one theorem with a theorem constant
      `b : Bool`, one reduction whose reduction package takes `b` as a parameter, and an assumption
      whose two games are the same composition. Keep it as small as hello-world.
- [ ] Unit test: hello-world exports `Red_big_composition_medium_composition_more_oracles.ec`, with
      `RedExp_<hop>_L` and `RedExp_<hop>_R` (two assumption compositions), and the router uses the
      left instance name `fwd2`.
- [ ] Unit test: kem-dem-cca-ssp exports three `Red_*.ec` files with one `RedExp_<hop>` each; in the
      first, `DEM`'s import `GET` calls `O.d_GET`, and `B_<hop>` has no `var` (`dem_idealization`
      is the literal `false`).
- [ ] Unit test: `reduction-consts` gives `B_<hop>` a `var b : bool`, a `setup(b0 : bool)`, and a
      `RedExp_<hop>.run` whose first argument is `b`.
- [ ] Unit test: the third kem-dem reduction (the map pairs the assumption's ideal game with the
      hop's left side) passes the assumption arguments of the correct side.
- [ ] Unit test: `ExportedTheorem::skipped` has no reduction for these projects, and `reductions`
      lists them in hop order.
- [ ] Compile tests: hello-world, kem-dem-cca-ssp and reduction-consts compile with the
      `Red_*.ec` files (`assert_tree_compiles` gets a loop over `exported.reductions`; it skips
      without `easycrypt`).
- [ ] The existing golden and compile tests stay green: no other file changes.

## 5. Rejected alternatives

All from ADR 0022:

- **One module with a nested router**, **Cryptobox style with no adversary**, **a memory
  hypothesis for the constants**, **theorem constants as abstract `op`s**, **the reduction
  experiment calls the router's `init`**, **literals only**.
- **A theorem-name prefix on the file name.** The theorem's directory already gives the theorem.
- **One router shared by reductions with the same reduction packages** (kem-dem's first and third
  reductions). Each reduction file stays self-contained; the generated text is cheap.

## 6. Acceptance criteria

- [ ] All tests of §4 green, the whole test suite green, `cargo clippy` clean.
- [ ] Complexity: the new module and every changed function in `game.rs` and
      `src/parser/reduction.rs` stay within budget (`crap_scope`).
- [ ] `domino easycrypt export` on `example-projects/4WHS --theorem Simple4WHS` writes
      `Red_Hybrid2_Hybrid3.ec`, and `B_<hop>` stores `b`. Translation only, no proving.
