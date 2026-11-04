# Story 97 — A hand-written reduction proof fixes the script

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** nothing.
**Blocks:** 98, 99.
**ADR:** `docs/adr/0022-a-reduction-is-a-router-an-adversary-and-an-experiment.md` (decisions 1–6).
**Decisions:** owner's grilling session of 2026-11-04/05, Questions 1–5. The terms **Reduction**,
**Mapped package**, **Reduction package**, **Reduction router**, **Reduction adversary**,
**Reduction experiment** and **Bound lemma** are in `CONTEXT.md`.

A **prototype** story. No Rust changes except one compile test. The output is hand-written
EasyCrypt and a short note. Stories 98 and 99 generate what this story writes by hand.

---

## 1. Why this story exists

ADR 0022 decides that translation writes the **whole** proof of a reduction, with no `admit`
(decision 4). We know the shape of the modules. We do not yet know a proof script that EasyCrypt
accepts for every reduction. The difficulty is the abort flags:

- On the left of a reduction equivalence, the hop's game has one router, `Game_<G>`, with one
  `abort_flag`.
- On the right, there are two routers: the reduction router `Red_<hop>` and the assumption game's
  `Game_<Assm>`. A call that reaches a mapped package goes through the extra
  `if (!Game_<Assm>.abort_flag)`.

So `proc; inline *; sim` is not sufficient. Cryptobox closes its steps that only change module names
`by sim` (`ec-cryptobox/Cryptobox.ec`, the `transfer` lemmas with
`(glob PKEY1){1} = (glob PKEY.PKEY1){2}`), but its modules have no abort flags.

If we generate a script before we know that it works, each failure is a translation bug that we
find late. This story finds the script first, on two real reductions.

## 2. The facts this story uses

- `domino easycrypt export --project example-projects/hello-world --out <scratch>` writes the
  tree for theorem `Proof` (11 files). The reduction `big_composition ~
  medium_composition_more_oracles` is skipped (`reductions are not translated`).
  - Assumption `Assumption: medium_composition ~ small_composition`. The two assumption games are
    **different compositions** (`MediumComposition`, `SmallComposition`), so this case needs two
    reduction experiments (ADR 0022, decision 3).
  - Map `medium_composition → big_composition { rand: rand, fwd: fwd }`, so the reduction package on
    the left is `fwd2`. Map `small_composition → medium_composition_more_oracles { rand: rand }`, so
    the reduction package on the right is `fwd`. **The reduction packages have different instance
    names on the two sides.** The parser pairs them by walking the call graph from the exports
    (`compare_reduction`, `src/parser/reduction.rs:67`).
  - The forwarded oracle `UselessOracle` of `fwd2` / `fwd` does not call the assumption game.
- `domino easycrypt export --project example-projects/kem-dem/kem-dem-cca-ssp --out <scratch>`
  writes the tree for theorem `kem_dem_cca_ssp`. The first reduction is
  `Game_MOD_CCA_PKE_Real_KEM_Real_DEM ~ Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM`, with assumption
  `KEM_CCA_Security`.
  - The mapped packages are `Scheme_KEM`, `Key`, `KEM`. The reduction packages are `Scheme_DEM`,
    `DEM`, `MOD_CCA_PKE`. `DEM` imports `Key.GET`: a reduction package calls a mapped package.
  - The two assumption games are the **same composition** `Game_CCA_KEM` (`init(b : bool)`), so one
    reduction experiment is sufficient.
  - `Exp_Game_MOD_CCA_PKE.run(dem_idealization, key_idealization)`. The reduction package `DEM`
    takes `dem_idealization`, which is the literal `false` in this hop.
- Packages are functors over their imports (`module DEM (O : DEM_Imports)`), and compositions
  build import adapters (`module Pkg_Imports_DEM : Pkg_DEM.DEM_Imports = { … }`). A reduction
  package instance that imports a mapped package becomes a functor over the assumption interface:
  `Pkg_Imports_DEM (O : Iface_Game_CCA_KEM)`, `Pkg_Inst_DEM (O : …) = Cloned_Pkg_DEM.DEM(Pkg_Imports_DEM(O))`.
- The equivalence files show the adversary declaration and the restriction form:
  `declare module A <: Interfaces.Adv_<C> { -Comp_<L>.Game_<L>, -Comp_<L>.Pkg_Inst_…, … }.`

## 3. What to build

Hand-write one file for each of the two reductions, next to an exported tree:

- `testdata/easycrypt/reduction-prototype/hello-world/Red_big_composition_medium_composition_more_oracles.ec`
- `testdata/easycrypt/reduction-prototype/kem-dem/Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.ec`

Each file has, in this order (ADR 0022):

1. The clones of the reduction packages, the import adapters (functors over the assumption
   interface where an import reaches a mapped package), and the **reduction router**
   `Red_<hop> (O : Interfaces.Iface_<Assm>) : Interfaces.Iface_<G>`, with `abort_flag` and
   `init(<reduction-package params>)`. A forwarded oracle calls `O.d_<assumption export name>`.
2. The **reduction adversary** `B_<hop> (A : Interfaces.Adv_<G>) (O : Interfaces.Iface_<Assm>)`
   with `setup` and `run`. `run` calls `Red_<hop>(O).init(..)` and then `A(Red_<hop>(O)).run()`.
3. The **reduction experiment(s)**: one `RedExp_<hop>` for kem-dem, `RedExp_<hop>_L` and
   `RedExp_<hop>_R` for hello-world.
4. A section with `declare module A`, the generated invariant as an `op`, the oracle lemmas, the
   two **reduction equivalences** `_L` and `_R`, and the **bound lemma**:
   ```
   lemma <hop>_bound &m :
     `|Pr[Exp_<GL>(A).run(..) @ &m : res] - Pr[Exp_<GR>(A).run(..) @ &m : res]|
   = `|Pr[RedExp_<hop>(A).run(..L) @ &m : res] - Pr[RedExp_<hop>(A).run(..R) @ &m : res]|.
   ```

**The theorem-constant case.** No example project has a small reduction where a reduction package
takes a theorem constant (4WHS `Hybrid2` does, but it is too large for a prototype). So in the
kem-dem file, treat `dem_idealization` **as if it were a theorem constant**: `B_<hop>` stores it
with `setup`, `RedExp_<hop>.run(dem : bool, b : bool)` takes it, and the two reduction
equivalences and the bound lemma quantify `(dem : bool)`. This is still true for every `dem`, and it
tests the `setup` path of ADR 0022 decision 2. The generated version (story 98) hard-codes literals.

**The proof script.** Find a script that has the same shape for every oracle and every reduction, so
that story 99 can generate it from the map alone. A suggested start:

- One small `equiv` for each mapped oracle that a reduction package calls:
  `Comp_<G>.Pkg_Inst_M.d_o ~ Comp_<Assm>.Game_<Assm>.d_o'`, with the assumption flag false
  before the call (`rcondt{2}`), equal package states, and
  `Game_<Assm>.abort_flag{2} = (res{2} = None)` after.
- One oracle lemma for each exported oracle, `Game_<G>.d_o ~ Red_<hop>(Game_<Assm>).d_o`, under the
  invariant, by `proc; inline <the routers>; if; [sim with the mapped-oracle equivs | auto]`.
- Each reduction equivalence: `byequiv => //; proc; inline <Exp, RedExp, B.setup, B.run, inits>;
  call (: <invariant>); auto`.
- The bound lemma: `by rewrite (<hop>_equiv_L &m ..) (<hop>_equiv_R &m ..).`

Change this script as EasyCrypt requires. The result is what counts, not the start.

Write `docs/research/reduction-proof-script.md`: the final script, with each tactic and the reason
for it, the invariant's conjuncts, and each place where the two prototypes needed different tactics
(if there are such places, say what in the map decides between them).

## 4. Tests first

- [ ] A compile test `reduction_prototypes_compile` in `src/writers/easycrypt/export.rs` (or a
      sibling test module). It exports hello-world and kem-dem-cca-ssp, writes each tree to a
      scratch directory, copies the prototype file in, and compiles the tree and then the
      prototype in dependency order. It uses the same compile helper as `assert_tree_compiles`
      (`test_support::assert_compiles`), and it skips without `easycrypt`.
- [ ] The prototype files have no `admit` (`grep -c admit` is 0). The equivalence files of the
      tree may keep their admits: the reduction file does not require them.

## 5. Rejected alternatives

- **Generate the script first and fix it on failure** (start with story 99). Each failure is then a
  translation bug in generated code, which is harder to read than a hand-written file.
- **Prototype on 4WHS** (`Hybrid2 → Hybrid3`, the real theorem-constant case). Too large: the
  memory rule "small capped fixtures only" applies, and the composition is much bigger than the
  question needs.
- **A new fixture for the theorem-constant case.** Treating `dem_idealization` as a constant in the
  kem-dem prototype tests the same mechanism with no new Domino project.

## 6. Acceptance criteria

- [ ] The two prototype files compile against their exported trees with no `admit`.
- [ ] `docs/research/reduction-proof-script.md` gives a script that depends only on: the map, the
      reduction-package pairing, the exported oracles of the hop's game, and the assumption exports
      that the reduction packages call.
- [ ] The test of §4 is green, the whole test suite is green, `cargo clippy` clean.
- [ ] The owner reads the script note and agrees that story 99 can generate it.
