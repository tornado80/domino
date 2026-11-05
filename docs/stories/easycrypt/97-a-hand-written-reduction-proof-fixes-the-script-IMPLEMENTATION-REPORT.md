# Story 97 — Implementation report: a hand-written reduction proof fixes the script

Prototype story. No Rust change except one test. Branch `amir/easycrypt-export`, implementation commit `6b8efa1a`. ADR 0022.

## What was built

### Two hand-written reduction files (no `admit`)

- `testdata/easycrypt/reduction-prototype/hello-world/Red_big_composition_medium_composition_more_oracles.ec`
  (`big_composition ~ medium_composition_more_oracles`, assumption `medium_composition ~
  small_composition`: two different compositions, so `RedExp_<hop>_L` and `_R`).
- `testdata/easycrypt/reduction-prototype/kem-dem/Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.ec`
  (assumption `KEM_CCA_Security`, one `RedExp_<hop>`; `dem_idealization` treated as a theorem
  constant: `B_<hop>.setup` stores it, the experiment and the lemmas take `dem : bool`).

Each file has, in order: the router (clones of the reduction packages, import adapters as
functors over the assumption interface where an import reaches a mapped package,
`Red_<hop>(O)` with `abort_flag` and `init`), the adversary `B_<hop>(A)(O)` with `setup`/`run`,
the experiment(s), the invariant `op`, and a section with `declare module A`, one oracle lemma
per exported oracle (per side in hello-world), the two reduction equivalences and the bound
lemma (equality).

### The note `docs/research/reduction-proof-script.md`

The final script with each tactic and its reason, the invariant's conjuncts (C1–C4), why the
suggested `sim` script cannot work, the differences between the two prototypes and what in the
map decides each one, and the limits.

### Test

`reduction_prototypes_compile` in `src/writers/easycrypt/export.rs`: for each prototype, assert
it has no `admit`, export the theorem, write the tree to a scratch directory, copy the
prototype in, and compile `Types`, `Interfaces`, `Pkg_*`, `Comp_*` and then the prototype with
`test_support::assert_compiles` (skips without `easycrypt`). The equivalence files are not
compiled: the reduction file does not require them.

## Findings that change the plan for stories 98 and 99

1. **The suggested script does not work, and no `sim`-based script can.** On the right each
   mapped call sits under `if (!Game_<Assm>.abort_flag)`. A context-free `sim` specification
   for (left mapped call, right guarded call) would need `!abort_flag` before and after, and a
   mapped call that returns `None` sets the flag. Every ghost or extra guard needs a partner on
   the left, whose code is fixed. Details in the note, section 5.
2. **What works: one oracle-lemma proof text for every oracle of every reduction.** Inline
   everything except the mapped packages (excluded by both `Pkg_Inst_<m>` and
   `Cloned_Pkg_<m>.<P>`), then a forward lockstep walk in a `do ?` loop: `sp`; two-sided `if`;
   `rcondt{2} 1` for the assumption game's guard; `rcondf{2} 1`/`if{2}` for its flag update;
   and for a mapped call or a sampling at the head, `alias` both results to `ec_fwd` and
   `seq 1 1 : (#pre /\ ={ec_fwd..})` closed by `call (: MEQ); sim`. EasyCrypt has no forward
   `call`/`rnd` in pRHL, and `alias` gives the result a name the script knows. Only the
   exclusion list and `MEQ` (the mapped packages' state equalities) change, both from the map.
3. **`setup` needs a functor argument.** `B_<hop>(A).setup(..)` is rejected
   (`unknown procedure`); the experiment calls `B_<hop>(A, Comp_<Assm>.Game_<Assm>).setup(..)`.
   `setup` does not use `O`, so decision 2 of the ADR still holds.
4. **`call (: INV)` subgoals of a multi-argument oracle** are stated with `m0{1} = m0{2} /\ ..`,
   so the equivalences use `conseq <lemma> => /#`, not `apply`.
5. **Use `glob` of the unapplied clone** (`glob Comp_G.Cloned_Pkg_KEM.KEM`) in the invariant:
   the `glob` of `Pkg_Inst_<..>` contains its imports' states too.
6. **The alias ladder:** `alias` names results `ec_fwd`, `ec_fwd0`, `ec_fwd1`, ...; the script
   tries the newest name first and needs one rung per mapped call or sampling on one path
   (4 rungs in the prototypes; kem-dem needs 2).

Not exercised: a sampling in a reduction package (none in the prototypes), and `while` loops
in reduction code (the walk cannot pass them; story 99 should check for them).

## Deviations from the story and the ADR

- The story's suggested proof is replaced (finding 1–2); the story allowed this.
- `RedExp` names the assumption game in the `setup` call (finding 3).
- The invariant `op` is declared just before the section, not inside it (it does not depend
  on `A`).
- The router of hello-world uses the left instance name (`Cloned_Pkg_Fwd2`) for the pair
  `fwd2`/`fwd`; the note makes that the rule.

## Tests run

All under `systemd-run --user --scope -p MemoryMax=6G timeout 1800`, EasyCrypt r2026.09 on
`PATH`, no proving job running (`ps aux | grep domino-ec`).

| Command | Result |
|---|---|
| `cargo test reduction_prototypes_compile -- --test-threads=1` | ok (34 s; it compiles, it does not skip) |
| `cargo test writers::easycrypt -- --skip 4whs --skip 4WHS --test-threads=1` | ok, 319 passed, 0 failed (303 s) |
| `cargo clippy --workspace --all-targets` | no warnings |
| `rustfmt --check src/writers/easycrypt/export.rs` | ok |

The 4WHS tests are skipped by the owner's rule (no big projects); the unfiltered suite was not
run (same rule). The prototypes were also compiled by hand with `easycrypt compile -no-eco`
against freshly exported trees, and a deliberately wrong lemma in a copy was rejected, so the
checks are real.
