# The proof script of a reduction (story 97)

**Status:** found by hand on two reductions, both compile with EasyCrypt r2026.09 with no
`admit`:

- `testdata/easycrypt/reduction-prototype/hello-world/Red_big_composition_medium_composition_more_oracles.ec`
- `testdata/easycrypt/reduction-prototype/kem-dem/Red_Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM.ec`

The test `reduction_prototypes_compile` (`src/writers/easycrypt/export.rs`) exports each tree,
copies the prototype in, and compiles `Types`, `Interfaces`, `Pkg_*`, `Comp_*` and then the
prototype. This note is the input of stories 98 (modules) and 99 (lemmas and proofs).

## 1. Summary

- The module shape of ADR 0022 works: router, adversary, experiment(s), two reduction
  equivalences, a bound lemma that states equality. One adjustment: `setup` (section 3.2).
- **The suggested script does not work.** `proc; inline; sim` with small equivs for the mapped
  oracles cannot be made to work, for any invariant (section 5). The reason is the extra
  `if (!Game_<Assm>.abort_flag)` around each mapped call on the right.
- **What works** is one oracle-lemma proof that is **the same text for every oracle of every
  reduction**. Only two lists in it change, and both come from the map: the mapped package
  instances (an `inline` exclusion list) and the equality of their states. The proof inlines
  everything except the mapped packages and then walks the two programs forward in lockstep
  with a `do ?` loop (section 4.3).
- The two prototypes use the same oracle-lemma text. They differ only where the map or the
  assumption differ (section 6).

## 2. Inputs (all from the map and the exports)

Story 99 needs only:

1. The hop's game instance on each side (`Comp_<GL>.Game_<GL>`, `Comp_<GR>.Game_<GR>`), and
   their arguments (`Exp_<G>.run(..)`).
2. The assumption game on each side (`Comp_<AL>.Game_<AL>`, `Comp_<AR>.Game_<AR>`) and their
   arguments. Same composition on both sides or not (section 6).
3. The map of each side: mapped instance of the hop's game ↔ instance of the assumption game.
4. The reduction-package pairing (left instance ↔ right instance, from `compare_reduction`).
   The router uses the **left** instance names.
5. The exported oracles of the hop's game (the router's interface `Iface_<G>`).
6. The assumption exports that the reduction packages call (they become `O.d_<export>` in the
   router's import adapters).
7. The theorem constants that the reduction packages take (`setup`'s parameters). In the
   prototype only kem-dem has one (`dem_idealization`, treated as a constant, story 97 §3).

The proof does **not** need the code of any package, the order of calls, or which oracle
calls which mapped oracle.

## 3. The modules (story 98)

### 3.1 Router

As ADR 0022 says. A clone of each reduction package (`clone Pkg_<P> as Cloned_Pkg_<Inst>`),
the composition's import adapters, but as **functors over the assumption interface** when an
import reaches a mapped package (`Pkg_Imports_<Inst> (O : Interfaces.Iface_<Assm>)`), and
`Pkg_Inst_<Inst> (O : ..) = Cloned_Pkg_<Inst>.<P>(Pkg_Imports_<Inst>(O))`. A forwarded import
is `r <@ O.d_<export>(..); return r;`, the same shape as a composition adapter. An adapter to
another reduction package calls `Pkg_Inst_<Other>(O).d_<oracle>`. The router
`Red_<hop> (O : Interfaces.Iface_<Assm>) : Interfaces.Iface_<G>` has `var abort_flag`,
`init(<reduction-package params>)` and the same abort wrapping as `Game_<G>`.

In hello-world the router clones `Fwd` as `Cloned_Pkg_Fwd2` (left name `fwd2`), and the right
partner `fwd` maps to it. The router is the same for both sides.

### 3.2 Adversary: `setup` needs a functor argument

`B_<hop> (A : Interfaces.Adv_<G>) (O : Interfaces.Iface_<Assm>)` with `var <const>` for each
constant, `proc setup(<const>_ : ..)` and `proc run()` (`Red_<hop>(O).init(<consts>);
b' <@ A(Red_<hop>(O)).run()`).

EasyCrypt does not accept `B_<hop>(A).setup(..)`: a procedure of a functor needs all its
arguments (`unknown procedure: B_<hop>.setup`). The experiment calls
`B_<hop>(A, Comp_<Assm>.Game_<Assm>).setup(..)`. `setup` does not use `O`, and the state
(`B_<hop>.<const>`) is the same for each `O`, so this is still decision 2 of the ADR. The
assumption game named here is the one that the same experiment runs. With no constants,
`setup` is `proc setup() : unit = { }` and is still called (decision 3: every reduction has an
experiment of the same shape).

### 3.3 Experiment(s)

```
module RedExp_<hop>[_L|_R] (A : Interfaces.Adv_<G>) = {
  proc run(<consts>, <assumption game args>) : bool = {
    var b' : bool;
    B_<hop>(A, Comp_<Assm>.Game_<Assm>).setup(<consts>);
    b' <@ Comp_<Assm>.Exp_<Assm>(B_<hop>(A)).run(<assumption game args>);
    return b';
  }
}.
```

One experiment when the two assumption games are the same composition (kem-dem:
`RedExp_<hop>.run(dem_idealization, b)`), else `_L` and `_R` (hello-world).

## 4. The lemmas and their proofs (story 99)

### 4.1 The invariant

An `op` for each reduction equivalence side (one op when the two sides use the same
compositions, as in kem-dem; `_L` and `_R` otherwise, as in hello-world). Its arguments are
values, so the lemma statements apply it to `(glob ..){1}`/`{2}` terms:

```
op inv_<hop>[_L|_R]
  (game_abort red_abort assm_abort : bool)
  (<const>_l <const>_r : bool) ...                         (* one pair per constant *)
  (<p>_l : glob Comp_<G>.Cloned_Pkg_<Inst>.<P>) (<p>_r : glob <right module>) ...
  : bool =
     game_abort = red_abort                                 (* C1 *)
  /\ (assm_abort => red_abort)                              (* C2 *)
  /\ <const>_l = <const>_r                                  (* C3, one per constant *)
  /\ <p>_l = <p>_r ... .                                    (* C4, one per paired package *)
```

Applied as `inv (Game_<G>.abort_flag{1}) (Red_<hop>.abort_flag{2}) (Game_<Assm>.abort_flag{2})
(Comp_<G>.Cloned_Pkg_<Inst>.<P>.<const>{1}) (B_<hop>.<const>{2}) (glob ..){1} (glob ..){2} ...`.

- **C1** `Game_<G>.abort_flag{1} = Red_<hop>.abort_flag{2}`: both routers abort together.
- **C2** `Game_<Assm>.abort_flag{2} => Red_<hop>.abort_flag{2}`: the assumption game never
  aborts while the router is still serving. This is what makes the guard
  `if (!Game_<Assm>.abort_flag)` true at every mapped call (it holds at an oracle's start, and
  the walk carries the facts from there).
- **C3** for each constant: the value the game's package stored at `init` equals the value
  `B_<hop>` stored at `setup` (`Comp_<G>.Cloned_Pkg_DEM.DEM.b{1} = B_<hop>.dem_idealization{2}`).
  Not used by the oracle proofs (the packages' own copies are in C4), but it is the ADR's
  conjunct and costs nothing.
- **C4** for each package pair: equal states. Pairs are (a) each **reduction package** of the
  game with its router clone (`Comp_<G>.Cloned_Pkg_<Inst>.<P>` ↔ `Cloned_Pkg_<LeftInst>.<P>`)
  and (b) each **mapped package** of the game with its assumption-game instance
  (`Comp_<G>.Cloned_Pkg_<Inst>.<P>` ↔ `Comp_<Assm>.Cloned_Pkg_<Inst'>.<P>`). Packages with no
  state (`Scheme_KEM`, `Scheme_DEM`) can be left out.

Use `glob` of the **unapplied clone module** (`glob Comp_G.Cloned_Pkg_KEM.KEM`), not of
`Pkg_Inst_KEM`: the `glob` of a functor application also contains the states of its
arguments (`glob Pkg_Inst_Fwd2` is `int * int` in hello-world, `glob Cloned_Pkg_Fwd2.Fwd` is
`int`).

`MEQ` below is the conjunction of the C4 equalities of the **mapped** packages only, written
directly as `(glob X){1} = (glob Y){2} /\ ..` (not through the op, because `sim` reads it).

### 4.2 The section and the adversary

```
section.
declare module A <: Interfaces.Adv_<G> {
  -<every Game_ and Cloned_Pkg_ module of Comp_<GL>, Comp_<GR>, Comp_<AL>, Comp_<AR>>,
  -Red_<hop>, -B_<hop>, -<every Cloned_Pkg_ of the router> }.
```

### 4.3 One oracle lemma for each exported oracle (and each side, unless shared)

```
local equiv <hop>[_L|_R]_d_<o> :
  Comp_<G>.Game_<G>.d_<o> ~ Red_<hop>(Comp_<Assm>.Game_<Assm>).d_<o> :
  ={arg} /\ <INV> ==> ={res} /\ <INV>.
proof.
proc; inline *
  -Comp_<G>.Pkg_Inst_<m> -Comp_<G>.Cloned_Pkg_<m>.<P>             (* each mapped instance m *)
  -Comp_<Assm>.Pkg_Inst_<m'> -Comp_<Assm>.Cloned_Pkg_<m'>.<P>.      (* each partner m' *)
do ? (sp; (
     (if; first by move=> /#)
  || (rcondt{2} 1; first by auto => /#)
  || (rcondf{2} 1; first by auto => /#)
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd2});
      first by (call (: <MEQ>); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd1});
      first by (call (: <MEQ>); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd0});
      first by (call (: <MEQ>); [by sim | by auto => /#]) || (auto => /#))
  || (alias{1} 1 with ec_fwd; alias{2} 1 with ec_fwd;
      seq 1 1 : (#pre /\ ={ec_fwd});
      first by (call (: <MEQ>); [by sim | by auto => /#]) || (auto => /#))
  || if{2})); auto => /#.
qed.
```

Every oracle lemma of both prototypes (2 + 2 in hello-world, 3 in kem-dem) has exactly this
text, with only `<G>`, `<Assm>`, `<o>`, `<INV>`, `<MEQ>` and the exclusion list filled in.

**Tactic by tactic.**

- `proc; inline * -<mapped>`: inline the routers, the reduction packages, all import adapters
  and the assumption game's oracles (`Game_<Assm>.d_<x>`, so its guard and its abort-flag
  update become visible code on the right), but keep each **mapped package call atomic** on
  both sides. After this the two programs are the same reduction code under other names; the
  right one has in addition, around each mapped call,
  `if (!Game_<Assm>.abort_flag) { r <@ M.d_x(..); if (r = None) Game_<Assm>.abort_flag <- true; }`.
  Each mapped instance must be excluded by **both** names: `Pkg_Inst_<m>` (how a composition's
  `Game_`/adapter calls it) and `Cloned_Pkg_<m>.<P>` (how a functor argument calls it, e.g.
  `Fwd2(Fwd(Rand))` in hello-world calls `Cloned_Pkg_Fwd.Fwd(..)`). With one of the two names
  missing, one side inlines the mapped package and the walk stops.
- `do ? (sp; ( alt || alt || ... ))`: walk both programs forward in lockstep. `sp` eats the
  leading assignments into the precondition (the facts the later steps need: equal locals,
  path conditions, the guard's flag). Then the first alternative that applies:
  - `if; first by move=> /#`: both programs start with the same `if` (the reduction code's
    own `if`s and the routers' `if (!abort_flag)`). The first subgoal (the conditions are
    equal) needs `smt` because the facts are inside the op; if it fails the alternative is
    discarded, so a left `if` is never paired with the right guard.
  - `rcondt{2} 1; first by auto => /#`: the right program starts with the assumption game's
    guard `if (!Game_<Assm>.abort_flag)`. Its condition is true: from C1, C2 and the router's
    `!abort_flag` at the first mapped call, and from the path condition `r <> None` plus the
    `sp` fact on the flag at later calls. This is the step that `sim` cannot do (section 5).
  - `rcondf{2} 1; first by auto => /#`: a right-only `if` whose condition is false
    (`if (r = None) abort_flag <- true` after a call that returned `Some`, when the facts
    say so).
  - The `alias`/`seq` alternatives: both programs start with a **mapped call** (or a
    sampling). EasyCrypt has no forward `call` or `rnd` in pRHL (`ecall ->>` is refused on
    equiv goals: `unsupported direction for ecall on an equiv. goal`), and `seq 1 1 : (#pre
    /\ ={x})` needs the name of the result variable, which `inline` renames differently on the
    two sides (right: the assumption game's `ec_result<N>`, left: the adapter's `r<N>`).
    `alias{i} 1 with ec_fwd` renames the result of the first instruction to a name we choose
    on each side, so `seq 1 1 : (#pre /\ ={ec_fwd})` splits off the call. `#pre` stays true
    across the call because the call only writes the mapped packages' states, and the
    precondition talks about them only through `MEQ`-equal pairs (the guard's flag is written
    by the next, visible instruction, not by the call). The first subgoal is closed by
    `call (: MEQ)` with `sim` for the call itself (same package code in two clones, as in
    Cryptobox's `transfer` lemmas) and `auto => /#` for the rest; for a sampling,
    `auto => /#`.
    `alias` picks a fresh name each time (`ec_fwd`, `ec_fwd0`, `ec_fwd1`, ..., see
    `EcMemory.bindall_fresh`), so the alternatives try the newest name first: `ec_fwd2`, then
    `ec_fwd1`, `ec_fwd0`, `ec_fwd`. A name that does not exist yet is a typing error, the
    alternative fails, and the next one is tried; the first one that type-checks is the alias
    just made. **The ladder must have one rung per mapped call or sampling on one path of an
    oracle** (4 rungs cover 4; kem-dem needs 2). Story 99 can emit a fixed, generous number of
    rungs (a failing rung costs one type error) or count the calls of the longest path.
  - `if{2}`: any other right-only `if` (the flag update when the result may be `None`). Both
    branches go on.
- `do ?` and not `do !`: `do !` requires progress on every subgoal it starts on and fails at
  the end of a branch (`invalid first instruction`). `do ?` stops cleanly.
- `auto => /#`: each leaf is straight-line code (the routers' last `if (ec_result = None)
  abort_flag <- true` has been split or is absorbed by `wp`); `smt` proves `={res}` and the
  op from the collected facts. The leaves where a mapped call returned `None` are where C2 is
  re-established: the reduction code's result is then `None`, so the router sets its flag.

### 4.4 The two reduction equivalences

```
lemma <hop>_equiv_L &m <consts> :
  Pr[Comp_<GL>.Exp_<GL>(A).run(<args L>) @ &m : res]
  = Pr[RedExp_<hop>[_L](A).run(<consts>, <assumption args L>) @ &m : res].
proof.
byequiv (: ={glob A} /\ arg{1} = (<args L>) /\ arg{2} = (<consts>, <assumption args L>)
           ==> ={res}) => //.
proc; inline *; wp.
call (: <INV>).
+ by conseq <hop>[_L]_d_<o1> => /#.
+ by conseq <hop>[_L]_d_<o2> => /#.
...
by auto => /#.
qed.
```

and the same for `_R`. Without arguments the precondition is `={glob A}` alone
(hello-world). `inline *` inlines the inits, `setup`, `Exp_<Assm>.run` and `B_<hop>.run`, but
not the abstract `A`. `call (: INV)` makes one subgoal for each oracle of `Iface_<G>`, in the
interface's order, then the init goal. **Use `conseq .. => /#`, not `apply`**: for an oracle
with several arguments EasyCrypt states the subgoal with `m0{1} = m0{2} /\ m1{1} = m1{2}`, not
`={arg}`, and `apply` fails on it. The last `auto => /#` checks the invariant after the inits
(both sides set every state; the assumption game's `init` gets the same argument as the
game's mapped packages, and `setup` stores the constant the game's package gets).

### 4.5 The bound lemma

```
lemma <hop>_bound &m <consts> :
  `|Pr[Comp_<GL>.Exp_<GL>(A).run(<args L>) @ &m : res]
    - Pr[Comp_<GR>.Exp_<GR>(A).run(<args R>) @ &m : res]|
  = `|Pr[RedExp_<hop>[_L](A).run(<consts>, <assumption args L>) @ &m : res]
      - Pr[RedExp_<hop>[_R](A).run(<consts>, <assumption args R>) @ &m : res]|.
proof. by rewrite (<hop>_equiv_L &m <consts>) (<hop>_equiv_R &m <consts>). qed.
end section.
```

## 5. Why `sim` cannot do it (do not try again)

On the left a reduction package calls a mapped package directly. On the right the same call
goes through `if (!Game_<Assm>.abort_flag) { .. }`. Every way to use `sim` needs a
specification for the pair (left mapped call, right guarded call) of the form
`={arg} /\ E /\ I ==> ={res} /\ E /\ I` (E: equalities, I: one invariant for all pairs), and it
must hold **without context**:

- To pass the guard, the precondition must imply `!Game_<Assm>.abort_flag{2}`.
- The postcondition must imply it again (it is the same I), but a mapped call that returns
  `None` sets the flag.
- Any other variable that could carry the information (a ghost in the router's adapter, the
  router's own flag set early, a guard on such a variable) needs a matching variable on the
  left, and the left game's code is fixed. Moving the guard to the left by a transitivity step
  (a "left assumption game" over the left's own mapped instances) moves the same problem to
  that step.

So some per-call-site reasoning is necessary: "after a mapped call returned `None`, the
reduction code calls no other mapped oracle in this oracle call" (Domino's `invoke` puts the
continuation under `if (!(r = None))` or behind `ec_done`). The forward walk gets it from the
path conditions, which is why the walk works with no knowledge of the code. `sim` also refuses
an invariant that mentions a variable the walked code writes (`abort_flag`).

## 6. Where the two prototypes differ, and what decides

The oracle-lemma script is identical. The differences:

| What | hello-world | kem-dem | Decided by |
|---|---|---|---|
| Reduction experiments | `RedExp_<hop>_L`, `_R` | one `RedExp_<hop>` | the assumption's two games are the same composition or not |
| Invariant ops / oracle lemmas | two sets (`_L`, `_R`) | one set, used by both equivalences | same: the left and right equivalences have the same compositions (game and assumption game) on both sides |
| `setup` | `setup()` with empty body | `setup(dem_idealization_)`, `var dem_idealization` | the theorem constants the reduction packages take |
| C3 conjunct | none | `DEM.b{1} = B.dem_idealization{2}` | same |
| Experiment arguments | none | `(dem_idealization, b)` | reduction-package constants, then the assumption game's own args |
| Router names | `Cloned_Pkg_Fwd2` for left `fwd2` / right `fwd` | the same names on both sides | the pairing; the router always uses the left names |
| `MEQ`, exclusion list | `fwd`, `rand` (L); `rand` (R) | `Key`, `KEM`, `Scheme_KEM` | the map of each side |
| Import adapters over `O` | `fwd2.UsefulOracle → O` | `DEM.GET`, `MOD_CCA_PKE.{DECAPS,ENCAPS,KEMGEN} → O` | which imports of reduction packages reach a mapped instance |

## 7. Limits and open points

- **Not exercised:** a sampling in a reduction package before a mapped call (no reduction
  package of the prototypes samples). The ladder's `|| (auto => /#)` closer is meant for it,
  but it is untested.
- **Loops:** the walk has no case for `while` (Domino `for` loops). A `while` in the inlined
  reduction code stops the walk, and the final `auto` cannot pass it. Story 99 should check
  the reduction packages' translated code (4WHS included) for loops before it relies on the
  script, and report such a reduction as not translated rather than emit a failing proof.
- **Ladder depth:** one rung for each mapped call or sampling on one path (section 4.3).
- **Proof time:** kem-dem's three oracle lemmas take about 10 s in total, hello-world's about
  1 s. The walk splits every `if`, so the number of leaves grows with the branching of the
  reduction code; each leaf is one `smt` call.
- **`if` side goals by `smt`:** the condition equalities go through the op; `smt` unfolds it.
  If this gets slow on a large invariant, `rewrite /inv_..` before the walk is the first thing
  to try.
- The hand-written files keep EasyCrypt's own warnings about uninitialized locals of the
  cloned packages (`DEM.d_ENC -> [c_]`); they come from the packages, not the reduction file.
