# Story 99 — A reduction exports its equivalences and its bound lemma, with the whole proof

**Epic:** EasyCrypt export: reductions and propositions — `docs/stories/easycrypt/epic-reductions-and-propositions.md` (part of the EasyCrypt Export epic, `00-overview.md`).
**Branch:** `amir/easycrypt-export`
**Depends on:** 97 (the proof script), 98 (the modules).
**Blocks:** 100.
**ADR:** `docs/adr/0022-a-reduction-is-a-router-an-adversary-and-an-experiment.md` (decisions 4–6).
**Decisions:** owner's grilling session of 2026-11-04/05, Questions 3, 4 and 5. The term
**Bound lemma** is in `CONTEXT.md`.

A **writer** story: `src/writers/easycrypt/reduction.rs` and tests. Test-first.

---

## 1. Why this story exists

After story 98, `Red_<L>_<R>.ec` has the modules but no lemma. The proposition lemma (story 100)
needs, for each reduction, the bound lemma: the original adversary's advantage between the hop's two
game instances **equals** the reduction adversary's advantage between the two assumption games.

## 2. The facts this story uses

- `docs/research/reduction-proof-script.md` (story 97): the script, the invariant's conjuncts, and
  what in the map decides between tactics (if anything).
- The prototype files under `testdata/easycrypt/reduction-prototype/` compile with no `admit`.
- The equivalence lemmas quantify the theorem constants that stay free as lemma arguments, after
  `&m`: `lemma Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM_equiv &m (b : bool) : Pr[…run(b) @ &m : res] = Pr[…run(b, false) @ &m : res].`
- The equivalence files declare the adversary with every module of both sides excluded:
  `declare module A <: Interfaces.Adv_<C> { -Comp_<L>.Game_<L>, -Comp_<L>.Pkg_Inst_…, … }.`
- Translation runs no EasyCrypt (ADR 0005, `CONTEXT.md` **Translation**). Tests compile.

## 3. What to build

Add to `Red_<L>_<R>.ec`, in one section:

1. `declare module A <: Interfaces.Adv_<G> { … }`, which excludes the modules of `Comp_<GL>`,
   `Comp_<GR>`, the assumption compositions, the reduction router's clones, `Red_<hop>` and
   `B_<hop>`.
2. **The invariant** as an `op`, built from the map and the pairing of story 98 (ADR 0022,
   decision 4): each package state on the left equals its partner's state on the right, the hop
   game's abort flag equals the router's, the assumption game's abort flag implies the router's,
   and each constant stored in `B_<hop>` equals the matching parameter state on the left. One
   invariant for each side when the two sides have different compositions.
3. **The oracle lemmas**, one for each exported oracle (and one small `equiv` for each mapped oracle
   that a reduction package calls, if the script of story 97 has them). When both sides of the hop
   use the same compositions and the same assumption composition, the two sides **share** these
   lemmas: they mention no constant value (ADR 0022, decision 5).
4. **The two reduction equivalences**, with the game instances' own arguments; theorem constants
   that stay free are lemma arguments:
   ```
   lemma <hop>_equiv_L &m (<free constants>) :
     Pr[Comp_<GL>.Exp_<GL>(A).run(..) @ &m : res] = Pr[RedExp_<hop>(_L)(A).run(..) @ &m : res].
   lemma <hop>_equiv_R &m (<free constants>) : … .
   ```
5. **The bound lemma**, with equality (ADR 0022, decision 6):
   ```
   lemma <hop>_bound &m (<free constants>) :
     `|Pr[Exp_<GL>(A).run(..) @ &m : res] - Pr[Exp_<GR>(A).run(..) @ &m : res]|
   = `|Pr[RedExp_<hop>(_L)(A).run(..) @ &m : res] - Pr[RedExp_<hop>(_R)(A).run(..) @ &m : res]|.
   ```
   The right side is in the **hop's** direction: the left assumption term is the one that the map of
   the hop's left side names.

Every proof is the script of story 97, generated. No `admit`. A proof that EasyCrypt does not accept
is a translation bug (ADR 0022, decision 4).

`ReductionReport` gets the names of the bound lemma and the two equivalences, so story 100 does not
build them again from strings.

## 4. Tests first

- [ ] Unit test: the hello-world reduction file has the two equivalences, the bound lemma and no
      `admit`. Its lemma **statements** are the same as the prototype's.
- [ ] Unit test: the first kem-dem reduction shares its oracle lemmas between `_L` and `_R` (one
      lemma for each exported oracle, not two).
- [ ] Unit test: hello-world (two assumption compositions) has an invariant for each side.
- [ ] Unit test: `reduction-consts` (story 98) quantifies `(b : bool)` in the equivalences and the
      bound lemma, and the invariant relates `B_<hop>.b` to the left game's parameter state.
- [ ] Unit test: the third kem-dem reduction's bound lemma has the assumption terms in the hop's
      direction (ideal first).
- [ ] Compile tests: hello-world, kem-dem-cca-ssp and reduction-consts compile, including every
      `Red_*.ec`, with no `admit` in a `Red_*.ec` file (skips without `easycrypt`).

## 5. Rejected alternatives

All from ADR 0022:

- **Proof jobs and lockstep execution for the reduction equivalences.** Slow for a proof of known
  shape, and every lockstep change could break a reduction.
- **Admit the reduction equivalences.** A hole in a step that Domino already discharged.
- **One reduction equivalence by anti-unification.** It needs an algorithm and a fallback, and no
  caller needs the general form.
- **The bound lemma with `<=`.** Equality is true and stronger, as EasyCrypt's `elgamal.ec`
  `conclusion` shows. Only the proposition lemma needs `<=`.

## 6. Acceptance criteria

- [ ] All tests of §4 green, the whole test suite green, `cargo clippy` clean.
- [ ] Complexity: every function in `reduction.rs` within budget (`crap_scope`).
- [ ] `domino easycrypt export` on `example-projects/4WHS --theorem Simple4WHS` writes
      `Red_Hybrid2_Hybrid3.ec` with its lemmas. Translation only; the owner compiles it by hand if
      they want to.
