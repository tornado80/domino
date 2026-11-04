# Story 100 — A proposition exports its lemma

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 99 (the bound lemmas).
**Blocks:** nothing.
**ADR:** `docs/adr/0022-a-reduction-is-a-router-an-adversary-and-an-experiment.md` (decisions 6–8).
**Decisions:** owner's grilling session of 2026-11-04/05, Questions 5, 6 and 7. The terms
**Proposition**, **Proposition lemma**, **Bound lemma** and **Open hop** are in `CONTEXT.md`.

A **writer** story: a new builder in `src/writers/easycrypt/`, the export report, tests.
Test-first.

---

## 1. Why this story exists

Translation writes one lemma for each equivalence and, after story 99, one bound lemma for each
reduction. Nothing joins them. A theorem's propositions (`Main: Game_MON_CCA_PKE_Real ~
Game_MON_CCA_PKE_Ideal`) are the claims that the user wants, and EasyCrypt has no statement of them.

## 2. The facts this story uses

- `Theorem::proofs: Vec<Proof>` (`src/theorem.rs:396`) has one `Proof` for each proposition. The
  parser refuses a proposition with no path (`UnprovenTheoremError`, `src/parser/theorem.rs:851`),
  so each proposition has a path.
- `Proof::path()` (`src/proof.rs`) gives the game instances of the path, each with the
  `ConstAssignment`s that its specialization fixes (`original_name()`, `assigned_value()`).
  `Proof::game_hops()` gives one hop between each pair of neighbours.
- **A hop can be used in either direction** (`other_game`, `src/proof.rs:323`). The direction is
  found by comparing the path neighbour with the hop's `left_game_instance_name()`.
- **One hop can be used more than once, with different specializations.** In kem-dem-cca-ssp, the
  path of `Main` is: `Game_MON_CCA_PKE` (b := false) ≡ `Game_MOD_CCA_PKE_Real_KEM` →KEM→ … →KEM→
  `Game_MOD_CCA_PKE_Real_KEM` (b := true) ≡ `Game_MON_CCA_PKE`. The equivalence is used two times,
  with `b := false` and with `b := true`.
- Each equivalence lemma quantifies the theorem constants: `lemma <L>_<R>_equiv &m (b : bool) :
  Pr[…Exp_<L>(A).run(b) @ &m : res] = Pr[…Exp_<R>(A).run(b, false) @ &m : res].`
- `EquivalenceReport` (`src/writers/easycrypt/export.rs:53`) and `ReductionReport` (stories 98, 99)
  give the file and lemma names. `skipped` lists conjectures and hybrids.
- EasyCrypt's `elgamal.ec` and Cryptobox's `PreSecurity_Init` close such a chain with `have ->:`
  rewrites and `smt()`.

## 3. What to build

A new module `src/writers/easycrypt/proposition.rs`. For each proposition, it writes
`Prop_<Name>.ec` (ADR 0022, decision 8). The file requires every `Eq_*.ec` and `Red_*.ec` on the
path, declares the adversary with the **union** of their restrictions, and has one lemma:

```
lemma <Name> &m (<theorem constants that the path does not specialize>) :
  `|Pr[Exp_<first>(A).run(..) @ &m : res] - Pr[Exp_<last>(A).run(..) @ &m : res]|
  <= <term of reduction step 1> + <term of reduction step 2> + … .
```

- **One term for each reduction step**, in path order. The term is literally the right side of that
  reduction's bound lemma, with the step's arguments, in the **hop's** direction, also when the path
  uses the hop in reverse (ADR 0022, decision 6).
- **Equivalences give no term.** The proof rewrites with the equivalence lemma at the step's
  arguments, and uses the symmetric form when the path uses it in reverse.
- **An open hop gives its own term** (ADR 0022, decision 7): the original adversary's advantage
  between the path's two neighbouring game instances,
  `` `|Pr[Exp_<a>(A).run(..) @ &m : res] - Pr[Exp_<b>(A).run(..) @ &m : res]| ``. An open hop is a
  conjecture, a hybrid, or an equivalence that has no `EquivalenceReport`.
- **No reduction step and no open hop**: the right side is `0%r`.
- **The proof**: the rewrites with the equivalence lemmas, one `have` for each bound lemma, then
  `smt()`. No `admit` in `Prop_*.ec`. The proposition is only as strong as its parts: the
  equivalences' oracle files can still have admits, and that is not this story's concern.

The export report:

- `ExportedTheorem` gets `propositions: Vec<PropositionReport>` (name, file, the number of reduction
  terms, and the open hops by kind and game instance names).
- `domino easycrypt export` prints one `proposition` line for each, and names its open hops.

**Hybrid hops.** `hello-world-hybrid` (theorem `Hybrid`, proposition `main`) has a hybrid hop between
`h$false$` and `h$true$`. If the path's neighbouring game instances of that hop cannot be stated as
`Exp_<C>(A).run(..)` with theorem constants only (for example because the hybrid index is still
free), stop and ask the owner before choosing a behaviour. ADR 0022 rejected "no proposition lemma"
for open hops that can be stated.

## 4. Tests first

- [ ] A new fixture `testdata/easycrypt/proposition-open-hop/`: one theorem with one equivalence, one
      conjecture and one proposition across both. Keep it as small as hello-world.
- [ ] Unit test: kem-dem-cca-ssp exports `Prop_Main.ec` with three reduction terms in path order,
      the third one in its hop's direction, and two uses of the equivalence lemma (`false`, `true`).
- [ ] Unit test: `proposition-open-hop` gets one open-hop term for the conjecture, and the report
      names it.
- [ ] Unit test: a proposition whose path has only equivalences has `0%r` as its right side.
- [ ] Unit test: the lemma takes exactly the theorem constants that the path does not specialize
      (kem-dem `Main`: none of `b`).
- [ ] Unit test: `hello-world-hybrid` behaves as the owner decided (§3).
- [ ] Compile tests: kem-dem-cca-ssp and proposition-open-hop compile, including `Prop_*.ec`, with no
      `admit` in `Prop_*.ec` (skips without `easycrypt`). Compile only; no `domino prove`.

## 5. Rejected alternatives

All from ADR 0022:

- **A chain of lemmas for each path position.** More lemmas for a generated proof, with no gain.
- **Assumptions as axioms with an epsilon.** An axiom over every adversary with no resource bound is
  false in EasyCrypt.
- **An axiom for each conjecture.** Not sound if the conjecture is false.
- **No proposition lemma when the path has an open hop.** Nothing for theorems with hybrids, and a
  status that the user must read and act on.
- **Terms in path direction.** The reader could not match a term with its bound lemma.

## 6. Acceptance criteria

- [ ] All tests of §4 green, the whole test suite green, `cargo clippy` clean.
- [ ] Complexity: every function in `proposition.rs` within budget (`crap_scope`).
- [ ] `domino easycrypt export` on `example-projects/4WHS --theorem Simple4WHS` writes
      `Prop_KXSecurity.ec`. Translation only, no proving.
