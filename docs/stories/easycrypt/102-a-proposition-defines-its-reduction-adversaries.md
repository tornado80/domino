# Story 102 — A proposition defines its reduction adversaries

**Epic:** EasyCrypt export: reductions without an experiment —
`docs/stories/easycrypt/epic-reductions-without-an-experiment.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 101 (the scripts).
**Blocks:** 103.
**ADR:** `docs/adr/0023-a-proposition-owns-its-reduction-adversaries.md` (decisions 1–4, 6).
**Decisions:** owner's grilling session of 2026-11-10/11, Decisions 1, 2, 4, 5, 6 and 8. The terms
**Reduction adversary**, **Bound lemma** and **Run lemma** are in `CONTEXT.md`.

A **writer** story: `src/writers/easycrypt/reduction.rs`, `reduction_lemmas.rs`, `proposition.rs`,
`export.rs` and tests. Test-first.

---

## 1. Why this story exists

Today `Red_<L>_<R>.ec` holds the router, `B_<hop>` with `setup`, `RedExp_<hop>`, the invariant with
conjunct C3, the oracle lemmas, two equivalences and the bound lemma. The bound lemma is stated on
`RedExp`, not on the assumption game's own experiment. This story moves the concrete part to the
proposition file and keeps only the generic part in the reduction's files.

## 2. The facts this story uses

- `reduction.rs`: `b_module`, `red_exp_module`, `StoredConst` and `adversary_init` build `B` and
  `RedExp`. `build_reduction_file` writes one file. `ReductionFile` carries `sides` and `lemmas`.
- `reduction_lemmas.rs`: `side_spec` adds C3 through `param_var_storing`. `SideSpec` decides shared
  versus `_L`/`_R` oracle lemmas. `oracle_proof` writes the ladder. `reduction_lemmas` writes the
  operator, the section, the oracle lemmas, `_equiv_L/_R` and `_bound`.
- `proposition.rs`: `Ctx::add_step` uses `rf.lemmas.bound` and takes its right side as the term.
  `step_values` gives the values that a step fixes (constant → literal). `open_hop` writes an open
  hop's term. `substitute` qualifies names.
- `export.rs`: `ReductionReport` (`equiv_lemmas`, `bound_lemma`, `lemma_consts`) and
  `PropositionReport`. The test `reduction_prototypes_compile` and the compile loop over
  `exported.reductions` and `exported.propositions`.
- `literal_text_to_expr` (`proof.rs`): theorem constants are `bool` or `int` literals.
- The equivalence layout (ADR 0013): `Eq_<L>_<R>.ec` joins, `Eq_<L>_<R>_<O>.ec` is one oracle,
  and a name rule rejects an oracle whose file collides with another file.
- `run` arguments are flat tuples of literals or binders.

## 3. What to build

**The reduction's files** (ADR 0023 decisions 2 and 6):

1. `Red_<L>_<R>_Router.ec`: the clones, the import adapters, the router `Red_<L>_<R>(O)` and
   `inv_<L>_<R>` (or `_L`/`_R`). The invariant has no conjunct C3. Remove `B`, `setup`, `RedExp`,
   `StoredConst` and the code that only they use.
2. `Red_<L>_<R>_<O>.ec`: one oracle lemma for each exported oracle. In this story the proof stays
   the generated ladder, so the tree compiles with no `admit`. Story 103 replaces it.
3. `Red_<L>_<R>.ec`: `declare module A` with the restrictions, and `run_<L>_<R>` (or `_L`/`_R` when
   the sides use different compositions), proved by `proc (inv ..) => //.` and one
   `by conseq <oracle lemma> => /#.` for each oracle.
4. The ADR 0013 name rule also rejects a reduction oracle called `Router`.
5. The reduction writer exports only the run lemma names (and the file names). It exports no
   invariant, oracle lemma or constant to the proposition writer.

**The proposition file** (ADR 0023 decisions 1, 3, 4):

1. For each reduction step on the path, take the values that the step fixes for the theorem
   constants that the reduction packages read. If the step leaves one of them free, the hop is an
   **open hop** of this proposition, with its own term.
2. One adversary for each different (hop, values) pair on the path:
   `B_<L>_<R><s> (A : Adv_<G>) (O : Iface_<Assm>)` with `run` that calls
   `Red_<L>_<R>_Router.Red_<L>_<R>(O).init(<values>)` and runs `A` against the router.
3. The **merge rule**: build one binder for each pair of differing values (left, right) of the game's
   and the assumption's `run` arguments. A game position and an assumption position with the same
   pair share the binder. Merge when both sides use the same game composition and the same
   assumption composition, and the set of the game's differing pairs equals the set of the
   assumption's. Then write `equiv_<L>_<R><s> &m (<binders>)`. Otherwise write
   `equiv_<L>_<R><s>_L &m` and `_R &m` with literals.
4. Each `equiv` proof: `byequiv (: ={glob A} /\ arg{1} = (..) /\ arg{2} = (..) ==> ={res}) => //.`,
   `proc; inline *; wp.`, `call (Red_<L>_<R>.run_<L>_<R> A).`, `by auto => /#.` (the script of
   story 101).
5. `bound_<L>_<R><s> &m`, an equality, proved by `rewrite` with the `equiv` lemma or lemmas. The
   proposition lemma takes its right side as the term, as today.
6. The suffix `<s>` is `_<const>_<value>` for each constant that the reduction packages read, in
   theorem order, with `neg<n>` for a negative integer. It is empty when they read no free constant.
   A hop that no proposition uses gets no adversary and no `equiv` or `bound` lemma.

**The report** (Decision 8):

- `ReductionReport`: the router file, the oracle files, the joining file, the run lemma names and
  the number of `admit`s. Remove `equiv_lemmas`, `bound_lemma` and `lemma_consts`.
- `PropositionReport`: for each reduction step, the adversary, its values, the `equiv` name (or the
  `_L`/`_R` names) and the bound name.

**Docs:** update `docs/easycrypt-export.md` §"Translating reductions" for the new files and lemmas,
and the prototype descriptions.

## 4. Tests first

- [ ] Unit test: kem-dem-cca-ssp writes `Red_<L>_<R>_Router.ec`, one `Red_<L>_<R>_<O>.ec` for each
      oracle and `Red_<L>_<R>.ec` for each reduction. No file contains `RedExp` or `setup`.
- [ ] Unit test: the invariant has no conjunct that relates a stored constant.
- [ ] Unit test: kem-dem-cca-ssp `Prop_Main.ec` has one adversary for each reduction with an empty
      suffix, a merged `equiv` lemma, and the bound lemmas in path order.
- [ ] Unit test: hello-world (two assumption compositions) gets `run_<L>_<R>_L` and `_R`. With a
      proposition (from story 101), it gets `equiv_.._L` and `_R` with literals.
- [ ] Unit test: `reduction-consts` with a path that fixes `b` gets `B_mod_real_mod_ideal_b_false`
      and `_b_true`. With a path that leaves `b` free, the hop is an open hop and gets no adversary.
- [ ] Unit test: the merge rule on flat tuples: equal pair sets merge, an assumption pair that the
      game does not have gives `_L`/`_R`, different compositions give `_L`/`_R`.
- [ ] Unit test: a negative integer value gives `neg<n>` in the suffix.
- [ ] Unit test: an oracle called `Router` is rejected with the name-rule error.
- [ ] Unit test: the report entries have the fields of §3.
- [ ] Compile tests: hello-world, kem-dem-cca-ssp and reduction-consts compile, with no `admit` in a
      `Red_*.ec` or `Prop_*.ec` file (skips without `DOMINO_EASYCRYPT`). Compile only; no `prove`.
- [ ] Update `reduction_prototypes_compile` for the prototypes of story 101.

## 5. Rejected alternatives

From the grilling of 2026-11-10/11 (ADR 0023):

- **Enumerate all values of the free constants**, **a section `declare op`** (EasyCrypt refuses
  it), **an abstract `op` for each constant**, **`RedExp` only for free constants.**
- **Only the oracle lemmas in the reduction's files**, and **the run lemma in the proposition
  file**: the proposition would name the invariant and every oracle lemma.
- **The `equiv` lemmas in the reduction's files**: they name `B`, which is in the proposition file.
- **`require import` of the reduction files**: the `Cloned_Pkg_*` names collide, so names stay
  qualified.
- **Merge a negated Boolean**, **never merge**, **full anti-unification of nested terms.**
- **Numbered adversaries**, **`real`/`ideal` suffixes.**
- **Option B of the report** (only file names and counts).

## 6. Acceptance criteria

- [ ] All tests of §4 green. Run the tests with a filter, never the full suite on a 4WHS-size
      project. `cargo clippy` clean.
- [ ] Complexity: every touched function within budget (`.sdlc-workspace/crap-coverage.sh <filter>`).
- [ ] `domino easycrypt export` on `example-projects/4WHS --theorem Full4WHS` writes the H1 and H6
      reductions with `B_.._b_false` and `B_.._b_true` in `Prop_main.ec`. Translation only; the
      owner compiles it by hand if they want to.
