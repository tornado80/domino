# Story 112 — A sampling into a name that holds a value goes through a temporary

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** nothing.
**Blocks:** nothing. Story 111 is independent of this story.
**ADR:** none. The change is easy to undo. It goes against one rejected alternative of story 96;
§2 and §6 say why that is correct now.
**Decisions:** owner's grilling session of 2026-11-14/15
(`program-mismatch_in_4WHS-mac_and_4WHS-prf-mac`), Questions 2 to 7 and 9. The term
**Oracle argument** is in `CONTEXT.md`.

A **writer** story: `src/writers/easycrypt/package.rs` (the oracle translator and `SampleTemps`),
tests and fixtures. Test-first.

---

## 1. Why this story exists

`MAC.Init` in the 4WHS-mac and 4WHS-prf-mac models samples into its own argument:

```
oracle Init(handle: (Integer, Integer, Integer, Bits(n), Bits(n)), key: Bits(n), hon: Bool) {
    if (Keys[handle] == None) {
        if hon {
            key <-$ Bits(n);
        }
        Honesty[handle] <- Some(hon);
        Keys[handle] <- Some(key);
    }
}
```

Since story 96, the export keeps this as a write to the parameter: `key <$ dbits_n;`. After
`proc; inline.`, the caller's `key <- kmac` comes before the sampling, and `sp` puts
`key{2} = kmac{2}` into `#pre`. At the sampling, the prover sends
`seq 1 1 : (#pre /\ temp{1} = key{2})`. EasyCrypt must then keep `key{2} = kmac{2}` after `key` is
sampled again. That is false, and the side goal fails.

Before story 104, the goal was admitted `program-mismatch`. Since story 104, the prover detects the
case (`sampled_var_in_pre`, `goals.rs:83`) and admits it `seq-post` with the claim
`sampling: key{2} in #pre`. The label is correct, but the goal is still admitted.

In the runs of 2026-10-30 (diagnosis of that day), this is the cause of these admits:

| Job | Project | Admits |
|---|---|---|
| hop 11 (`H6_1_1 ~ H7_0`), `Send2` | 4WHS-mac | N51 (`temp{1} = key{2}`) |
| hop 11, `Send3` | 4WHS-mac | N138 |
| hop 13 (`H7_1_1_0 ~ H7_1_1_1`), `Send2` / `Send3` | 4WHS-mac | N51, N68 / N104, N133 (`key{1} = key{2}`) |
| hop 11, `Send2` / `Send3` | 4WHS-prf-mac | N45 / N142 (`y{1} = key0{2}`; the inlined name is `key0`) |
| hop 13, `Send2` / `Send3` | 4WHS-prf-mac | N25, N66 / N18, N181 (`key0{1} = key0{2}`) |

The side-invariant job `SideInv_H7` has `program-mismatch` admits in both projects at the hoare
step `seq 1 : (#pre); 1: auto => />.` (`sampling_hoare`): 4WHS-mac `Send2` N32, N42, `Send3` N64,
N99; 4WHS-prf-mac `Send2` N17, N41, `Send3` N13, N128. Hoare `rnd` makes no lossless goal, so the
cause of story 111 does not apply. That the cause is this story's is an inference. It was not
replayed. Story 104's check covers only the two-program `sampling()`, not `sampling_hoare`.

## 2. The facts this story uses

- **Tested on 2026-10-30** at N51 of hop 11 `Send2` (4WHS-mac), on a copy of `Pkg_MAC.ec` changed by
  hand:

  ```
  var key_ : bits_n;
  …
  if (hon) {
    key_ <$ dbits_n;
    key <- key_;
  }
  ```

  Then `seq 1 1 : (#pre /\ temp{1} = key_{2}); 1: auto => />.` closes, and the next goal is the
  program goal that the joint tree expects.
- **The export has this pattern already.** A sampling into a table entry, `T[k] <-$ τ`, becomes
  `ec_s<N> <$ d; T.[k] <- ec_s<N>;` (`package.rs:1007-1020`). `SampleTemps` (`package.rs:847`) holds
  the counter and the declarations, and `declare_sample_temp` (`package.rs:885`) gives the next name.
- **The module and the debugger listing share the translator.** `build_proc` makes one
  `SampleTemps` per proc (`package.rs:788`). The EasyCrypt listing calls the same translator
  through `translate_oracle_stmt` (`lower.rs:686`) with its own `SampleTemps` (`lower.rs:236`,
  `lower.rs:623`). A change inside the translator therefore reaches both. Check during the story
  whether one listing `SampleTemps` spans more than one frame (inlined oracles), and see §3.4.
- **The identifier kind is known.** `PackageIdentifier` (`identifier.rs:205`) has `OracleArg`,
  `State` and `Local`. An argument and a state field need no analysis.
- **Alignment does not look at assignments.** `align.rs` compares only decisions (branches and
  samplings). One more assignment after a sampling does not change alignment. The prover reads the
  sampled variable from EasyCrypt's goal (`lvalue.pp`), so it follows the new name.
- **The randomness mapping does not look at names.** The `simple` mapping pairs samplings by
  `sample-id` (`src/writers/smt/contexts/equivalence/emit.rs:711`). The Domino model does not
  change, so Domino's proofs do not change.
- **The scope in the three 4WHS models.** The only sampling into a name that already holds a value
  is `key` in `MAC.Init` of 4WHS-mac and 4WHS-prf-mac. In 4WHS, `MAC.Init` takes only `handle`, and
  `key` is a local that it samples once. `KX_noprfkey` writes `k` in `Reveal` and samples it in
  `Test`. These are different oracles, so that is not a case. The export of 4WHS must therefore
  not change.
- **The research.** This is SSA for the one write that needs it. Each write gets a fresh version,
  so a fact about the old value stays true (2LS, arXiv 2302.02380; the Strata SSA pass,
  strata-org/Strata PR 1127). The Strata pass also shows the trap: a renamed write to an output or
  argument is lost if nothing copies it back. Here the copy `x <- ec_s<N>` is that copy.

## 3. What to build

In `src/writers/easycrypt/package.rs`:

1. **`SampleTemps` keeps the locals that the body has written.** It has a private set of the
   locals written so far in the current proc, in program order, on any branch. The translator adds a
   local to it at each write: an assignment, a sampling, a tuple pattern (each of its names), and the
   `ec_r<N>` binding of an invoke. A write in a `then` branch before the `if` ends counts. This
   over-approximates, and that is harmless. No caller reads or sets the set.
2. **The `Pattern::Ident` arm of the sampling** (`package.rs:997`) samples into a temporary when the
   target already holds a value. That is the case when the target is:
   - an oracle argument (`PackageIdentifier::OracleArg`);
   - a state field (`PackageIdentifier::State`);
   - a local in the set of item 1.

   Then it emits `ec_s<N> <$ d; x <- ec_s<N>;`, with `declare_sample_temp`, as the table arm does.
   For every other target, it emits `x <$ d;` as before. The doc comment says why the temporary is
   there: `#pre` can hold a fact about the old value of `x`, and a sampling into `x` would make the
   `seq` post of the prover false.
3. **The prover does not change.** Story 104's check stays as a safety net, for a shape that this
   story does not cover.
4. **The debugger listing.** If one listing `SampleTemps` spans several frames, the set must not mix
   the locals of two frames. Key the set by the name the translator writes (`resolve_name`), which is
   unique per frame, or reset the set at each frame. The test of §4 shows that the module and the
   listing agree for `MAC.Init`.
5. **Docs.** `docs/proving-algorithm.md` §9.1 and §9.2, rows of `seq-post`: say that the export now
   prevents the case of an argument, a state field and a local written before (story 112). The
   check of story 104 stays for a shape the export does not see. `docs/easycrypt-export.md`: the
   section on oracle bodies shows the new form, next to the table-entry form.

A loop variable (`CodeLoopVar`) is out of scope. A sampling in a loop body gives a `while` in
EasyCrypt, and alignment already reports it as `unknown-ec-instruction`.

## 4. Tests first

- [x] Unit test in `package.rs`: an oracle that samples into its argument renders
      `ec_s1 <$ dbits_n; key <- ec_s1;`, and declares `ec_s1` once.
- [x] Unit test: a sampling into a state field renders through a temporary.
- [x] Unit test: a local that an earlier statement writes (an assignment, then a sampling) renders
      through a temporary. A write in a `then` branch, then a sampling after the `if`, also does.
- [x] Unit test: a sampling into a local with no earlier write renders `x <$ d;` as before, with no
      temporary. A local written in one oracle and sampled in another oracle of the same package
      does not get a temporary.
- [x] The `story96` fixture: `the_body_still_writes_to_the_argument` changes. The write to `key` is
      now the copy `key <- ec_s<N>`. `an_argument_that_the_body_writes_is_not_declared_again` stays
      green.
- [x] Unit test: the EasyCrypt listing (`lower.rs`) of the `story96` oracle has the same sampling
      and copy as the module.
- [x] Compile test: `story96_full_tree_compiles_in_dependency_order` stays green.
- [ ] Regression test: the export of `example-projects/4WHS` gives the same text as before. No
      sampling there gets a temporary.

## 5. Acceptance criteria

- [x] All tests of §4 green, with filtered test runs only. `cargo clippy` clean.
- [ ] Complexity: the sampling arm of `translate_stmt`, `SampleTemps` and every other touched
      function within budget (`.sdlc-workspace/crap-coverage.sh <filter>`). If `translate_stmt` goes
      over budget, move the sampling arm into a function of its own.
- [ ] The export of `ec4whs/4WHS` (theorem `Full4WHS`) is byte-identical to the export before the
      story.
- [ ] The proof runs: see story 111 §7. They run once, after Stories 111 and 112 are both merged.
      For this story: no `seq-post` admit with a claim `sampling: key{…} in #pre` or
      `sampling: key0{…} in #pre`, and no `program-mismatch` admit at the `MAC.Init` sampling in
      hop 11 `Send3` (both projects) and in `SideInv_H7` `Send2` (both projects). If an admit of
      this cause stays, the report diagnoses it. It does not fix it in this story.

## 6. Rejected alternatives

- **Every sampling goes into a temporary.** The rule is the simplest and needs no analysis, but
  every exported module changes, and the inlined names move (`ni1` becomes `ni2`). Every
  hand-written proof that names a sampled variable breaks (change amplification).
- **The prover quantifies the old value in the `seq` post** (Floyd's strongest postcondition,
  `∃x′. P[x′/x]`). EasyCrypt has no syntax for "`#pre` with `key{2}` replaced by a bound variable".
  The prover would have to print `#pre` itself, and after `sp` that is hundreds of KB. Story 104 §6
  put this off for that reason.
- **Change only the models** (`k <-$ Bits(n); key <- k;` in `MAC.Init`). No Domino change, but
  Domino accepts a write to an argument, so the next model with this shape gets `seq-post` admits
  again. The export can absorb the case itself.
- **Arguments and state fields only, no locals.** The rule reads only the identifier kind, but a
  local written before is a known shape (story 104 §1) that would stay an admit.
- **A pre-pass over the oracle body** (in the style of `collect_locals`) that computes the set and
  gives it to the translator. The set would cross a module boundary, and `lower.rs` would have to
  run the pre-pass too (change amplification). The set stays private to the translator.
- **Story 96 §5 rejected "a fresh local, with a copy of the argument at proc entry".** Its reasons
  do not apply to this story. (1) "EasyCrypt does not need it": EasyCrypt does not need it to
  compile, but the prover needs it for the `seq` post. (2) "The module and the debugger listing would
  then be different": the two share the translator, so they change together. (3) "Each affected
  oracle gets one more statement to prove": the copy is an assignment, and `sp` takes it. Also, the
  copy here is at the sampling, not at proc entry, and only the sampled target changes.
