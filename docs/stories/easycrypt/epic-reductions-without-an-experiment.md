# Epic — EasyCrypt export: reductions without an experiment

**Parent epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Follows:** `epic-reductions-and-propositions.md` (stories 97–100).
**Branch:** `amir/easycrypt-export`
**ADR:** `docs/adr/0023-a-proposition-owns-its-reduction-adversaries.md` (supersedes parts of ADR
0022).
**Glossary:** `CONTEXT.md` — **Reduction**, **Reduction package**, **Reduction router**,
**Reduction adversary**, **Bound lemma**, **Run lemma**, **Oracle lemma**, **Proposition lemma**,
**Open hop**.
**Decisions:** owner's grilling session of 2026-11-10/11, Decisions 1 to 9.
**Effort:** L.

---

## 1. Goal

After stories 97–100, each reduction has a **reduction experiment** `RedExp_<hop>(A).run(consts..)`,
so its bound lemma is not stated on the assumption game's own experiment. Its oracle proofs are long
tactic ladders that nobody can read. After this epic, a reduction looks like the hand-written
`_Lotta` files of Full4WHS:

- `Exp_<G>(A).run(..) = Exp_<Assm>(B_<L>_<R><s>(A)).run(..)`, with one adversary for each set of
  values that a proposition gives to the reduction packages' constants;
- one equivalence lemma for both sides when that is safe;
- oracle proofs with one line for each program step, written by the blind walk of
  `docs/proving-algorithm.md`.

## 2. What the epic delivers

| File | Holds | Written by |
|---|---|---|
| `Red_<L>_<R>_Router.ec` | clones, router `Red_<L>_<R>(O)`, `inv_<L>_<R>` | `export` |
| `Red_<L>_<R>_<O>.ec` | one oracle lemma | `prove` (`admit` after `export`) |
| `Red_<L>_<R>.ec` | `run_<L>_<R>` (or `_L`/`_R`), joins the oracle lemmas | `export` |
| `Prop_<Name>.ec` | `B_<L>_<R><s>`, `equiv_<L>_<R><s>` (or `_L`/`_R`), `bound_<L>_<R><s>`, the proposition lemma | `export` |

`<s>` is `_<const>_<value>` for each theorem constant that the reduction packages read, in theorem
order, with `neg<n>` for a negative integer. It is empty when they read no free constant.

## 3. Out of scope

- Hybrid hops (ADR 0022 decision 7 stays).
- Merging a negated Boolean (`run(.., !b)`).
- Proving 4WHS-size projects. Tests use small fixtures only, and `prove` runs only on them.
- Lockstep execution for reductions.

## 4. Stories

| Order | # | Story | File | Depends on |
|---|---|---|---|---|
| 1 | 101 | A hand-written prototype fixes the new reduction layout | `101-a-hand-written-prototype-fixes-the-new-reduction-layout.md` | — |
| 2 | 102 | A proposition defines its reduction adversaries | `102-a-proposition-defines-its-reduction-adversaries.md` | 101 |
| 3 | 103 | A proof job proves a reduction's oracle lemmas | `103-a-proof-job-proves-a-reductions-oracle-lemmas.md` | 102 |

The stories are sequential. After story 102 the tree compiles with no `admit` (the oracle files
still have the ladder). Story 103 replaces the ladder with the proof job.

## 5. Done when

- [ ] Stories 101–103 are done, each with its implementation report.
- [ ] No exported file names `RedExp_` or `setup`.
- [ ] `domino easycrypt export` and then `domino easycrypt prove` on kem-dem-cca-ssp leave no `admit`
      in a `Red_*.ec` or `Prop_*.ec` file, and the whole tree compiles.
- [ ] `docs/easycrypt-export.md` and `docs/proving-algorithm.md` describe the new layout and the
      reduction proof job.
