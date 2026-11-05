# Epic — EasyCrypt export: reductions and propositions

**Parent epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**ADR:** `docs/adr/0022-a-reduction-is-a-router-an-adversary-and-an-experiment.md`
**Glossary:** `CONTEXT.md` — **Assumption**, **Reduction**, **Mapped package**, **Reduction
package**, **Reduction router**, **Reduction adversary**, **Reduction experiment**, **Bound lemma**,
**Proposition**, **Proposition lemma**, **Open hop**.
**Decisions:** owner's grilling session of 2026-11-04/05. Hybrid hops put out of scope on
2026-11-05.
**Effort:** L.

---

## 1. Goal

Translation skips each reduction hop (`"reductions are not translated"`), and nothing joins the
hop lemmas into a statement of a proposition. After this epic, the exported tree of a theorem ends
with one EasyCrypt lemma for each proposition. The lemma bounds the original adversary's advantage
by the advantages of the reduction adversaries against the assumptions.

## 2. What the epic delivers

- **For each reduction hop, `Red_<L>_<R>.ec`** (ADR 0022, decisions 1–6, 8):
  - a **reduction router** `Red_<hop>(O : Iface_<Assm>)` built from clones of the reduction
    packages, with its own abort flag; a call that reaches a mapped package goes to `O`;
  - a **reduction adversary** `B_<hop>(A)(O)` that stores the theorem constants (`setup`) and
    runs `A(Red_<hop>(O))`;
  - a **reduction experiment** `RedExp_<hop>(A).run(consts..)` that runs the assumption game's own
    experiment against `B_<hop>(A)`, so no lemma needs a memory hypothesis;
  - two **reduction equivalences** (`_L`, `_R`) and the **bound lemma** (equality), with a complete
    generated proof and an invariant that comes from the map.
- **For each proposition, `Prop_<Name>.ec`** (ADR 0022, decisions 6–8): one lemma, advantage `<=` the
  sum of the bound lemmas' right sides in path order. Equivalences give no term. An **open hop** (a
  conjecture, or an equivalence that translation does not write) gives its own term.

## 3. Out of scope

- **Hybrid hops.** A proposition whose path has a hybrid hop gets no proposition lemma, and the
  report says so. A reduction inside a hybrid hop stays skipped. A later design decides how hybrids
  translate.
- Randomness mappings.
- Proving 4WHS-size projects. 4WHS is translated only; tests compile the small fixtures.

## 4. Stories

| Order | # | Story | File | Depends on |
|---|---|---|---|---|
| 1 | 97 | A hand-written reduction proof fixes the script (prototype) | `97-a-hand-written-reduction-proof-fixes-the-script.md` | — |
| 2 | 98 | A reduction exports its router, adversary and experiment | `98-a-reduction-exports-its-router-adversary-and-experiment.md` | 97 |
| 3 | 99 | A reduction exports its equivalences and its bound lemma | `99-a-reduction-exports-its-equivalences-and-bound-lemma.md` | 97, 98 |
| 4 | 100 | A proposition exports its lemma | `100-a-proposition-exports-its-lemma.md` | 99 |

The stories are sequential: each one needs the output of the one before it.

## 5. Done when

- [ ] Stories 97–100 are done, each with its implementation report.
- [ ] `domino easycrypt export` on kem-dem-cca-ssp writes three `Red_*.ec` files and `Prop_Main.ec`,
      and the whole tree compiles with no `admit` in a `Red_*.ec` or `Prop_*.ec` file.
- [ ] `domino easycrypt export` on hello-world-hybrid reports its proposition as skipped because of
      the hybrid hop.
- [ ] `docs/easycrypt-export.md` describes the reduction translation and no longer says "skip".
