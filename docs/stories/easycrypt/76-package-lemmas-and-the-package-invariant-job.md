# Story 76 — Package lemmas and the package-invariant job

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 73, symbolic-execution 29.
**Blocks:** 77.
**ADR:** 0016 (package invariants are proved once for each package), 0017 (open calls).
**Decisions:** grilling of 2026-10-12/20, Questions 4, 6 and 11.

A **translation, tactics and CLI** story, Rust only.

---

## 1. Why this story exists

ADR 0014 proves package invariants inside `SideInv_<C>_<O>`, once for each composition. Domino now
checks each package once (stories 74, 75). The owner wants EasyCrypt to do the same, by quantifying
over the package's imports as one quantifies over an adversary (Question 4, ADR 0016). Nothing is
known about the imports, so each import call is proved with `call (_: true)`.

Vocabulary (`CONTEXT.md`, already updated): **Package-invariant lemma**, **Frame lemma**,
**package-invariant job**, **Open call**.

## 2. Inherited

- Story 03/14: package variants `Pkg_<V>.ec`, `module <V>(O : <V>_Imports)`, `proc init`.
- Story 69: the side-invariant job machinery (`JobKind`, records, saved trees, locks, seal, resume,
  `--jobs N`, `Judgement::Hoare`), the leaf procedure (64), the part fallbacks (65), the key case
  split (66).
- Story 73: `PkgInv_<N>_of_<P>` templates.
- Symbolic-execution 29: the package tree of `<V>.<O>` with the verdict of each named check.

## 3. Work to do

### 3.1 The package-invariant lemma

For each package variant `<V>` whose package has invariants, and each oracle `<O>`, a file
`PkgInv_<V>_<O>.ec`:

```
require import Pkg_<V>.
section.
declare module I <: <V>_Imports {-<V>}.
lemma PkgInv_<V>_<O> :
  hoare[<V>(I).<o> : PkgInv_<N1>_of_<P> {| <V>'s state |} /\ … ==> res <> None => PkgInv_<N1>_of_<P> {| … |} /\ …].
proof. … qed.
end section.
```

- The state record literal is the variant's state fields at the one memory.
- Translation writes `admit` as the proof. The package-invariant job owns it.

### 3.2 The frame lemma

In the same section, or in `Frame_<V>_<O>.ec`:

```
declare op J : (glob I) -> bool.
declare axiom I_<f> : hoare[I.<f> : J (glob I) ==> res <> None => J (glob I)].   (* one for each import *)
lemma Frame_<V>_<O> : hoare[<V>(I).<o> : J (glob I) ==> res <> None => J (glob I)].
```

- **First task of the story:** settle the exact form when an import aborts, and test it on the fork
  with a hand-written example before you write the generator. The goal: after `I.<f>` returns
  `None`, the package returns `None`, so the post is true without `J`.
- The proof is structural and fixed: `proc`, `auto` over the package's own statements (they cannot
  write `glob I`), `call I_<f>` at each import call, `if` over each branch. Translation writes it,
  and the package-invariant job checks it. No Domino tree and no verdicts.

### 3.3 The start lemma

`hoare[<V>(I).init : true ==> PkgInv_… {| … |} /\ …]`, one conjunct for each named invariant, in
`PkgInv_<V>_init.ec`. Proof: `proc; auto` and then the part fallbacks. Its Domino verdict is the
start check of story 75.

### 3.4 Join file

`PkgInv_<V>.ec` `require`s every oracle file, the frame lemmas and the start lemma.

### 3.5 The package-invariant job

- `domino easycrypt prove --pkg-inv <P>` (`--oracle O` for one oracle) proves, for each variant of
  `P` that the theorem uses: the package-invariant lemma of each oracle, the frame lemma of each
  oracle and the start lemma.
- It is the job machinery of story 69 with a new `JobKind::PackageInvariants(P)`: records, saved
  trees and locks under `session/PkgInv_<V>/<O>.*` and `progress/PkgInv_<V>/<O>.*`; one oracle is one
  unit of parallelism (ADR 0013).
- The walk of a package-invariant lemma: `proc.`, then the package tree. A determined node gives
  `rcondt`/`rcondf`, a split gives `if.` with a bullet for each arm, a sampling `rnd`/`auto`, an
  **open call `call (_: true)`**. At a terminal: the leaf procedure (64) with one memory, the part
  fallbacks (65), the key case split (66). An unfolded `PkgInv_<N>_of_<P>` gives its named claim and
  the package tree's verdict.
- Names: the new files join the lemma-file name rule of story 69 (`LemmaFileCollision`).

### 3.6 Rejected alternatives (see ADR 0016)

- One combined lemma with `call (_: J)`; only the package lemma with a re-walk for each composition;
  ADR 0014 unchanged; a side-invariant job that proves missing package lemmas; one job for each
  theorem in a fixed order.

## 4. Acceptance criteria

- [ ] The report shows the hand-written frame lemma for an aborting import that compiles on the fork
      (§3.2, first task).
- [ ] Translation of Full4WHS writes `PkgInv_<V>_<O>.ec`, the frame lemmas, `PkgInv_<V>_init.ec` and
      `PkgInv_<V>.ec` for each variant with invariants; with every proof admitted they compile.
- [ ] `prove --pkg-inv PRF` on Full4WHS proves or admits each lemma, and each admit names its claim
      and the package tree's verdict.
- [ ] Every frame lemma is proved without an admit on Full4WHS.
- [ ] A test: two oracles of one package run in parallel with `--jobs 2`.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --pkg-inv PRF --tactics --jobs 4
cd <out> && easycrypt compile PkgInv_<V>.ec
```
