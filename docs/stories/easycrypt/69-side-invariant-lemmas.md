# Story 69 — Side-invariant lemmas of the composition, joined with `conseq`

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 58, 64, 65, 68, symbolic-execution 25.
**Blocks:** nothing.
**ADR:** 0014 (supersedes 0010).

A **translation, tactics and CLI** story, Rust only.

---

## 1. Why this story exists

ADR 0010 (story 58) put every package invariant and game invariant inside `inv`, under the
`!abort` guard. So each leaf of each equivalence also proves both sides' one-sided invariants, and a
composition that is in two equivalences (`H6` in H6_1_0 ~ H6_1_1 and H6_1_1 ~ H7_0) has its
invariants proved in each of them.

The owner decided (grilling of 2026-10-09/12, Questions 10–11):

- the side invariants are proved for each **composition**, for every value of its parameters,
  never for each game instance or each equivalence;
- one file for each oracle, `SideInv_<C>_<O>.ec`, and `SideInv_<C>.ec` to join them, flat in the
  export directory;
- `prove --side-inv <C>` proves them; `--proofstep <eq>` does not, and stops with a warning when
  they are missing; a whole-theorem `prove` proves them in parallel with the equivalences;
- the side-invariant job follows the side tree of one-sided execution (symbolic-execution 25).

Tested on the fork during the grilling: `by conseq eqf hM hN.` joins an equiv lemma with a hoare
lemma for each side. A hoare lemma that says nothing about a parameter global (`M.b`) applies under
an equiv precondition that fixes it. In the translation the parameters are module globals that
`params_inv` fixes (for example `Pkg_Inst_PRF.b`), so this is the case here.

Vocabulary (`CONTEXT.md`, already updated): **Side-invariant lemma**, **side-invariant job**,
**Oracle lemma**, **One-sided execution**, **Package invariant**, **Game invariant**.

## 2. Inherited from earlier stories

- **Story 58:** `PkgInv_<Pkg>` templates over `<Pkg>_pkgstate`, the `PkgInv_<l|r>_<Inst>` wrappers,
  `GameInv_<G>`, `side_invariant_ops`, `Part::SideInvariant`. They live in each equivalence's
  invariant file today.
- **Story 64–66:** the leaf procedure, the part fallbacks and the key case split.
- **Story 68:** oracle lemmas `Eq_<L>_<R>_<O>.ec`, the glue `Eq_<L>_<R>.ec`, records and locks for
  each oracle, `--jobs N`.
- **Symbolic-execution 25:** the side tree of `C.O`, with the verdict of each package and game
  invariant check at each terminal.

## 3. Work to do

### 3.1 Translation

- **Definitions, one time each:** each package invariant template `PkgInv_<Pkg>` (and its
  `<Pkg>_pkgstate`) goes to `Pkg_<Pkg>.ec`, because the package declares it. `GameInv_<C>`, the
  composition's side state record (one `<Pkg>_pkgstate` field for each package instance) and
  `side_inv_<C> s = !s.abort => PkgInv_… /\ … /\ GameInv_<C> s` go to `Comp_<C>.ec`. The
  equivalence's invariant file no longer defines them.
- **`SideInv_<C>_<O>.ec`**, for each oracle `O` of each composition `C` that has a package or game
  invariant:
  `lemma SideInv_<C>_<O> : hoare[<C>.<O> : side_inv_<C> {| … |} ==> side_inv_<C> {| … |}].`
  The record literal is the composition's globals at the one memory. Translation writes it with
  `admit` as its proof. The side-invariant job owns it.
- **`SideInv_<C>.ec`** `require`s each `SideInv_<C>_<O>`. Translation writes it.
- **`inv`** keeps `params_inv`, the abort equality and `!abort => StateRelation_invariant`.
- **The oracle lemma** (story 68) assumes the side invariants:
  `equiv[… : ={arg} /\ inv … /\ side_inv_<L> {| … |}{1} /\ side_inv_<R> {| … |}{2} ==> ={res} /\ inv …]`.
  It does not `require` `SideInv_` files.
- **The glue** `call`s with `inv … /\ side_inv_<L> … /\ side_inv_<R> …`. Its base case also shows the
  side invariants on the initial state. Each oracle bullet is
  `+ by conseq Eq_<L>_<R>_<O> SideInv_<L>_<O> SideInv_<R>_<O>.` Only the glue `require`s `SideInv_<L>`
  and `SideInv_<R>`. A side whose composition has no side invariant has no `SideInv_` file, no
  `side_inv` conjunct, and no lemma in the `conseq`.
- **Names:** `SideInv_<C>_<O>` and `SideInv_<C>` must not collide with each other or with other
  files (`SideInv_A` with oracle `B_x` against composition `A_B` with oracle `x`). Translation
  rejects a collision and names both.

### 3.2 The side-invariant job

- `prove --side-inv <C>` runs one side-invariant job: for each oracle of `C`, it runs
  one-sided execution (or reads the saved side tree), then a tactics run on `SideInv_<C>_<O>.ec`.
  `--jobs N` works as for oracle lemmas.
- Record, saved tree and lock: `session/SideInv_<C>/<O>.record.json`, `<O>.tree.json`,
  `progress/SideInv_<C>/<O>.lock`. Seal, respawn and resume as for oracle lemmas.
- The walk: `proc; inline.`, then the router prelude (`if (!abort_flag)`: the arm where the game has
  already aborted keeps the state and closes with the quick close). Then it follows the side tree:
  a determined node gives `rcondt ^if` / `rcondf ^if`, a branch with both arms gives `if.` and a bullet
  for each arm, a sampling gives `rnd`/`auto`. At a terminal: the leaf procedure of story 64 with one
  memory (`auto => &hr hpre.`), the part fallbacks of story 65, the key case split of story 66.
- Claims: an unfolded `PkgInv_<Inst>` or `GameInv_<C>` gives its claim, with the side tree's
  verdict. §3.6 applies to each claim. A part with no claim gets the worst verdict of the terminal's
  checks.

### 3.3 The `prove` command

- `--side-inv <C>`: only the side-invariant job of `C`.
- `--proofstep <eq>`: before it starts, the proof job checks that, for each side of the equivalence
  whose composition has side invariants, `SideInv_<C>.ec` and each `SideInv_<C>_<O>.ec` are on
  disk. A file with admits counts (a **partial proof**). If one is missing, the equivalence does not
  start, and the job warns: `side invariants of <C> are not proved: run prove --side-inv <C> first`.
- Neither option: the side-invariant jobs of every composition whose `SideInv_` files are missing
  run **in parallel** with the equivalences' proof jobs. The oracle lemmas do not need the
  `SideInv_` files; only the glue does, and nothing runs the glue before the end.

### 3.4 Rejected alternatives (see ADR 0014)

- Lemmas for each equivalence (proved several times), or for each game instance (the wrong owner).
- Game invariants only (two mechanisms for one kind of claim).
- `conseq` in each oracle lemma (no parallel run of compositions and equivalences).
- A blind one-sided walk (symbolic-execution 25 §3.4).

## 4. Acceptance criteria

- [ ] Translation of Full4WHS writes `SideInv_<C>_<O>.ec` and `SideInv_<C>.ec` for each composition
      with side invariants, and none for the others. With every proof admitted, each glue
      `Eq_<L>_<R>.ec` compiles.
- [ ] `inv` in each invariant file has no `PkgInv_` or `GameInv_` conjunct.
- [ ] A test: `prove --proofstep <eq>` with a missing `SideInv_` file does not start the equivalence
      and prints the warning.
- [ ] A test: a whole-theorem `prove` starts a side-invariant job and a proof job at the same time.
- [ ] A test: the name rule rejects the collision of §3.1.
- [ ] The implementation report gives, for H6_1_0 ~ H6_1_1 and H6_1_1 ~ H7_0, the admits and wall
      time before and after, and the admits of `SideInv_H6_*`.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --side-inv H6 --tactics --jobs 4
$D easycrypt prove --theorem Full4WHS --proofstep <step of H6_1_0 ~ H6_1_1> --tactics
cd <out> && easycrypt compile Eq_H6_1_0_H6_1_1.ec
```
