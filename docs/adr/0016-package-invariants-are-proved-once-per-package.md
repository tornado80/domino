# Package invariants are proved once for each package, over any environment

**Status:** accepted. Partly supersedes ADR 0014: it replaces how package invariants are proved, and
it adds start lemmas. ADR 0014 stays the decision for game invariants. Implemented by
`docs/stories/easycrypt/76-package-lemmas-and-the-package-invariant-job.md` and
`docs/stories/easycrypt/77-side-invariants-from-package-lemmas.md`. Grilling of 2026-10-12/20,
Questions 4, 6, 11 and 12.

ADR 0014 proves the package invariants of a composition inside `SideInv_<C>_<O>`, so a package that
is in many compositions is proved again in each one. Branch `amir/check-package-invariants-once`
(PR 426) already checks each package invariant one time with the solver. A package declares its
imports as a module type (`<Variant>_Imports`, ADR 0001), packages do not share state, and EasyCrypt
can quantify over a module of a module type with a memory restriction, as it does for adversaries
(`declare module O <: Orcl {-Count}`, `easycrypt/theories/encryption/Indist.ec:112`).

We decided:

1. **A package-invariant lemma for each oracle of each package variant.** In a section,
   `declare module I <: <Variant>_Imports {-<Variant>}`, the lemma is
   `hoare[<Variant>(I).<O> : PkgInv_… ==> res <> None => PkgInv_…]`, one conjunct for each named
   invariant. At each import call the proof uses `call (_: true)`: nothing is known about the
   imports, so the invariant holds for every environment. The proof follows the package tree
   (one-sided execution with open calls, ADR 0017).
2. **A frame lemma for each oracle of each package variant.** For any `I` and any
   `J : glob I -> bool` that every procedure of `I` keeps (`declare op`, `declare axiom`),
   `<Variant>(I).<O>` keeps `J`. It says nothing about the package's invariants, and its proof
   follows the program shape only: `auto` over the package's own statements, which cannot write
   `glob I`, and the axiom at each import call. It needs no Domino tree.
3. **`SideInv_<C>_<O>` keeps its statement, `side_inv_<C>`, but its package invariants come from
   lemmas.** Its proof goes bottom-up along the call graph, which is acyclic: the package-invariant
   lemma of each instance gives that instance's invariant, with `I` set to its real import provider;
   the frame lemma of a calling instance, with `J` set to the invariants of the instances it calls,
   carries them through its code. Only the game invariants are proved by walking the composition's
   oracle, and the side tree checks only them.
4. **Start lemmas.** For each package variant, `hoare[<Variant>(I).init : true ==> PkgInv_…]`. For each
   composition, `hoare[Game_<C>.init : true ==> GameInv_…]`. `inv` has no start lemma: the goal that
   `call (: inv /\ side_inv_L /\ side_inv_R); last first.` brings to the front in the main lemma
   already proves the start of `inv` and of both side invariants.
5. **A package-invariant job proves one package**: `domino easycrypt prove --pkg-inv <P>` proves the
   package-invariant, frame and start lemmas of every variant of `P`. A side-invariant job proves
   the game-invariant start lemma of its composition, never a package lemma, and does not start a
   composition whose package lemma files are missing. In a whole-theorem run the package jobs start
   first, each side-invariant job waits for the packages of its own composition, and proof jobs
   start at once.

## Considered options

- **One combined lemma with `call (_: J)`.** Fewer files, but `J` appears in every leaf goal of the
  Domino-guided proof, and the package tree does not know `J`.
- **Only the package-invariant lemma; `SideInv_<C>_<O>` walks each caller again to carry the
  invariants of the instances it calls.** No new lemma kind, but the caller's code is walked once for
  each composition, which is the repetition this ADR removes.
- **Keep ADR 0014 for package invariants; only Domino checks them once.** EasyCrypt would still prove
  them for each composition, and Domino would give no verdict for those admits, because PR 426 takes
  the package claims out of the composition's walk.
- **A side-invariant job that proves missing package lemmas itself.** Two compositions that share a
  package would both prove it, so two jobs would work on one oracle (against ADR 0013).
- **One job for each theorem in a fixed order.** No narrow rerun of one package or one oracle.
- **A separate ADR for the game-invariant start lemma.** Too small to pass the ADR test alone.

## Consequences

- A package used in many compositions is proved once in EasyCrypt, as it is in Domino.
- A frame lemma is needed only where an instance with an invariant is called through another
  package. The others are still written, because they cost no solver time and keep the rule simple.
- The exact form of the frame lemma when an import aborts (`res = None`) is settled in story 76,
  with an EasyCrypt test.
- `SideInv_` files from before the change are stale: they walk the package code.

## Implementation notes (story 77)

Three things the decision needs in EasyCrypt, found when `SideInv_<C>_<O>` was built from the
lemmas. They do not change the decision.

- **The lemmas must be about the instance's clone.** A composition clones a variant once for each
  instance, and a lemma about `<V>` says nothing about a clone. The lemma files of a variant form
  one chain of theories (`clone include` of the file before), and the composition clones the end
  of the chain, `PkgInv_<V>`, instead of `Pkg_<V>`. So any job that reads a composition needs the
  package lemma files: a job creates the missing ones as translation wrote them.
- **A caller without invariants has frame lemmas too** (`KX` over `PRF` in Full4WHS), and a
  package-invariant job for its package checks them.
- **`J` must be a function of `glob I`.** `glob` of an import adapter holds only the variables that
  its procedures use (`PRF.kid_` is not in `glob` of `KX`'s adapter), and EasyCrypt does not let a
  frame keep a predicate on another module that shares memory with `I`. So each adapter that a frame
  lemma can use has a procedure `ec_footprint` that reads every variable below the caller, and
  `J_<Y>_in_<X>` reads `Y`'s variables at their positions in `glob I`, which EasyCrypt orders by path.
