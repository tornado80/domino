# A reduction is a router, an adversary and an experiment

**Status:** accepted. Implemented by `docs/stories/easycrypt/97-…` to `100-…`. Grilling of
2026-11-04/05, Questions 1 to 7.

Translation skips reduction hops until now. A reduction maps the packages of an assumption game to
packages of the hop's game instance; the other packages are the reduction packages. We want to reuse
the translated packages and compose them, and not inline them into one adversary.

We decided:

1. **Two modules for each reduction.** The **reduction router** `Red_<hop>(O : Iface_<Assm>)` has
   the hop's game interface. It is built from clones of the reduction packages, with the same import
   adapters and the same abort-flag wrapping as a composition's `Game_<C>`. A call that reaches a
   mapped package goes to `O`. It has its own abort flag, because a reduction package can abort while
   the assumption game does not. The **reduction adversary** `B_<hop>(A)(O)` starts the router and
   runs `A(Red_<hop>(O))`.
2. **No hypothesis on the start memory.** An EasyCrypt adversary's `run()` has no arguments, and a
   module cannot read a lemma argument. So the theorem constants that the reduction packages need
   (booleans and integers that are not widths) go through a **reduction experiment**
   `RedExp_<hop>(A).run(consts..)`. It calls `B_<hop>(A).setup(consts..)`, which stores them in
   `B_<hop>`, and then runs the assumption game's own `Exp_<Assm>(B_<hop>(A))`, unchanged. The
   reduction's lemmas quantify the constants as lemma arguments, as the equivalence lemmas do.
3. **Every reduction has a reduction experiment**, also when it needs no constants, so the
   proposition lemma treats all reductions the same. When the two assumption games are different
   compositions, there is one reduction experiment for each side.

4. **Translation writes the whole proof of the reduction equivalences** (`Exp_<G>(A)` against
   `RedExp_<hop>(A)` for each side), with no `admit`. The code on the two sides is the same package
   code under other module names, and Domino's reduction check already proved that the mapped part
   is the assumption game. So the invariant comes from the map: equal package states, equal abort
   flags of the hop's game and the router, the assumption game's abort flag implies the router's,
   and the constants stored in the adversary equal the game's. No hand-written SMT-LIB and no proof
   job. A proof that EasyCrypt does not accept is a translation bug. A hand-written prototype on
   hello-world and on the first kem-dem reduction fixes the script before translation generates it.

5. **Two reduction equivalences, one for each side**, with the game instances' own arguments
   (theorem constants that stay free are lemma arguments). Their oracle lemmas mention no constant
   value, so the two sides share them when they use the same compositions.
6. **The bound lemma states equality** of the two advantages, as EasyCrypt's `elgamal.ec`
   `conclusion` does. Only the **proposition lemma** uses `<=`: the sum of the bound lemmas' right
   sides, one term for each reduction step in path order, each term in its hop's own direction so it
   is literally that bound lemma's right side.

7. **A hop that translation does not prove** (a conjecture, or an equivalence that translation does
   not write) gives its own term to the proposition lemma: the original adversary's advantage
   between the hop's two game instances. No axiom; the bound stays true and shows the open hop. The
   export report lists these hops. **Hybrid hops are out of scope** (owner's decision of
   2026-11-05): a proposition whose path has a hybrid hop gets no proposition lemma, and the report
   says so. A hybrid's game instances can keep the hybrid index free, so the term is not always an
   experiment with theorem constants only; a later design decides how hybrids translate.

8. **File names have no theorem prefix.** Each theorem already has its own directory. A reduction
   is one file, `Red_<L>_<R>.ec`, with all its modules and lemmas: no proof job owns a part of it,
   so the one-file-per-oracle rule of ADR 0013 does not apply. A proposition is `Prop_<Name>.ec`.
   If two theorems must load together, each theorem directory gets a named EasyCrypt load path
   (`-I Name:dir`, `from Name require ..`), which covers every file and not only the hop files.

## Considered options

- **One module, with the router nested in the adversary.** Most local, but one module has two jobs,
  the state names become longer, and the router does not reuse the composition seam.
- **Cryptobox style, no adversary.** The lemmas talk about `A(Red(Game_<Assm>))`. The bound is then
  not stated on the assumption game's own experiment, and each hop needs a new experiment.
- **A variable of the adversary with a memory hypothesis** (`B_h.b{m} = b => ..`), as Cryptobox's
  `lemma Security` does for its start state. Every proposition lemma then carries the reductions'
  configuration as hypotheses.
- **Theorem constants as abstract `op`s.** This changes every experiment and equivalence lemma, and
  one proposition cannot specialize a fixed `op` to both `false` and `true`.
- **The reduction experiment calls the router's `init` itself.** It must name a concrete assumption
  game for the functor argument and know how the router uses its constants.
- **Literals only.** This blocks 4WHS, where `Hybrid2` gives the theorem constant `b` to the
  reduction packages.
- **Prove the reduction equivalences with proof jobs and lockstep execution.** This reuses the
  tools, but they are made for real code differences; here they would walk equal code, slowly, and
  every lockstep change could break a reduction.
- **Admit the reduction equivalences.** The fastest full chain, but it leaves a hole in a step that
  Domino has already discharged.
- **One reduction equivalence by anti-unification** of the two sides' arguments. Closer to the
  equivalence lemmas, but it needs an algorithm and a fallback, and no caller needs the general form.
- **A chain of lemmas for each path position.** More lemmas for a generated proof, with no gain.
- **Assumptions as axioms with an epsilon.** An axiom over every adversary with no resource bound is
  false in EasyCrypt.
- **An axiom for each conjecture** (equal probabilities). Not sound if the conjecture is false.
- **No proposition lemma when the path has an open hop.** Safe, but nothing for a theorem with one
  conjecture, and a status that the user must read and act on. Hybrid hops get this behaviour only
  because they are out of scope.
- **The theorem name as a prefix of the hop files.** It renames the equivalence files, which session
  records, saved trees, progress keys and tests use, and it does not stop `Types.ec` or `Comp_*.ec`
  from clashing between theorems.
