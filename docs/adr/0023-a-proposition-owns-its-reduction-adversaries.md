# A proposition owns its reduction adversaries, and a proof job proves the reduction's oracles

**Status:** accepted. Supersedes ADR 0022 decisions 2, 3, 4, 5 and 8, the part of decision 1 about
the reduction adversary, and its rejection of "one reduction equivalence by anti-unification".
Implemented by `docs/stories/easycrypt/epic-reductions-without-an-experiment.md` (stories 101 to
103). Grilling of 2026-11-10/11, Decisions 1 to 9. Decision 5 ("with the blind walk") is
superseded by ADR 0024.

ADR 0022 gave each reduction a **reduction experiment** `RedExp_<hop>(A).run(consts..)`, because an
EasyCrypt adversary cannot read a lemma argument. Its bound lemma is therefore not stated on the
assumption game's own experiment, and the reduction's oracle proofs are long generated tactic
ladders that nobody can read. The hand-written `_Lotta` files of Full4WHS show a better shape: one
adversary for each set of values, with `Exp_<G>(A) = Exp_<Assm>(B(A))`, and short proofs that show
each program step.

We decided:

1. **The values come from the proposition paths.** A reduction adversary fixes the values of the
   theorem constants that the reduction packages read. A hop whose reduction packages read no free
   theorem constant has one adversary. Otherwise it has one adversary for each different set of
   values that a proposition step gives to these constants. A path that leaves such a constant free
   makes the hop an **open hop** of that proposition (ADR 0022 decision 7). A hop that no
   proposition uses has no adversary, no equivalence lemma and no bound lemma. The reduction
   experiment, `setup`, and the invariant conjunct "a constant stored in `B` equals the game's copy"
   are removed.
2. **The reduction's files hold only what is generic.** The oracle lemmas and the **run lemma**
   `equiv[A(Game_<G>).run ~ A(Red_<hop>(Game_<Assm>)).run : ={glob A} /\ inv ==> ={res} /\ inv]`
   hold for all values of the reduction parameters. The invariant relates the parameters only
   through equal package states, because `init` stores them in the package state. The run lemma is
   the only lemma of a reduction that a proposition names.
3. **The proposition file holds what is concrete:** the reduction adversaries
   `B_<L>_<R><s>(A)(O)`, which start the router with literal values and run `A` against it, the
   equivalence lemmas `equiv_<L>_<R><s>`, and the bound lemmas `bound_<L>_<R><s>`. The suffix `<s>`
   is `_<const>_<value>` for each constant that the reduction packages read, in theorem order. A
   negative integer is written `neg<n>`. The run lemma is `run_<L>_<R>`, or `run_<L>_<R>_L` and
   `_R` when the two sides use different compositions.
4. **One equivalence lemma covers both sides when that is safe.** The run arguments are flat tuples
   of literals, so Plotkin's anti-unification is a short loop: each pair of values that differ
   between the two sides gets one binder, and a game position and an assumption position with the
   same pair share it. Translation merges the two sides when both sides use the same game
   composition and the same assumption composition, and the set of the game's differing pairs equals
   the set of the assumption's differing pairs. Otherwise it writes `_L` and `_R` lemmas with
   literals.
5. **A proof job proves the reduction's oracle lemmas with the blind walk** of the proving algorithm
   (`docs/proving-algorithm.md`). The walk reads the goals from EasyCrypt (ADR 0002), so it knows
   the `sp` counts and the inlined names. It writes `sp`, `if`, `rcondt`/`rcondf` and `seq` steps,
   as the `_Lotta` proofs do. After `export`, each oracle lemma has an `admit` until `prove` runs.
   Translation still writes the run lemma, the equivalence lemmas, the bound lemmas and the
   proposition lemma in full.
6. **Files follow the equivalence layout of ADR 0013.** `Red_<L>_<R>_Router.ec` holds the clones,
   the router and `inv_<L>_<R>`. `Red_<L>_<R>_<O>.ec` holds one oracle lemma. `Red_<L>_<R>.ec` joins
   them in the run lemma and is the file that a proposition loads. The ADR 0013 name rule rejects an
   oracle called `Router`.
7. **A reduction hop is a game hop for `prove`.** `--gamehop`, `--oracle`, `--jobs`, resume and a
   fresh start work as they do for equivalences, with `session/Red_<L>_<R>/` and
   `progress/Red_<L>_<R>/`. The job runs no lockstep execution, no solver and waits for no
   side-invariant file.

## Considered options

- **Enumerate all `2^k` values of the free constants.** Many unused adversaries, and integers have
  no finite set of values.
- **A section `declare op` for each constant.** EasyCrypt refuses it: "module B cannot depend on
  declared operator c".
- **An abstract `op` for each constant** and **a reduction experiment only for free constants.**
  Rejected again for the reasons of ADR 0022, and the second keeps two shapes.
- **Only the oracle lemmas in the reduction's files.** Each equivalence proof in the proposition
  file must then write the invariant with its clones and one `conseq` for each oracle: the state
  leaks out of its owner.
- **The run lemma in the proposition file.** The same leak.
- **Translation writes the blind walk itself.** It must predict EasyCrypt's inlining, positions and
  names, which ADR 0002 rejects. A test showed that a bare `sp` goes through `if` statements, so the
  counts are necessary.
- **Keep the tactic ladder and make it shorter.** It stays a blind search and does not become
  readable.
- **Full lockstep execution.** It needs a synthetic right composition and an SMT invariant, and the
  assumption game's extra abort guards break the alignment.
- **Also merge a negated Boolean** (`run(.., !b)`). No such hop was found, and it was not tested.
- **Never merge.** Twice the lemmas, and not the `_Lotta` shape.
- **The reduction keeps the plain file name** (`Red_<L>_<R>.ec` for the router, `_Run.ec` for the
  run lemma). The plain name would then mean another thing than for equivalences.
- **Number the adversaries** (`_1`, `_2`). The number does not show the values and changes with the
  path. `real`/`ideal` suffixes need a meaning that translation does not know.
- **A separate `--reduction` flag** for the proof job. A second way to select work, and propositions
  keep `admit`s with no hint why.

## Consequences

- `export` is no longer complete for reductions: a reduction's oracle files have `admit`s until
  `prove` runs. The export's overwrite guard (ADR 0004) must also protect proved `Red_*` oracle
  files.
- The proposition writer owns the merge rule and the names. The reduction writer exports only the
  run lemma's name.
- The walk admits a step that it cannot close (`program-mismatch`), and a loop in a package stops
  it.
- Two propositions that use the same hop with the same values each define their own adversary.
