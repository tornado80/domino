# Package and game invariants are conjuncts of `inv`

**Status:** accepted. Implemented by `docs/stories/easycrypt/58-translate-package-and-game-invariants.md`.

Domino assumes every package invariant and every game invariant (`CONTEXT.md`) on the states
before each oracle call, on both sides. It proves each one on the new state as a separate claim,
with the dependency `no-abort`. Until story 58 the EasyCrypt translation skipped them, so the
EasyCrypt `inv` was weaker than what Domino assumes.

We now put them **inside `inv`**, under the same `!abort` guard as the invariant:

```
op inv (l : L_state) (r : R_state) : bool =
     params_inv l r
  /\ l.`l_abort_flag = r.`r_abort_flag
  /\ (!l.`l_abort_flag =>
        Domino_invariant l r /\ PkgInv_l_<Inst> l /\ … /\ GameInv_<L> l
                             /\ PkgInv_r_<Inst> r /\ … /\ GameInv_<R> r).
```

`PkgInv_<l|r>_<Inst>` is a one-line wrapper, ``PkgInv_<Pkg> l.`l_pkg_<Inst>``. The body of the
package invariant is translated one time, in `PkgInv_<Pkg>`, over `<Pkg>_pkgstate` (ADR 0007).
Each wrapper and each `GameInv_` operator stands for exactly one Domino claim.

So the one `call (: inv …)` assumes them on the old states and proves them on the new states, which
is exactly what Domino's SMT path does. The proof skeleton, the bullets and the base case do not
change. The tactics driver sees the new operators as more conjuncts on a leaf.

## Considered options

- **Separate `hoare` lemmas joined with `conseq`.** For each side and each oracle, generate
  `hoare[Exp_G.O : side_inv ==> side_inv]`. Then join them into the pRHL proof with
  `conseq (_: inv ==> inv) H_l H_r` (the EC-Tricks `01_conseq.ec` pattern for one-sided facts on an
  equiv). This is the usual EasyCrypt idiom. It is also more modular: a game invariant is proved
  one time per game instance, and every equivalence that contains that instance uses it again. It
  was rejected **for now** because it adds a new proof kind to the proof skeleton, the tactics driver
  (a one-sided walker), lockstep execution (one-sided verdicts), the session record and the live
  page. That is a lot of change amplification for a small gain: in the current projects, only one
  game instance with one-sided invariants is in two equivalences (`H6_1_1` of Full4WHS, in
  `H6_1_0 ~ H6_1_1` and `H6_1_1 ~ H7_0`).
  **Come back to this option** when a project uses one game instance with package or game
  invariants in many equivalences, or when the one-sided conjuncts make leaf goals too large for
  the tactics run.
- **No `!abort` guard on the new conjuncts.** Rejected. Domino proves them on the new state only
  under `no-abort`. After an abort, the state that the router keeps does not have to satisfy them.

## Consequences

- Every leaf goal now also contains the one-sided invariants of both sides. A leaf that EasyCrypt
  cannot close splits into more parts, and lockstep execution gives each part its own Domino
  verdict (story 58).
- The base case must show the one-sided invariants on the initial state. The existing
  `auto => />; smt(emptyE map_empty).` does this for the PRF invariant of 4WHS.
- A project whose one-sided invariant is false on the initial state now fails to compile in
  EasyCrypt at the base case. Domino rejects such a project too, with its initial-state check.
