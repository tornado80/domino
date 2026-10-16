# Domino

Domino checks game-based cryptographic proofs written in the State-Separating Proofs (SSP) style.

## Language

**Assumption**:
A named claim `A: G0 ~ G1` that two game instances are indistinguishable. A **Reduction** cites exactly one assumption by name.
_Avoid_: axiom (unless it is a base assumption)

**Base assumption**:
An assumption without a mark. The theorem does not prove it. It is trusted as given, and it is listed in the summary of trusted assumptions after each proof.
_Avoid_: explicit assumption, primitive assumption

**Derived assumption**:
An assumption marked `derived`. It is a proof obligation: it is usable by a reduction only after it is **Established** by a path between its two games.
_Avoid_: modular assumption, discharged assumption

**Established**:
An assumption is established if it is a base assumption, or if there is a hop path between its two games where each reduction cites an assumption that was established earlier in the derivation. "Earlier" means earlier in the well-founded derivation, never earlier in the file. A cycle makes nothing established. Only hops and assumptions of the same theorem count; another theorem never establishes an assumption.

**Proposition**:
A named claim `P: G0 ~ G1` that the theorem must prove. It is accepted only when its hop path uses reductions that cite established assumptions. The name of a proposition has no link to the names of assumptions.

**Conjecture**:
A hop that the tool does not check. A result whose path uses a conjecture is established only modulo that conjecture.

## Relationships

- A **Reduction** cites one **Assumption**; the reduction is valid only if its per-hop check passes and the cited assumption is **Established**.
- A **Proposition** is proven by a path of hops (equivalences and reductions).

## Flagged ambiguities

- "Discharged" was used for both "proved by a path" and "not a base assumption". Use **Established** for the first meaning.
