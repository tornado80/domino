---
status: accepted
---

# Derived assumptions are opt-in (`derived`), and every proof prints its trusted assumptions

A theorem's `assumptions` block can contain claims that the same theorem also proves (for example `KSEarly` in the simple-binding `Main`). The tool did not check that a reduction cites only claims that are proved without circularity. We decided: an unmarked assumption is a **base assumption** (trusted, as before), and an assumption marked `derived` is a proof obligation that the tool must **establish** by a least-fixpoint over the theorem's hops (a reduction is an edge only when its cited assumption is already established). Cycles and missing paths are a hard load error that lists all failures together. Because the default is fail-open (a forgotten `derived` silently trusts the claim), every proof prints a summary of the base assumptions it depends on, in the same way as Lean `#print axioms`, Coq `Print Assumptions` and Isabelle `thm_oracles`. Do not "fix" the default to fail-closed without a migration plan for existing projects.

## Considered Options

- **`base` keyword with fail-closed default** (unmarked = obligation). Safest, but every existing `.ssp` file (44 in this repo, plus user projects) must change. Rejected by the project owner in favor of no change to existing files.
- **Legacy mode** (strict only if any `base` mark is present). Rejected: the meaning of one entry depends on a hidden mode set by other entries.
- **Infer derived assumptions** from matching propositions, or treat "no path found" as base. Rejected: a typo or a failed proof silently becomes an axiom.
- **A reduction cites a proposition by name, or resolves its claim by games only.** Rejected: the owner wants all claims in the `assumptions` block.
- **Establish assumptions across theorems.** Rejected: it needs game-instance matching between theorem files. The scope is one theorem.

## Consequences

- The summary is the only guard against a forgotten `derived`. It must always be shown, before SMT work starts, and it must not be behind a flag.
- "Earlier" in a derivation means an earlier fixpoint round, never an earlier position in the file. The order of hops and blocks has no effect.
