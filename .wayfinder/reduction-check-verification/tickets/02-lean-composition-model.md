---
title: Lean data model of SSP compositions
type: wayfinder:grilling
status: open
assignee: Amir Rajabi
blocked_by: []
---

## Question

How do we represent, in Lean, the objects that the reduction check reads: package (opaque, with
name, parameters, imported and exported oracle signatures), package instance, composition
(instances, edges, exports), game instance (with resolved parameters), and the assumption mapping
of package instances? Which equality is "equal up to the mapping" (renaming of instances, export
aliases, parameter values)? The output is a list of Lean definitions in outline (no proofs), with
each choice explained against the Rust types in `src/` (`Composition`, `PackageInstance`,
`Edge`, `Export`, `ReductionMapping`).

## Progress (grilling in progress, not resolved)

The ticket is still open and claimed. The grilling stopped after two answers. Continue with the
pending question below.

### Facts from the Rust code

- `Composition` (`src/package.rs`) has `pkgs: Vec<PackageInstance>`, `edges: Vec<Edge>` and
  `exports: Vec<Export>`. Edges and exports point to instances by their index in `pkgs`.
- `Edge { from, to, sig, alias }`: `alias` is the **import name** (`f` in `f: O1 of x`), and
  `sig.name` is the **destination oracle** (`O1`). `Edge::name()` gives the import name. Without an
  alias, the two names are the same.
- `Export { to, sig, alias }`: `alias` is the name that the adversary sees, and `sig.name` is the
  oracle of the instance.
- `PackageInstance` has `pkg` and `params: Vec<(PackageConstIdentifier, Expression)>`.
  `package_instances_diff` compares the parameter expressions after it resolves game constants and
  redacts game information.
- `GameInstance { name, game, types, consts }`.
- The Rust types do not contain the rule "one edge for each import" (W1 in the bug corpus).

### Decisions so far

1. **Two layers for wiring.** A raw layer copies Rust (lists of edges and exports, `Nat` indices),
   for the refinement proof. A wired layer represents the wiring as a function, so W1 holds by
   construction. A lemma: `RawComp.WellFormed → ∃ wired composition`. The theorem is stated on the
   wired layer.

   ```lean
   structure RawEdge where
     src : Nat; imp : ImportName
     dst : Nat; oracle : OracleName
   structure RawComp where
     insts   : List Inst
     edges   : List RawEdge
     exports : List RawExport
   def RawComp.WellFormed : RawComp → Prop

   structure Comp where
     ι      : Type
     [fin : Fintype ι] [deq : DecidableEq ι]
     inst   : ι → Inst
     wire   : (i : ι) → imports (inst i) → ι × OracleName
     export : ExportName → Option (ι × OracleName)
   ```

2. **Parameters are opaque values.** An instance is a package and a parameter assignment to an
   abstract type `Val` with decidable equality. The theorem is generic in `Val`. The Rust side must
   only prove the sound direction: "the redacted expressions are syntactically equal → the values are
   equal". This is the boundary of trusted instantiation.

   ```lean
   variable (PkgName ParamName Val : Type) [DecidableEq PkgName] [DecidableEq Val]
   structure Pkg where
     name    : PkgName
     imports : Finset ImportName
     oracles : Finset OracleName
   structure Inst where
     pkg  : Pkg
     args : ParamName → Option Val
   ```

### Pending question (the user wanted to clarify it first)

**How does the model represent the context R (a composition with open imports) and R ∘ A?**

- Option A, *open composition* (my recommendation): R is an `OpenComp I`. Its wires go to an
  internal instance or to a name of the assumption's export interface `I`. `R ∘ A` is a closed `Comp`
  with instance type `R.ι ⊕ A.ι`. The theorem says `∃ R : OpenComp I`, and R1, X1 and X2 follow from
  "the same R on both sides".
- Option B, *partition view*: there is no separate R. A construction game is a `Comp` with a
  partition into context and mapped part (an embedding `m : A.ι ↪ C.ι` that is closed downwards). The
  theorem lists the conditions directly. This is closer to the check, but R1 and X2 must be written by
  hand.

Start the next session with: "What do you want to clarify about this question?"

### Questions after that (not asked yet)

1. Instance identity: an abstract `Fintype ι`, or `Fin n` like the Rust indices? Are instance names in
   the model (only for diagnostics), or not?
2. Name types: are `ImportName`, `OracleName` and `ExportName` abstract types with decidable
   equality, or `String`?
3. Oracle signatures: does the model contain argument and return types, or are they a function of
   package and parameters (so E1 "matching signatures" follows from equal packages)?
4. The assumption interface `I`: export names with signatures. Is "`A_L` and `A_R` have the same
   interface" a hypothesis, or a condition that the check must test?
5. "Equal up to the mapping": the definition of composition isomorphism (a bijection on instances that
   keeps `inst`, `wire` and `export`). Must export names be equal (yes, they are the adversary
   interface), and must import names be equal (they follow from the package)?
6. Hybrid reductions: how do construction instances such as `inst$bit$` and parameters with a free loop
   variable appear? Is it enough that `Val` contains symbolic values, or does the model need a family of
   compositions indexed by the loop variable?
7. Raw layer: the shape of `RawExport`, and the full list of conditions in `RawComp.WellFormed`
   (W1, indices in range, unique export names, the destination instance has the oracle).
8. Lean setup for the model: Mathlib dependency (for `Fintype`, `Equiv`, `Finset`), Lean version.
