# Story 72 — Claim kinds come from declarations, never from a name

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 71.
**Blocks:** 73, 74.
**Decisions:** grilling of 2026-10-12/20, Questions 2 and 7.

A **Domino core** story: the SMT writer, the prover, the debugger and the EasyCrypt translation all
read the result. Rust only.

---

## 1. Why this story exists

A claim or dependency name stands for one of a few kinds of thing. Today the kind is guessed from
the spelling (`ClaimType::guess_from_name`, `src/theorem.rs:221`): a name that starts with
`relation` is a state relation, one that starts with `invariant` is the invariant, and anything else
is a lemma. The guess runs in three places: `Claim::from_tuple` (`src/theorem.rs:243`), the
dependency calls in `emit.rs:389`, and a test helper in `src/debug/claims.rs:570`.

So a misspelled relation (`relaton-keys`) silently becomes a project lemma, and the solver gets a
call to a function that does not exist, or a wrong kind. The prover, the debugger and the EasyCrypt
translation can each get a different answer.

The invariant files already say what each name is: `define-state-relation`, `define-lemma`,
`define-package-invariant <name>` and `define-game-invariant <name>` (on `main`, story 71).
Verification tools such as Dafny and Boogie resolve a name's kind from its declaration, never from
a naming convention.

Christoph Egger's stack has a `resolve_claims` that reads the kind from the parsed statements, but
falls back to the guess. The stack is not merged (Question 7), so this story does the resolution on
our branch, in the same place.

Vocabulary (`CONTEXT.md`, already updated): **Claim kind**, **Dependency**, **Project lemma**.

## 2. Inherited

- `EquivalenceContext::load_invariants` (`src/gamehops/equivalence/mod.rs:233`) parses the invariant
  files into `SmtStmt`s with a `SmtStatementKind` (story 71).
- `Claim { name, ty, dependencies, admitted }` (`src/theorem.rs`), with `ty` from the guess.
- Consumers of `ClaimType`: `src/debug/claims.rs`, `src/debug/lockstep_run.rs`,
  `src/debug/side_run.rs`, `src/writers/smt/contexts/equivalence/emit.rs`,
  `src/parser/tests/complete/mod.rs`.

## 3. Work to do

### 3.1 The closed set of kinds

```
enum ClaimKind {
    BuiltIn(BuiltInFact),          // no-abort, left-no-abort, right-no-abort, equal-aborts, same-output
    StateRelation,                 // define-state-relation (the invariant is one of them)
    ProjectLemma,                  // define-lemma
    PackageInvariant { .. },       // generated: name, owner, instance, side
    GameInvariant { .. },          // generated: name, owner, side
}
```

`BuiltInFact` is an enum, not a lemma with a string. The names of the built-in facts are the ones on
`main` today; `left-no-abort` and `right-no-abort` stay (Question 7).

### 3.2 One resolution, at load

- The parsed `Claim` has no kind. Remove `ty` from `Claim`, and remove `ClaimType` and
  `guess_from_name` from `src/theorem.rs`.
- `EquivalenceContext::resolve_claims` runs right after `load_invariants`. For each claim and each
  dependency of each oracle's proof tree, it finds the kind: a built-in name, or a statement of the
  parsed files with that name. It stores `ResolvedClaim { name, kind, dependencies:
  Vec<ResolvedDependency>, admitted }`.
- **A name that resolves to nothing is a load error**, and so is a claim or a dependency that names a
  plain `define-fun` (a helper). The error gives the proofstep, the oracle, the claim and the name,
  and the nearest declared name when one is close (edit distance), for example:
  `claim relaton-keys of oracle Send1 in proofstep 3 is not declared; did you mean relation-keys?`
- The generated package-invariant and game-invariant claims are built with their kind; they never go
  through a name lookup.

### 3.3 Consumers read only resolved claims

- `emit.rs` builds each call from `kind` (the `match` at `emit.rs:389` uses the resolved kind).
- `verify_fn.rs` iterates resolved claims.
- The debugger (`claims.rs`, `lockstep_run.rs`, `side_run.rs`) takes resolved claims from the
  context. The test helper `declared` in `claims.rs` builds a `ResolvedClaim` with an explicit kind.
- The EasyCrypt translation reads state relations by kind, not by spelling.

### 3.4 Rejected alternatives

- **Each consumer resolves lazily** (`read_from_smt(name, stmts)` where it needs a kind, no load
  error). Each consumer would need the parsed statements: state escapes its owner, four call sites
  change for each new kind, and a misspelling shows only in the consumer that looks first.
- **The kind in the proof syntax** (`relation foo`): changes the language for something that the
  SMT file already says.
- **Keep the guess as a fallback** (the stack's shape): the misspelling stays silent.

## 4. Acceptance criteria

- [ ] `rg guess_from_name src` and `rg 'enum ClaimType' src` find nothing.
- [ ] A test: a proof that names `relaton-keys` while the file defines `relation-keys` fails at load
      with the error of §3.2, including the suggestion.
- [ ] A test: a claim that names a helper (`define-fun`) fails at load.
- [ ] A test: `equal-aborts`, `no-abort`, `left-no-abort`, `right-no-abort` and `same-output` resolve
      to `BuiltIn`, `invariant` to `StateRelation`, and a `define-lemma` to `ProjectLemma`.
- [ ] Every known-good example project proves as before, and the debugger's verdicts on 4WHS
      Simple4WHS do not change.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cargo test --workspace claim
cd example-projects/4WHS && $D prove --proof Simple4WHS
```
