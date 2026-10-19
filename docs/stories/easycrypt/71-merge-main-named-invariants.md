# Story 71 — Merge `domino-repo/main`: named package and game invariants

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** nothing.
**Blocks:** 72, 73, symbolic-execution 26.
**Decisions:** grilling of 2026-10-12/20, Questions 1 and 7.

A **merge** story. It only makes the branch build and pass its tests, with the smallest changes that
the merge needs. It adds no feature. Stories 72 and 73 add the features.

---

## 1. Why this story exists

The owner wants three branches in `amir/easycrypt-export`, merged one at a time, each as its own
story (Question 1): `domino-repo/main`, then `amir/html-viewer` (symbolic-execution 26), then
`amir/check-package-invariants-once` (story 74).

Upstream `main` now has the named-invariant work (fetched 2026-10-19):

| Commit | What |
|---|---|
| `f1f22011` | allow multiple game/package invariants |
| `c2edd46c` | adapt examples |
| `b2e5fe28` | simplify the name of lemmas to `<lemma-name>-<oracle-name>` |
| `34176eb7`, `64b1e588`, `966b3301`, `47d7199c` | adapt test projects, example projects, macro, 4WHS |

The rest of Christoph Egger's stack (`275ead5d` "Resolve Claims" up to `c4be7374` "No more
invariant claim types are needed") is **not** merged. The owner called it not stable (Question 7).
So these do **not** come in: the CLI rename `proofstep` → `gamehop` and `proof` → `theorem`, the
removal of `left-no-abort` and `right-no-abort`, the UI rewrite, and the config struct. Claim
resolution without guessing is our own story 72.

`keks/ty-params` is not merged either. It now sits on the old stack (Question 8).

## 2. What `main` changes

- `(define-package-invariant <name> …)` and `(define-game-invariant <name> …)`: an invariant has a
  mandatory name, and one owner may declare several.
- `SmtStatementKind` carries names: `PackageInvariant { name, package, game }`,
  `GameInvariant { name, game }`, `StateRelation { name }`, `GeneralRelation { name, oracle }`.
- The SMT names include the invariant name: `package-invariant!<name>!<game>-<pkg>!`,
  `game-invariant!<name>!<game>!`, and a project lemma becomes `general-relation!<name>!<oracle>!`.
- `EquivalenceContext::load_invariants` appends left and right invariants separately
  (`append_left_invariants`, `append_right_invariants`).
- Every example and test project declares its invariants with the name `main`.

## 3. Work to do

### 3.1 The merge

`git merge domino-repo/main`. The conflicts (`git merge-tree`, 2026-10-19):

- `example-projects/4WHS/theorem/full/invariant-H7_1_1_0-H7_1_1_1.smt2`
- `src/gamehops/equivalence/smtrewrite.rs`
- `src/gamehops/equivalence/verify_fn.rs`
- `src/writers/smt/contexts/equivalence/emit.rs`

### 3.2 Rules for the resolution

- **One owner for each claim name stays** (symbolic-execution 25). HEAD has
  `package_invariant_claim_name(owner, pkg_inst)` and `game_invariant_claim_name(owner)`
  (`emit.rs:1711`), and `smtrewrite.rs` calls them. `main` builds the same names with
  `SmtStatementKind::name()`. Resolve this so that the two owner functions take the invariant name
  as well, `package_invariant_claim_name(name, owner, pkg_inst)` and
  `game_invariant_claim_name(name, owner)`, and so that `SmtStatementKind::name()` calls them. No
  second `format!` of these names may stay.
- **The debugger checks one claim for each named invariant.** The core claim set (symbolic-execution
  23), the all-claim run and the side tree (symbolic-execution 25) generate one package-invariant
  claim for each named invariant of each instance, and one game-invariant claim for each named game
  invariant.
- **EasyCrypt translation keeps one operator for each owner for now.** Where an owner has several
  named invariants, `PkgInv_<Pkg>`, `PkgInv_<C>_<Inst>` and `GameInv_<C>` are the conjunction of
  them. All projects have one invariant named `main`, so the output does not change. Story 73
  gives each name its own operator (ADR 0018).
- **Project lemma names.** Where the debugger or the EasyCrypt translation reads a project lemma by
  its SMT name, it uses `main`'s name (`<lemma-name>-<oracle-name>`). The core claim set leaves
  project lemmas out, as before.
- **Claim types still come from the old guess** (`ClaimType::guess_from_name`). Story 72 replaces
  it. Do not change it here.

### 3.3 Rejected alternatives

- **Merge the whole stack** (Question 7): not stable, and it changes the CLI and the built-in facts.
- **Wait until the stack is on `main`:** unknown wait; the named invariants are already on `main`.

## 4. Acceptance criteria

- [ ] `git log` shows one merge commit of `domino-repo/main` (`47d7199c` or later).
- [ ] `rg 'format!\("package-invariant!|format!\("game-invariant!' src` finds nothing outside the
      two owner functions.
- [ ] A test: a package with two named invariants gives two package-invariant claims in an
      all-claim run, named by the owner function.
- [ ] Translation of Full4WHS gives the same files as before the merge (all invariants are `main`).
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
- [ ] The known-good example projects prove as before (`domino prove`).

## 5. How to verify

```bash
cargo test --workspace
cd example-projects/4WHS && $D prove --proof Simple4WHS
$D easycrypt export --theorem Full4WHS --out /tmp/ec71 --force && diff -r /tmp/ec71 <export before>
```
