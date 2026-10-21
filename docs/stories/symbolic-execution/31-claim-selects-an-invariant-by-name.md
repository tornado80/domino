# Story 31 — `--claim` selects a package or game invariant by name in `domino prove`

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 30.
**Blocks:** nothing.
**ADR:** 0021.
**Decisions:** grilling of 2026-10-21/22, Questions 12 and 13.

A **prover** story, Rust only. Test-first.

---

## 1. Why this story exists

A package or a composition can declare several invariants, and each is a claim of its own
(`CONTEXT.md`). Today `domino prove --package P` always proves all of them. `--claim` "does not apply
to package invariants": `--package` accepts it and ignores it. The owner wants to choose one
invariant, with `--package` and with `--game` (story 30).

Today `--package` also accepts `--injective-randmap` and ignores it. A package has no randomness
mapping. A flag that is accepted and does nothing is an unknown unknown, so it is refused.

## 2. Inherited

- `Prove.claim` (`crates/domino/src/cli.rs`): on an equivalence, a wildcard pattern on the full claim
  name (`Wildcard::new`, `src/gamehops/equivalence/verify_fn.rs:102`).
- `PackageInvariantSmtDriver::verify_claim_group` (`src/package_invariant/verify.rs:167`): it checks
  every claim of `ctx.invariant_claims()`.
- `GameInvariantSmtDriver` (story 30).
- The declared names: `(define-package-invariant <name> …)`, `(define-game-invariant <name> …)`.

## 3. Work to do

- With `--package P` or `--game C`, `--claim <pattern>` is a **wildcard on the declared invariant
  names** of the owner: `--claim main`, `--claim 'nonce*'`. The full claim name
  (`package-invariant!<name>!<P>!`, `game-invariant!<name>!<C>!`) is not part of the interface. The
  driver that owns the names does the match; the CLI passes the pattern only.
- The filter applies to each claim group: to each oracle, and to the start (`--invariant-start`).
- For a game invariant check, the filter selects which game invariants are **proved**. All package
  and game invariants are still **assumed** on the old state, as before.
- No match is an error, before any solver work: "no invariant of `<owner>` matches `<pattern>`",
  with a `help` that lists the declared names. A run that checks zero claims must not say
  "verified".
- `--package` refuses `--injective-randmap` (clap `conflicts_with`).
- The help text of `--claim` says: "With `--package` or `--game`: a wildcard on the names of the
  owner's invariants. Otherwise: a wildcard on the names of the equivalence claims."
- Plain `domino prove` and `--proof/--proofstep` do not change: `--claim` there still matches the
  equivalence claim names, and the package-invariant section of plain `prove` is not filtered.
- Remove the refusal of `--claim` with `--game` that story 30 added.

## 4. Rejected alternatives

- **The full claim name, as on an equivalence** (Question 13): the inner `!…!` format becomes part of
  the interface, and the owner is typed two times.
- **An exact name only** (Question 13): not the same as `--claim` on an equivalence, which takes a
  wildcard.
- **No match proves nothing and reports success**, as `--claim` on an equivalence does now: a false
  green.
- **`--package` keeps accepting `--injective-randmap`:** a flag that does nothing.
- **A separate story for the `--package` refusal:** it is one `conflicts_with` next to the new code.

## 5. Tests first

- [ ] Red: a package fixture with two invariants (for example a copy of
      `test-projects/test-package-invariant-params` with a second, false invariant `bad`):
      `--package P --claim main` verifies and checks only `main`; `--claim bad` fails; no flag
      fails (as now).
- [ ] `--claim 'ma*'` matches `main`.
- [ ] `--package P --claim nope`: the error lists `main, bad`, and no solver runs.
- [ ] `--game C --claim <name>` on a composition with two game invariants checks only that one, and
      still assumes the other one on the old state (one test where the selected invariant is proved
      only with the other as an assumption).
- [ ] `--game S --invariant-start --claim main` checks only `main` at the start.
- [ ] clap refuses `--package P --injective-randmap`.
- [ ] `--proof T --claim <pattern>` behaves as before (an existing test, or a new one).

## 6. Acceptance criteria

- [ ] All tests of §5 green.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 7. How to verify

```bash
cd testdata/debug/se25
$D prove --game S --claim main      # O fails
$D prove --game S --claim nope      # error: the invariants of S are: main
$D prove --package P --injective-randmap   # refused by clap
```
