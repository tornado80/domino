# Story 23 — The core claim set: debug without project lemmas

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 21 (`ClaimQuery` with parts, the check names); 19 (all-claim runs, `ClaimSet`).
**Blocks:** nothing. Independent of story 22.

---

## 1. Why this story exists

The owner said: *"I am now wondering whether assuming lemmata in lockstep execution for claims
causes an issue, because in EasyCrypt we don't translate lemmata and the proving depends on
debugging information. At least EasyCrypt listing lockstep execution should not assume lemmas, and
I would like to have an option for lockstep execution on the Domino listing to ignore lemmata, so
only proving same-output, equal-aborts, invariants as well as game and package invariants."*

Facts found during the grilling:

- **The EasyCrypt listing already assumes no project lemma.** `ClaimSet::NoDependencies`
  (`src/debug/lockstep_run.rs`) checks `equal-output` and `invariant`, both with no dependencies.
  The shared base frame (`shared_base_frame`, `driver.rs`) holds the randomness mapping,
  `invariant` on the old states, and the package and game invariants on the old states. It holds
  no lemma. Nothing locks this in with a test.
- **On the Domino listing, a claim is checked under its dependencies.** If the theorem says
  `invariant: [no-abort, my-lemma]`, then `my-lemma` is asserted before the negated `invariant`
  goal (`check_claim`, `claims.rs`). This is the same as `domino prove`. In a single-claim run
  the dependencies go into the base frame and prune.
- In the code, every claim name that does not start with `relation` or `invariant` has the type
  `Lemma` (`ClaimType::guess_from_name`, `src/theorem.rs`). This includes the built-in facts
  `same-output`, `equal-aborts` and `no-abort`. The glossary therefore uses **project lemma** for
  a lemma hand-written in the project.
- The sequential driver resolves its claims with its own copy of the `Obligations` rule
  (`run_debug_command`, `driver.rs`). Lockstep uses `ClaimSet::resolve`.

Vocabulary (`CONTEXT.md`): **Core claim set**, **Dependency**, **Project lemma**, **Check**,
**All-claim run**.

## 2. Inherited from earlier stories

- **Story 19 / ADR 0003:** the claims are independent of the strategy and of the listing.
  `ClaimSet` has `NoDependencies` (the EasyCrypt set) and `Obligations { only }`.
- **Story 21:** `ClaimQuery` carries its dependencies and its parts. `check_claim` checks the
  parts under the claim's dependencies.
- `false_by_terminals` (`claims.rs`) knows the four built-in dependencies: `no-abort`,
  `left-no-abort`, `right-no-abort`, `equal-aborts`.

## 3. Work to do

### 3.1 One claim resolver for both strategies

Move `ClaimSet` and its `resolve` from `lockstep_run.rs` to `src/debug/claims.rs`. The sequential
driver uses `ClaimSet::resolve` too, and its own copy of the `Obligations` rule is deleted.

### 3.2 `ClaimSet::Core`

Add a third value:

```rust
/// The core claim set: `equal-aborts`, `same-output`, `invariant`, and the generated package
/// and game invariant claims, each under its built-in dependencies only. Project lemmas and other
/// declared claims are neither checked nor assumed. Narrowed to one claim by name.
Core { only: Option<String> },
```

- The claims are the obligation set (`obligations()`) filtered to `equal-aborts`, `same-output`,
  `invariant`, and the claims from `generate_game_or_package_invariant_claims`. A declared claim
  with any other name (a project lemma, a `relation-…` claim) is left out.
- Each kept claim keeps only the dependencies that `false_by_terminals` knows (`no-abort`,
  `left-no-abort`, `right-no-abort`, `equal-aborts`). Every other dependency is removed.
- The parts of `invariant` (story 21) are the same as in the obligation set.
- `only: Some(name)` narrows inside the core set. A name outside it is `ClaimNotFound`, with the
  message "claim `<name>` is not in the core claim set" and the list of core claims.
- `ClaimSet::resolve` is the only place that knows this rule.

### 3.3 The CLI

`domino debug` gets `--claim-set <obligations|core>`, default `obligations`. Both strategies take
it. The help text: "Which claims to check. `obligations` (the default): every claim of the
proofstep, each under its declared dependencies, as `domino prove` does. `core`: only
`equal-aborts`, `same-output`, `invariant` and the package and game invariants, each under its
built-in dependencies only (`no-abort`, `equal-aborts`, …). Project lemmas are neither checked nor
assumed, as in EasyCrypt."

`domino easycrypt debug` does not get the flag. It always uses `NoDependencies`.

### 3.4 Where a core run writes

So that a core run never replaces an obligations run of the same oracle:

| Run | Directory below the oracle |
|---|---|
| all-claim, `obligations` | `!all-claims!` (as today) |
| all-claim, `core` | `!core-claims!` |
| one claim, `obligations` | `<claim>` (as today) |
| one claim, `core` | `<claim>!core!` |

Put the rule next to `ALL_CLAIMS_DIR` in `src/debug/layout.rs`. The viewers and the summaries say
which set was checked: "all 5 claims of the core claim set".

### 3.5 Lock in the EasyCrypt listing

Add a test: a synthetic project under `testdata/debug/story23/` whose `invariant` and
`same-output` depend on a project lemma `my-lemma`. Run EasyCrypt-mode lockstep execution on it
(`ClaimSet::NoDependencies`). Assert that neither the base frame nor any pair's goal blocks
contain `my-lemma`.

The same project serves §4: an oracle whose `invariant` is verified with `my-lemma` and fails
without it.

## 4. Acceptance criteria

- [ ] `ClaimSet` lives in `claims.rs`. Both strategies resolve their claims through it. The
      sequential copy of the rule is gone.
- [ ] On the story-23 project, `domino debug --claim-set core` (both strategies) checks exactly
      `equal-aborts`, `same-output`, `invariant` and the package and game invariant claims, and
      never asserts `my-lemma` (check the `smt/` files of a failing pair).
- [ ] On the same oracle, `--claim-set obligations` verifies `invariant`, and `--claim-set core`
      gives it goal-fails or inconclusive.
- [ ] `--claim-set core --claim my-lemma` stops with "claim `my-lemma` is not in the core claim
      set".
- [ ] A core run writes to `!core-claims!` (or `<claim>!core!`). An obligations run of the same
      oracle is still on disk after it.
- [ ] The EasyCrypt-listing test of §3.5 passes.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```sh
source ~/.cache/domino/cvc5-lib-env.sh
cargo build -p domino --features cvc5-lib
D=$PWD/target/debug/domino
cd testdata/debug/story23
$D debug --proof Eq --proofstep 0 --oracle O
$D debug --proof Eq --proofstep 0 --oracle O --claim-set core
$D debug --proof Eq --proofstep 0 --oracle O --claim-set core --lockstep
ls _build/debug/Eq/*/O/
grep -l my-lemma _build/debug/Eq/*/O/!core-claims!/*/smt/* ; echo "expect no file"
```

## 6. Rejected alternatives

- **A boolean flag `--no-project-lemmas` that each strategy filters with.** Rejected: the filter
  rule in two drivers, and the flag threaded through both (change amplification).
- **Use the EasyCrypt claim set (`NoDependencies`) on the Domino listing.** Rejected: it joins
  `equal-aborts` and `same-output` into one check, has no `no-abort` dependency, and has no
  separate package and game invariant checks. The owner asked for those as separate checks.
- **Lockstep only.** Rejected: ADR 0003 makes the claims independent of the strategy, and a
  sequential core run is a useful way to see what EasyCrypt can prove.

## 7. Notes / risks

- A core verdict is not EasyCrypt's verdict. The Domino listing still has `no-abort`, and
  EasyCrypt has no such dependency. The core set only removes what EasyCrypt surely does not
  have.

## 8. State handed to the next story

Record in `23-…-IMPLEMENTATION-REPORT.md`: where `ClaimSet` lives, the directory names, and the
verdicts of the story-23 project with each claim set.
