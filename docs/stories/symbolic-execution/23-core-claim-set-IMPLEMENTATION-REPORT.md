# Story 23 — Implementation report: the core claim set

`domino debug` has a new option, `--claim-set <obligations|core>`. Both strategies take it. A core
run checks only `equal-aborts`, `same-output`, `invariant` and the package and game invariant
claims. Each claim keeps only its built-in dependencies. A core run does not check or assume
project lemmas.

## What changed

### One claim resolver (`src/debug/claims.rs`)

- `ClaimSet` and `ResolvedClaims` moved here from `lockstep_run.rs`. `ClaimSet` is now `pub`.
  `lockstep_run` re-exports it.
- `ClaimSet` has a third value, `Core { only }`.
- `ClaimSet::resolve` is the only place that knows which claims a set holds. Both strategies
  call it. The copy of the `Obligations` rule in `run_debug_command` is removed.
- `ResolvedClaims` has two new fields:
  - `claims`: the declared claims, with the dependencies they keep. The sequential driver needs
    them for the base frame and the checks. It is empty for `NoDependencies`.
  - `label`: the directory below the oracle.
- `core_claims(obligations, generated)` is the core filter. It keeps a dependency only if
  `false_by_terminals` knows it (`is_built_in_dependency`). The parts of `invariant` come from
  `ClaimQuery::of`, as for the obligation set.
- `ClaimSet::of(core, only)`, `only()`, `is_core()` and `dir()` are helpers for the CLI and the
  drivers.
- The EasyCrypt checks are built by `lockstep_run::easycrypt_queries`. `resolve` calls it for
  `NoDependencies`. The function stays in `lockstep_run.rs` because it uses the EasyCrypt
  `inv` operator names.

### API

- `run_debug_command` and `run_lockstep_domino` take `claim_set: ClaimSet`. Before, they took
  `claim: Option<&str>`.
- `DebugError::ClaimNotFound` has a new field, `core: bool`. With `core`, the message is
  "claim `<name>` is not in the core claim set (core claims: …)".
- `DebugRun` and `LockstepMeta` have a new field, `core: bool` (`#[serde(default)]`).

### Directories (`src/debug/layout.rs`)

- `CORE_CLAIMS_DIR = "!core-claims!"`, next to `ALL_CLAIMS_DIR`.
- `claim_dir(claim, core)` gives the directory: `!all-claims!`, `!core-claims!`, `<claim>` or
  `<claim>!core!`.

### Summaries and viewer

- `report::all_claims_line` is shared by both summaries. It gives "all 5 claims of the core
  claim set" for a core all-claim run.
- A sequential single-claim core run says "invariant (core claim set)".
- The lockstep viewer header says "all claims of the core claim set".

### CLI (`crates/domino/src/cli.rs`, `main.rs`)

- `--claim-set <obligations|core>`, default `obligations`, with the help text of §3.3.
- `domino easycrypt debug` does not get the flag. It always uses `NoDependencies`.

### Test data

`testdata/debug/story23/`: theorem `Eq`, proofstep 0, oracle `O`.

- Left: `ctr <- x`. Right: `ctr <- x` only if `x > 0`.
- `invariant` is `left.p.ctr = right.p.ctr`.
- `my-lemma` is `x > 0`. `invariant` and `same-output` depend on `[no-abort, my-lemma]`.
- Package `A` (left) has a package invariant and game `GL` has a game invariant, so the run
  has generated claims.

## Verdicts on the story-23 project

| Run | equal-aborts | same-output | invariant | my-lemma | package-invariant!gl-p! | game-invariant!gl! |
|---|---|---|---|---|---|---|
| obligations (both strategies) | 2 verified | 1 verified, 1 unreachable (dependency) | 1 verified, 1 unreachable (dependency) | 1 verified, 1 GOAL FAILS | 2 verified | 2 verified |
| core (both strategies) | 2 verified | 2 verified | 1 verified, 1 GOAL FAILS | not in the set | 2 verified | 2 verified |
| `--claim invariant` (obligations) | | | 1 verified, 1 unreachable | | | |

`my-lemma` is not provable alone (`x > 0`), so the obligations run fails on it. This is
intentional: the lemma is necessary for `invariant`.

`--claim-set core --claim my-lemma` stops with: "claim `my-lemma` is not in the core claim set
(core claims: equal-aborts, same-output, invariant, package-invariant!gl-p!,
game-invariant!gl!)".

## Difference from the story

§5 says `grep -l my-lemma …/!core-claims!/*/smt/*` gives no file. It gives files, because the
lemma is in a theorem invariant file and its `define-fun` is in the base declarations of every
run. No line asserts it. The tests check this: every line that names
`relation-my-lemma` is a `(define-fun`. To check by hand, use
`grep -n relation-my-lemma …/smt/*` and see that only the `define-fun` line shows.

## Tests

- `claims.rs` (no solver): `the_core_set_keeps_the_core_claims_with_their_built_in_dependencies_only`,
  `a_name_outside_the_core_set_is_not_found_in_it`, `a_set_names_its_directory`.
- `lockstep_run.rs` (cvc5-lib), on the story-23 project:
  - `the_easycrypt_listing_assumes_no_project_lemma` (§3.5).
  - `a_lockstep_core_run_checks_the_core_claims_without_the_project_lemma`.
  - `a_sequential_core_run_checks_the_core_claims_without_the_project_lemma` (also the
    obligations verdict of `invariant`).
  - `with_the_obligation_set_invariant_holds_under_the_project_lemma`.
  - `a_project_lemma_is_not_in_the_core_claim_set`.

Results:

- `cargo test --workspace`: sspverif lib 672 passed, 5 ignored. All other suites pass.
- `cargo test --workspace --features domino/cvc5-lib`: sspverif lib 782 passed, 6 ignored. All
  other suites pass.
- `cargo clippy --workspace --all-targets`, with and without the feature: no warnings.

## State for the next story

- `ClaimSet` is in `src/debug/claims.rs`. To add a claim set, add a value there and its rule
  in `resolve`.
- Directory names: `!all-claims!`, `!core-claims!`, `<claim>`, `<claim>!core!`
  (`layout::claim_dir`).
- The debug index shows a core run with its directory name in the claim column. It has no
  separate claim-set column.
