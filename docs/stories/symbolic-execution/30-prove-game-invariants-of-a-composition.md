# Story 30 — `domino prove --game C`: the game invariants of a composition, on their own

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 25, EasyCrypt 77, EasyCrypt 85.
**Blocks:** 31, 32.
**ADR:** 0021 (one-sided invariant checks name their owner, not a theorem); 0014, 0016.
**Decisions:** grilling of 2026-10-21/22, Questions 1–5, 10–12.

A **prover** story, Rust only. Test-first.

---

## 1. Why this story exists

`domino prove --package P` proves a package invariant on its own. A game invariant has no such
check: `domino prove` proves it only inside an equivalence, for the two game instances, with their
constants bound (`generate_game_invariant_claims`, `src/gamehops/equivalence/verify_fn.rs:290`).
The side-invariant lemma `SideInv_<C>_<O>` needs the stronger claim: for every value of C's
parameters (ADR 0014). Today the owner finds a false game invariant only when
`domino easycrypt prove --side-inv C` gives admits.

After this story:

```
domino prove --game C [--oracle O] [--invariant-start]
```

proves each game invariant of composition C, for every value of its parameters, with no theorem.

Vocabulary (`CONTEXT.md`, already updated): **Composition** (also *game*), **Game invariant** (and
its two strengths), **Package invariant**.

## 2. Inherited

- `src/debug/side_run.rs`: `free_theorem`, `free_params`, `copy_name`. The free composition `C` and
  its copy `C$side`, with each parameter a free theorem constant, and the `Equivalence` of the two.
  Since story 85 of the EasyCrypt epic, the free theorem holds only these two instances.
- `src/package_invariant/`: `PackageInvariantSmtDriver` (claim groups, one for each oracle and
  `!invariant-start!`; `--oracle`; `--invariant-start`; `--parallel`), and its UI section
  (`UI_SECTION_NAME`).
- `src/gamehops/equivalence/verify_fn.rs`: `generate_game_invariant_claims`,
  `generate_game_invariant_start_asserts`.
- `crates/domino/src/main.rs`: `prove`, `PackageWithProof`, `ReqOracleWithInvariantStart`.

## 3. Work to do

### 3.1 One owner of the free composition

- A new module, `src/game_invariant/`, owns the free composition. Move `free_theorem`,
  `free_params` and `copy_name` there from `side_run.rs`. `side_run.rs` calls the module.
- The module gives two entry points:
  - from a theorem, as now (the EasyCrypt side, `easycrypt debug/prove --side-inv C`): the names of
    the free constants come from the theorem's constants. The trace claims, the base frame and the
    fingerprint of the side tree do not change, so saved side trees resume (ADR 0008).
  - from C alone (this story and story 32): the same, from an empty theorem with a name of its own,
    `<C>$Invariant`, as `open_game_theorem` names the package's (`src/package_invariant/open_game.rs:34`).
- The module gives the `EquivalenceContext` of `C` against `C$side`, with the invariants loaded.
  Only the left side is read. The claims, their names (`game-invariant!<N>!<C>!`) and the
  package-invariant assumptions are those that the side tree already reads. Thus `prove --game` and
  `debug --game` (story 32) read one encoding.

### 3.2 The driver

- `GameInvariantSmtDriver` in the new module. Its claim groups are one for each exported oracle of C
  and `!invariant-start!`, as for a package.
- For each oracle: assume all package invariants of C's instances and all game invariants of C on
  the old state; prove each game invariant on the new state, under `no-abort`.
- The start: each game invariant holds after `init`.
- `--oracle O`: only O's group. `--invariant-start`: only the start group. Both: refused, as now
  (`ReqOracleWithInvariantStart`).
- `--parallel`, `--transcript` and `--smtsolver` work as for `--package`.
- The UI has one section, "game invariants", with one row for C, as the package section has.
- When C's instances have package invariants, the report says one line:
  `assumes the package invariants of <P1>, <P2>; prove them with domino prove --package <P>`.

### 3.3 The CLI

- `Prove` gets `--game <C>`. Help text: "Only prove the game invariants of this composition (as in
  `games/C.comp.ssp`; not a game instance), for every value of its parameters. Needs no theorem. It
  assumes the package invariants of its instances: prove them with `--package`. Plain `domino
  prove` does not run this check."
- `--game` conflicts with `--proof`, `--proofstep`, `--package` and `--injective-randmap` (clap
  `conflicts_with_all`, as in `EcDebug`). The message for `--proof`/`--proofstep` says why, as
  `PackageWithProof` does.
- Errors, each with a `help` that lists what exists:
  - no composition named C: list the compositions;
  - C has no game invariant: "composition `C` has no game invariant; its package invariants are
    proved with `--package`";
  - C exports no oracle O: list C's exports.
- A package and a composition can have the same name (4WHS: `CR`, `MAC`, `Nonces`, `PRF`).
  `--package X` always selects the package, `--game X` always the composition.
- Plain `domino prove` does not change (ADR 0021, point 4).

`--claim` with `--game` is story 31. Until then, `--game` refuses `--claim`.

## 4. Rejected alternatives

- **The game instance name** (Question 1): a weaker claim, and it needs the theorem (ADR 0021).
- **`--proof T` required** (Question 2): the theorem changes nothing in the check (ADR 0021).
- **`--game C` proves the package invariants too** (Question 3): repeats each package for each
  composition (ADR 0016) (ADR 0021).
- **A twin of `PackageInvariantContext`**, a one-game SMT encoding of its own with no copy `C$side`
  (Question 11): two encodings of one game invariant, so `prove` and `debug` can drift. The unused
  copy is a known cost, already accepted for the side tree.
- **One target flag that finds the kind** (`--invariants-of X`, Question 4): package and
  composition names are often the same.
- **Subcommands** (`domino prove game C`, Question 4): breaks every script for no new power.
- **`--side-inv C`** as the flag name (Question 5): the side-invariant lemma covers the package
  invariants too, but this check proves only the game invariants.
- **Plain `prove` runs `--game` too** (Question 10): changes the meaning and the exit code of plain
  `prove` (ADR 0021).

## 5. Tests first

- [ ] Red: `testdata/debug/se25`, `domino prove --game S`: the group of oracle `O` fails (the path
      with `x < 0` breaks `main`), and the start group verifies. The exit code is non-zero.
- [ ] `test-projects/test-game-invariant-params`, `--game C`: every group verifies. This shows that
      the free parameters `n` and `f` are read by the game invariant.
- [ ] `--game S --oracle O` runs only O's group; `--game S --invariant-start` runs only the start
      group.
- [ ] The report of `--game S` names the package invariant of `P` as assumed.
- [ ] A composition with no game invariant gives the error with the hint; an unknown composition
      lists the compositions; an unknown oracle lists the exports.
- [ ] clap refuses `--game` with `--proof`, `--proofstep`, `--package`, `--injective-randmap` and
      `--claim`.
- [ ] A fixture where a package and a composition have the same name: `--package X` runs the package
      section, `--game X` the game section.
- [ ] The move of §3.1 changes nothing: for `se25` and `se25-name-taken`, the `trace.json` claims,
      the base frame and the fingerprint of `easycrypt debug --side-inv S` are byte-identical before
      and after.
- [ ] Agreement: for `se25`, the oracles that fail `prove --game S` are the oracles whose side tree
      (`easycrypt debug --side-inv S`) has a failing terminal.

## 6. Acceptance criteria

- [ ] All tests of §5 green.
- [ ] Plain `domino prove` on `example-projects/4WHS` and on the test projects gives the same result
      as before.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget. `side_run.rs` gets
      smaller.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 7. How to verify

```bash
cd testdata/debug/se25
$D prove --game S                     # O fails: the path with x < 0 breaks main
$D prove --game S --invariant-start   # verified
cd ../../../test-projects/test-game-invariant-params
$D prove --game C                     # verified
```
