# Story 46 — The leaf budget applies only when the user asks for it

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 27 (tactic generation), 35 (`prove` is its own command).
**Blocks:** nothing. It is independent of story 47.

---

## 1. Why this story exists

The owner: *"I want the leaf budget to apply only when the user provides it."*

`domino easycrypt prove --leaf-budget <secs>` defaults to 300 s (`crates/domino/src/cli.rs`,
`EcProve.leaf_budget`). So every tactics run gives up on a leaf after five minutes, whether or not
anyone asked for that. It admits the parts it has not reached with the note `(leaf time budget
spent)`. Story 27's implementation report already pointed out what this costs: *"The leaf budget
makes the result depend on timing on kem-dem (which part is cut off)"*. Two runs on the same project
can admit different parts of the same leaf, depending on how fast the machine is.

A leaf cannot run forever without the budget: `--ec-timeout` (default 60 s) still bounds every
sentence, and taking a leaf apart sends a finite number of sentences. The budget is therefore a
user's trade (a faster run, more admits), not a safety net. It should apply only when someone chooses it.

Vocabulary (`CONTEXT.md`): **Leaf**, **Leaf budget**.

## 2. Inherited from earlier stories

- **Story 27:** the budget covers only the split by meaning
  (`Prover::leaf_of` → `solve_ambient`, `src/easycrypt/tactics/driver.rs`). The deadline is set
  just before `solve_ambient` and cleared after it. `solve_ambient` checks it before each step and
  calls `admit_part(…, " (leaf time budget spent)")` once it has passed. The fast path and
  the rungs before the split are not under the budget, and stay that way.
- **Story 35:** the flag lives on `EcProve`; `main.rs` turns it into `TacticsOptions.leaf_budget`
  (`src/easycrypt/tactics/mod.rs`), whose `Default` also says 300 s, and the driver's
  `Prover.leaf_budget`.
- **`src/easycrypt/tactics/tests.rs`** builds a `Prover` with `leaf_budget: 60 s`.

## 3. Work to do

- `EcProve.leaf_budget` becomes `Option<u64>` with **no default**. Help text: the seconds one
  leaf may spend being split by meaning before its remaining parts are admitted; **off unless
  given**; each sentence is still bounded by `--ec-timeout`.
- `TacticsOptions.leaf_budget` and `Prover.leaf_budget` become `Option<Duration>`. The `Default`
  for `TacticsOptions` is `None`. `leaf_of` sets `deadline` only when there is a budget.
  `solve_ambient`'s check is unchanged, since it already handles `deadline: None`.
- Any `--leaf-budget` value given is honoured as is. `0` has no special meaning: it admits every part of
  the split at once, which is what the current code would do.
- Tests that relied on the 300 s default without saying so now run without a budget. Tests that
  need one pass it explicitly. `tactics/tests.rs`'s `Some(60 s)` stays if a test depends on it;
  otherwise it becomes `None`.
- **Leave alone:** ADRs and earlier stories and reports. They record what was true at the time.

## 4. Acceptance criteria

- [ ] `domino easycrypt prove …` without `--leaf-budget` never admits a part with the note
      `(leaf time budget spent)`.
- [ ] `domino easycrypt prove --leaf-budget N …` behaves as today's default did with `N`.
- [ ] `domino easycrypt prove --help` says the budget is off unless given.
- [ ] A unit test on the driver: with `leaf_budget: None`, the deadline stays `None` through
      `leaf_of`; with `Some(d)`, it is set to `now + d` around `solve_ambient` and cleared after.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt export --theorem <T> --force
$D easycrypt prove --theorem <T> --force            # no "(leaf time budget spent)" admits
grep -rn "leaf time budget spent" <out>/Eq_*.ec     # nothing
$D easycrypt prove --theorem <T> --force --leaf-budget 5
grep -rn "leaf time budget spent" <out>/Eq_*.ec     # appears where a leaf was cut
$D easycrypt prove --help | grep -A2 leaf-budget
```
