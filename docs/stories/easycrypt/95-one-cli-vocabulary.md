# Story 95 — One CLI vocabulary: `--project`, `--theorem`, `--gamehop`, `--game`, `--package`, `--timeout`

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 94 (this story renames the words in the header that 94 writes).
**Blocks:** nothing.
**ADR:** none. The rejected alternatives are in §5.
**Decisions:** owner's grilling session of 2026-10-26, Questions 5 to 8. The terms **Project**,
**Theorem** and **Game hop** are in `CONTEXT.md`.

A **CLI** story: `crates/domino/src/cli.rs`, `crates/domino/src/main.rs`, the text that `src`
prints, the tests and the docs. Test-first.

---

## 1. Why this story exists

`domino easycrypt …` and the other commands use different names for the same things:

| Concept | `domino easycrypt …` now | `debug`, `prove`, `inline`, `html`, `latex`, `proofsteps` now |
|---|---|---|
| project | `--project` (global) | `--path` |
| theorem | `--theorem` | `--proof` |
| game hop index | `--proofstep` | `--proofstep`; the subcommand is `domino proofsteps` |
| one-sided run of a composition | `--side-inv C` | `--game C` |
| one-sided run of a package | `--pkg-inv P` | `--package P` |
| per-query solver timeout (ms) | `debug --debug-timeout` | `debug --timeout` |

A user must remember which command uses which name. The theorem language already calls a step of a
theorem a game hop (the keyword `gamehops`, and `src/gamehops/`).

## 2. The names after this story

| Concept | All commands |
|---|---|
| project | `--project <DIR>` |
| theorem | `--theorem <NAME>` |
| game hop index | `--gamehop <N>`; the subcommand is `domino gamehops` |
| one-sided run of a composition | `--game <C>` |
| one-sided run of a package | `--package <P>` |
| per-query solver timeout (ms) | `--timeout <MS>` |

`--gamehop` keeps its meaning: the index from 0 that `domino gamehops` prints.
`--ec-timeout` (`domino easycrypt prove`, seconds for one EasyCrypt sentence) does not change; it is
a different timeout, and no command has both.

### 2.1 `--game` and `--package` on `domino easycrypt`

The pairs match one to one (ADR 0016):

- `domino prove --game C` and `domino easycrypt prove --game C` walk the oracles of C and prove its
  game invariants. Both take the package invariants from the package job.
- `domino prove --package P` and `domino easycrypt prove --package P` prove the package invariants
  of P.

The EasyCrypt lemma `SideInv_<C>_<O>` states more than the SMT check: package invariants and game
invariants. Its package part comes from the lemmas of `--package`. The help text of
`domino easycrypt prove --game` must say this:

> Only the side-invariant job of this composition: the lemma `SideInv_<C>_<O>.ec` of each of its
> oracles. Its game invariants are proved here, along the side tree of one-sided execution; its
> package invariants come from the package-invariant and frame lemmas of `--package`, which must
> exist first.

The file and directory names (`SideInv_<C>`, `PkgInv_<V>`, `session/…`, `progress/…`,
`!debug!/SideInv_<C>/…`) do not change.

## 3. The scope: what people type and read

| Layer | Changes? |
|---|---|
| CLI flags and the subcommand `proofsteps` | **Yes.** |
| Text that people read: `--help`, stdout, stderr, error messages, page titles and labels, `summary.txt`, `Readme.md`, the command lines in `docs/*.md` | **Yes.** "proofstep" becomes "game hop", "proof" (as the name of a theorem) becomes "theorem". |
| Files that tools read: the `trace.json` field `"proofstep"`, the result record `<strategy>_result.json` (`src/debug/index.rs:56`) | **No.** The debug index reads old result records from disk. |
| Rust names (`proofstep_dir`, `Prove::proofstep`, `fn proofsteps`, …) | **No.** Field names in `cli.rs` change only where clap takes the flag name from them. |
| Old stories and implementation reports in `docs/stories/` | **No.** They are history. |

## 4. What to build

### 4.1 The CLI (`crates/domino/src/cli.rs`)

- `Commands::Proofsteps` becomes `Commands::Gamehops` (subcommand `gamehops`), with a doc comment
  for `--help`.
- On `Prove`, `Debug`, `Inline`, `Html`, `Latex`, `Gamehops`: `path` becomes `project`, `proof`
  becomes `theorem`, `proofstep` becomes `gamehop`. The `conflicts_with_all` strings change with
  them.
- On `EcProve`, `EcCheckAlignment`, `EcDebug`: `proofstep` becomes `gamehop`; `side_inv` becomes
  `game`; `pkg_inv` becomes `package`; `debug_timeout` becomes `timeout`. The help text of
  `EcProve::game` is the text of §2.1.
- **No aliases.** An old name gives clap's error (`unexpected argument '--proof'`).
- Each doc comment says "game hop" and "theorem", and refers to `domino gamehops`.

### 4.2 The text that `src` prints

The 52 places outside `cli.rs` that print an old flag name (for example
`#[error("--game cannot be used with --proof or --proofstep")]`, `crates/domino/src/main.rs:100`),
in `src/debug/*`, `src/easycrypt/*`, `src/game_invariant/*`, `src/package_invariant/context.rs`,
`src/writers/html.rs`. Find them with
`grep -rnE -e '--(proof|path|proofstep|side-inv|pkg-inv|debug-timeout)\b' src crates/domino/src`.

The word "proofstep" in text that people read: the stdout reports, `summary.txt`, the titles of the
viewers (`src/debug/lockstep_viewer.html`, `src/debug/report.rs`), the debug index, the live page of
a tactics run, the stage messages and the `domino gamehops` output. The `trace.json` field stays
`proofstep`; the page reads it and writes "game hop".

### 4.3 The callers

- `crates/domino/tests/*.rs`: the 26 places that pass the old flags, and the tests that match on
  printed text.
- `scripts/test-known-examples.sh:63`.
- `Readme.md:88-95`, and the command lines in `docs/*.md` (not `docs/stories/`).

The `domino` skill (`domino-skills/domino/SKILL.md`) uses the new names already. It was committed
before this story, in its own repo.

## 5. Rejected alternatives

- **Rename everything, JSON fields and Rust names too.** The debug index would not read old result
  records without serde aliases, and the diff touches about 400 places for no change that a user
  sees. It can be a later mechanical story.
- **Rename the flags only.** `--gamehop 3` would print "proofstep 3": two words for one thing.
- **Hidden aliases for the old names, with or without a warning on stderr.** The owner chose a hard
  break, and changes every caller in the repo and the skill instead.
- **`--side-inv` and `--pkg-inv` on all commands.** `domino prove --side-inv C` would be the wrong
  word: the SMT check proves the game invariants of C, not a side-invariant lemma.
- **Keep `--side-inv`, `--pkg-inv` and `--debug-timeout` for a later story.** Two dialects stay, and
  the users get a second hard break.

## 6. Tests first

- [x] For each command, clap parses the new names (`try_parse_from`, as the test in `cli.rs` does):
      `prove --project D --theorem T --gamehop 3`, `debug --project D --theorem T --gamehop 3
      --oracle O`, `inline …`, `html --theorem T`, `latex --project D`, `gamehops --project D`,
      `easycrypt prove --theorem T --gamehop 3`, `easycrypt prove --theorem T --game C`,
      `easycrypt prove --theorem T --package P`, `easycrypt debug --theorem T --game C --timeout 500`,
      `easycrypt check-alignment --theorem T --gamehop 3`.
- [x] For each old name, clap gives an error: `--path`, `--proof`, `--proofstep`, `--side-inv`,
      `--pkg-inv`, `--debug-timeout`, and the subcommand `proofsteps`.
- [x] The conflicts still hold: `easycrypt prove --gamehop 3 --game C` and
      `easycrypt prove --game C --package P` give errors; `prove --game C --theorem T` gives the
      error of `main.rs`, now with the new names.
- [x] `domino gamehops` prints the same table as `domino proofsteps` did.
- [x] No `--help` text and no printed message has an old name: a test that runs `--help` for each
      command and subcommand and searches for the old names.

## 7. Acceptance criteria

- [x] All tests of §6 green, the whole test suite green, `cargo clippy` clean.
- [x] `scripts/test-known-examples.sh` passes.
- [x] `grep -rnE -e '--(proof|path|proofstep|side-inv|pkg-inv|debug-timeout)\b|proofsteps' src
      crates scripts Readme.md docs --exclude-dir=stories` finds nothing, except the JSON field
      `proofstep` and the Rust names that §3 keeps.
- [ ] The owner's check: a lockstep page title, a stdout report and an error message say "game hop".
- [x] Complexity: no function in `main.rs` above budget after the renames (`crap_scope` on
      `crates/domino/src/main.rs`).
