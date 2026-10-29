# Story 96 — Implementation report: an oracle that writes its argument exports

Rust only. Implementation commit: `84ae81e0` on `amir/story96` (base `ef3d2125`). No ADR.

## What changed

### `src/writers/easycrypt/package.rs`

- `build_proc` puts the EasyCrypt names of the oracle arguments into `seen` before it calls
  `collect_locals`. The names come from the same `PackageScope` mangling as the locals, so the
  two spellings are equal. `record_local` skips a name in `seen`, so it does not declare a
  `var` for an argument.
- The body does not change. A write to an argument stays a write to the parameter
  (`key <$ dbits_n;`, `h <- h + 1;`, `(h, extra) <- pair;`).
- `record_local` has a new doc comment that tells what `seen` holds.
- `collect_locals`, `lower.rs`, `check-alignment`, the tactics and the side-invariant writers do
  not change.

### Fixture (`testdata/easycrypt/story96/`)

One package `W` with one oracle `Init(h, key, hon, pair)`. The body samples into `key` when
`hon` is true (the shape of `MAC.Init`), assigns `h`, and assigns the tuple pattern
`(h, extra)`. One composition `G`, and the theorem `Story96` with one equivalence `L ~ R`
(both `G`).

## Tests

New tests:

| Test | Before the fix | After the fix |
|---|---|---|
| `package::tests::an_argument_that_the_body_writes_is_not_declared_again` | red: `argument `h` has a `var` line` (the proc had `var key` and `var h`) | green |
| `package::tests::the_body_still_writes_to_the_argument` | green (guard) | green |
| `export::tests::story96_full_tree_compiles_in_dependency_order` | red: `Pkg_W.ec: line 14 (8-11)] duplicated local/parameters name: `key'` | green |

The compile test ran EasyCrypt (`~/.opam/easycrypt/bin/easycrypt`). It did not skip: the run
has no `skipping compile check` line, and it takes 6.4 s.

Runs (`CARGO_TARGET_DIR` of the `domino-amir-easycrypt-export` worktree, default parallelism):

- Baseline, before the first edit: `cargo test -p sspverif --lib writers::easycrypt`:
  340 passed, 0 failed.
- After the fix: `cargo test --workspace`: all green. `sspverif` lib: 943 passed, 0 failed,
  6 ignored. The golden tests and the existing full-tree compile tests stay green, so an
  oracle that does not write its argument gives the same text as before.
- `cargo clippy --workspace -- -D warnings` (the CI command) and
  `cargo clippy --workspace --all-targets -- -D warnings`: clean.
- `cargo fmt --check`: the changed files are clean. See "Findings".

## Complexity

`sdlc code status .` and `sdlc crap . --since-ref ef3d2125 --threshold 15` stop with
`No sdlc-config.json found`: this repo is not a target of an `sdlc` workspace.
**CRAP gate: UNMEASURED.** CC counted by hand (decision points + 1; a second number also counts
each `?` as a branch):

| Symbol | CC | CC with `?` | Note |
|---|---|---|---|
| `build_proc` | 4 | 11 | edited; the new line adds no branch |
| `record_local` | 3 | 5 | doc comment only |
| `collect_locals` | 8 | 13 | not edited; the story names it |
| test `story96_init_proc` | 1 | 1 | new |
| test `var_lines` | 1 | 1 | new |
| test `an_argument_that_the_body_writes_is_not_declared_again` | 5 | 5 | new; counts the `if` of each `assert!` |
| test `the_body_still_writes_to_the_argument` | 3 | 3 | new; counts the `if` of `assert!` |
| test `story96_full_tree_compiles_in_dependency_order` | 1 | 1 | new |

All are below 15. The complexity box of §6 stays open because the CRAP score is not measured.

## Real-world check (ec4whs)

- Binary: `cargo build -p domino --features cvc5-lib --release`, copied to
  `/tmp/claude-3155823/story96/domino-story96`. The build needs
  `CVC5_LIB_DIR` and `CVC5_INCLUDE_DIR` set to
  `~/.cache/domino/cvc5-1.4.2-Linux-x86_64-static/{lib,include}`. Without them, `cvc5-sys`
  tries to build cvc5 from source and stops with `cmake: command not found`.
- `domino-story96 easycrypt export --project ~/ec4whs/4WHS --theorem Full4WHS
  --out /tmp/claude-3155823/story96/out`: 225 files.
- `Pkg_MAC.ec`: `d_Init` has no `var key` line. The two `var key` lines in the file are in
  `d_Mac` and `d_Verify`, where `key` is a local and not an argument.
- `easycrypt compile -I out/Full4WHS out/Full4WHS/Comp_H7.ec`: exit 0. `Pkg_MAC.ec` alone:
  exit 0.
- Negative control: in a copy, the old line `var key : bits_n;` in `d_Init` makes
  `Comp_H7.ec` fail with `duplicated local/parameters name: `key'`. The check thus finds the bug.
- Not run: `easycrypt prove`. The owner's check of §6 stays open.

## Findings outside the story

- `cargo fmt --check` fails at `ef3d2125`, before this story, in five files:
  `crates/domino/src/cli.rs`, `crates/domino/src/main.rs`, `crates/domino/tests/prove_claim.rs`,
  `src/debug/index.rs`, `src/easycrypt/tactics/tests.rs`. CI (`rust.yml`) runs
  `cargo fmt --check`. Not fixed here: the commit plan of this story has one implementation
  commit, and other sessions change these files. One `cargo fmt` commit on
  `amir/easycrypt-export` fixes it.
- The release build with `cvc5-lib` needs the `CVC5_*` variables above on this machine (no
  `cmake`).

## Deviations from the spec

None.
