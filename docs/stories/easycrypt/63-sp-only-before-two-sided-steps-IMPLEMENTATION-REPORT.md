# Story 63 — Implementation report: `sp` only before a two-sided step

Rust only. The translation does not change.

## What changed

- **`driver.rs`, `step_node`.** A determined node no longer gets `sp k l.` first. `step_node`
  checks that the front goal is a program goal and calls `determined`, which sends
  `rcondt{i} ^if; 1: auto => /#.` (or `rcondf`) directly. The other kinds (synchronized `if.`,
  split `if{1}.`, sampling `seq`) keep `sp_front` before their step. The straight-line code
  before the `if` stays in the programs; the next two-sided step's `sp` or the leaf takes it.
- The router prelude (`oracle_inner`) and the fallback (`prove_blind`) do not change.
- `--no-quick-close` does not change: the side goal of `rcondt`/`rcondf` still gets
  `auto => /#` first.

### Rejected shape

A flag on `sp_front` or a second `sp`-less path in `determined`. The kind check in
`step_node` is the one place where the order is decided.

## Tests

- `the_walk_of_the_joint_tree_alone_closes_hello_world_too` (live, `cvc5-lib` + EasyCrypt): it
  now asserts that no `sp` sentence comes right before an `rcondt`/`rcondf` sentence. It already
  asserts `sp 1 1.` and `if.` (the router prelude). The synchronized `if.` after `sp` is unchanged
  code, so no new test for it was added.
- `cargo test --lib`, `cargo clippy --workspace --all-targets`, `cargo build --release --workspace`:
  680 passed, 5 ignored; clippy clean; release build OK.

## Not done

- The live tests did not run: `--features cvc5-lib` does not build here (no `cmake` for
  `cvc5-sys`). The new assertion is compiled only with that feature, so it was not compiled either.
- The acceptance asks for a driver unit test with no EasyCrypt. The driver talks to a real
  `Session` process; there is no fake session, so such a test needs a new seam. Not added.
- The H2_1 ~ H3_0 counts (`sp` sentences, `branch-condition` and `side-goal` admits, before and
  after) were not measured: the owner asked for no EasyCrypt proof runs in this session.
  Before (2026-10-08, from the story): 1,408 `sp` sentences over all hops, 1,018 of them before
  `rcondt`/`rcondf`.
- Risk: `rcondt{i} ^if` now sees straight-line code before the `if`. Its side goal is a `hoare`
  over that code; `auto => /#` should handle it, but this is not checked on Full4WHS.
- The CRAP gate was not measured (`sdlc` is not available here). `step_node` has CC 5.
- The repository is not `cargo fmt` clean before this story (`crates/domino/src/main.rs` and
  others); the story did not run `cargo fmt` on the whole tree.
