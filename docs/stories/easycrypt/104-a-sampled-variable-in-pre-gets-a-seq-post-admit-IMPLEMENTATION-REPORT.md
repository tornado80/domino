# Story 104 — Implementation report: a sampled variable that `#pre` mentions gets a `seq-post` admit

Prover story. Branch `amir/easycrypt-export`, ADR 0024 (decision 5). Implementation in the commit
"Story 104: a sampled variable that #pre mentions gets a seq-post admit" (14db326e), review fixes in
b934e153.

## What was built

**JSON** (`src/easycrypt/json.rs`): `Form.module` (the module of a `glob` node, as EasyCrypt prints
it) and `LValue.vars` (the `pvar`s an lvalue writes). Both were in EasyCrypt's JSON already and not
read.

**The check** (`src/easycrypt/tactics/goals.rs`):

- `ProgramSide { Left, Right }` names a program of an `equivS` goal.
- `sampled_in_pre(goal, side, lvalue) -> bool` and `sampled_var_in_pre(...) -> Option<&Form>`
  (the variable that matched). True when `#pre` holds, in the memory of `side`, a `pvar` with the
  same scope and name/path as a variable of the lvalue, or a `glob G` where `G` is the variable's
  module or a module that contains it. `pub(crate)`; story 106 calls it.
- `glob_holds`: `G` matches any contiguous run of the module path's segments, because EasyCrypt
  prints `G` relative to the scope (`MAC` for `Pkg_MAC.MAC`); `Top.` and functor arguments
  (`M(A)`) are dropped. `strip_top` replaces three copies of `strip_prefix("Top.")`.

**The prover** (`src/easycrypt/tactics/driver.rs`):

- `synchronized_sampling(goal) -> Option<SyncSampling>`, a pure function: `Seq(post)` with
  `(#pre /\ x{1} = y{2})`, or `Admit(claim)`: `sampling` when assignments come before the sampling
  (as before), `sampling: <x>{<side>} in #pre` when the check is true on side 1 or 2 (left first).
  For a tuple lvalue the claim names the variable that matched.
- `sampling()` loads the front goal in full (`full_front`, so a stub cannot hide a variable), asks
  `synchronized_sampling`, and on `Admit` calls `seq_post_admit(idx, claim)` and sends no `seq`.
  `seq_post_admit` now takes the claim.

**Docs** (`docs/proving-algorithm.md`): §9.1 `seq-post` also means "`#pre` mentions the sampled
variable"; §9.2 has a row for the new claim, and the new case is no longer called defensive.

## Decisions and deviations

- The §4 test "`sampling()` … writes `seq-post` … and sends no `seq`" tests the pure
  `synchronized_sampling` that `sampling()` follows, not `sampling()` itself: `sampling()` reads
  its goal from a live session. The admit call on `Admit` is one line.
- `sampled_in_pre` carries `#[allow(dead_code)]` until story 106 calls it; the driver uses
  `sampled_var_in_pre` to name the variable.
- Not changed: the blind walk (`prove_blind`, step 5) still sends `seq 1 1` without the check. The
  epic keeps the blind walk unchanged; story 106's reduction walk calls the check.
- `full_front` now runs at every synchronized sampling. It costs a round trip only when the front
  goal was read with `head`.
- Glob matching by segment runs can give a false positive when two modules share a segment name
  (e.g. two `MAC` modules); the cost is a `seq-post` admit instead of a `seq` attempt.

## Tests run

| Command | Result |
|---|---|
| `cargo test -p sspverif --lib goals::tests -- --test-threads=1` | 31 passed (4 new: local in `&2`, `glob` incl. `Top.`/short/functor names and a non-container, global `pvar`, `Send2` nonce) |
| `cargo test -p sspverif --lib sampl -- --test-threads=1` | 17 passed (2 new in `tactics::tests`: admit with `sampling: key{2} in #pre`; `seq 1 1` post for `ni1`) |
| `DOMINO_EASYCRYPT=… systemd-run --user --scope -p MemoryMax=6G timeout 900 cargo test -p sspverif --lib the_walk_of_the_joint_tree_alone_closes_hello_world_too -- --test-threads=1` | 1 passed (live, hello-world, the `seq 1 1` path), 118 s |
| `cargo clippy --workspace --all-targets` | clean |
| `.sdlc-workspace/crap-coverage.sh goals::tests sampling` | coverage ingested |
| `sdlc crap gate . --since-ref cfb075ce --threshold 15` | not run: `bwrap: loopback: Failed RTM_NEWADDR` |

A run of the whole `easycrypt::` test module (`timeout 900`) was cut by the timeout without a result
line; it is not counted.

## Written, not run

None. The live 4WHS-mac case (an oracle sampling into its argument `key`) is the acceptance of
story 107, not run here.

## Epic §5 "Done when"

- [ ] Stories 104–107 done with reports — 104 done.
- [ ] `prove` on `reduction-consts` and `reduction-two-calls` leaves no admit — story 106.
- [ ] Hop 12 of Full4WHS — story 107.
- [ ] `docs/proving-algorithm.md` — §9.1/§9.2 updated for `seq-post`; §10 and the new reasons with 106.
