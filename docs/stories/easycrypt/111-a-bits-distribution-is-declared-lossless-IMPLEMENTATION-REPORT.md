# Story 111: implementation report. A Bits distribution is declared lossless

A writer story on branch `amir/easycrypt-export`. Commits: `8776ecfb` (the implementation, the
goldens, the fixture and the docs), `7e530985` (the review fix), and this report.

## Result

For each bits type, `Types.ec` now declares

```
op [lossless] dbits_n : bits_n distr.
```

and no longer has a separate `axiom dbits_n_ll`. EasyCrypt declares `dbits_n_ll` itself and puts
it into the hint bases `random` and `lossless`. A one-sided sampling of `dbits_n` now closes
under `seq 0 1 : (#pre); 1: auto => />.`, and the prover is unchanged.

The new fixture is red with the old declaration and green with the new one. With the old
`Types.ec` (from `HEAD` before the change), EasyCrypt stops at the `qed` of the `equiv` with
`cannot save an incomplete proof`. With the new one, it compiles.

## What was built

- **`EcItem::OpDecl { name, ty, tags: Vec<String> }`** (`ast.rs`). `render_op_decl`
  (`render.rs`) prints `op [t1 t2] name : ty.` when `tags` is not empty, and `op name : ty.`
  otherwise. Every other `OpDecl` (zero, one, `func_*`, and the kitchen-sink test) has
  `tags: vec![]` and renders the same text as before.
- **`bits_type_items`** (`typesfile.rs`) tags the distribution `lossless` and emits no `Axiom`.
  Its doc comment says why.
- **Goldens.** The seven `Types.ec` files under `testdata/easycrypt/story0{2,3,4}/` are updated.
  In each one, only the `op dbits…` line changes, and the `axiom` line is removed.
- **Fixture** `testdata/easycrypt/story111/`. It has `Types.ec`, which is the writer's output for
  hello-world, and `IndependentSampling.ec`. That file proves `L.f ~ R1.f`, where `R1.f` samples
  `dbits_n` once, with `seq 0 1 : (#pre); 1: auto => />.`. It also has a lemma that names
  `dbits_n_ll` by hand (`exact dbits_n_ll`).
- **Docs.** `docs/easycrypt-export.md` shows the new line. In `docs/proving-algorithm.md` §9.2,
  the blind-walk row of `program-mismatch` names story 111.

## Tests

All runs were filtered and used `--test-threads=1`, under `systemd-run --user --scope -p
MemoryMax=6G` and with `DOMINO_EASYCRYPT` set, so the compile tests really ran.

| Test | Result |
|---|---|
| `op_decl_with_lossless_tag_renders_the_tag`, `op_decl_without_tags_renders_as_before` (`render.rs`) | ok |
| `bits_type_items_named_width`, `bits_type_items_any_width_has_no_suffix`, `bits_type_items_numeric_width_is_lossless_with_no_axiom` | ok |
| `*_types_file_matches_golden` (3), `story111_types_file_matches_writer_output` | ok |
| `*_types_file_compiles` (3), live | ok |
| `independent_sampling_closes_with_lossless_bits_distribution`, live | ok |
| `writers::easycrypt::{tests, interfaces, package, game}` (74 tests, including the compile tests over the story 03/04 goldens) | ok |
| `cargo clippy --workspace --all-targets` | clean |
| `rustfmt --check` on the touched files | clean |
| `cargo test easycrypt` (the wide filter) | **did not finish**: it was stopped by its 3000 s timeout. Two live tests failed before that, see below |
| CRAP gate | **not run to the end**: `crap-coverage.sh writers::easycrypt::typesfile writers::easycrypt::render writers::easycrypt::tests` ingested coverage, but `sdlc crap gate` fails with `bwrap: loopback: Failed RTM_NEWADDR`. The new function `render_op_decl` has two branches, and both are covered |

### The two live failures in `easycrypt::tactics::tests::live`

These two tests failed:

- `a_resumed_job_does_not_walk_the_oracles_the_record_holds`
- `three_jobs_prove_three_oracles_at_once_and_the_report_keeps_oracle_order`

The first one fails alone, with `Check(NoSuchOracle { oracle: "AnotherUsefulOracle", file:
"Red_big_composition_medium_composition_more_oracles.ec" })`. That error comes from the oracle
selection (`tactics/oracles.rs`, `check.rs`), not from `Types.ec`.

I could not confirm that they fail at `7e0c6af6`, because a base-commit worktree was not
permitted in this session. They look unrelated to this story, but this has not been verified.

## Deferred to the owner

The proof runs of §7 are not made here. They run once, after Stories 111 and 112 are both merged,
in `ec4whs`:

1. 4WHS-mac, hop 11, `Send3`;
2. 4WHS-prf-mac, hop 11, `Send3`;
3. 4WHS-mac, `SideInv_H7`, `Send2`;
4. 4WHS-prf-mac, `SideInv_H7`, `Send2`.

Before these runs, the translation files are exported again (`export --force`).

## Review

- **Spec.** Nothing was missing. One note: the story111 `Types.ec` was a copy, so it could drift
  from the writer's output. This is fixed: `story111_types_file_matches_writer_output` checks it
  against the writer.
- **Standards.** No documented standard was broken. The review raised a judgement call:
  `tags: Vec<String>` is stringly typed, and `tags: vec![]` is repeated at the call sites. I kept
  it, because §3.1 of the story names this shape (`tags: Vec<String>`). An `enum OpTag` is the
  option if a second tag ever appears.

## Follow-ups

- Find out whether the two failing live tactics tests above also fail on the base commit.
- The CRAP gate cannot run in this sandbox (bwrap).
