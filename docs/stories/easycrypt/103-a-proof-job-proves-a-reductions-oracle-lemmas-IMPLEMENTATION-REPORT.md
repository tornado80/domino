# Story 103 — Implementation report: a proof job proves a reduction's oracle lemmas

Prover story. Branch `amir/easycrypt-export`, ADR 0023. Implementation in the commit "Story 103: a proof job proves a reduction's oracle lemmas", review fixes after it.

## What was built

**Export** (`reduction_lemmas.rs`, `export.rs`):

- Each oracle lemma's proof is the placeholder of an equivalence oracle file: `(* d_<O> *)` and `+ proc; inline. admit.`. `oracle_proof`, `ladder`, `alias_names`, `LADDER_RUNGS` and the `exclusions`/`meq` fields of `SideSpec` are removed.
- `ReductionOracleFile` and the new `ReductionReport.oracle_lemmas` (`ReductionOracleLemma`) carry the job's oracle name, the procedure (the placeholder's marker) and the invariant operator.
- `admit_count` is one for each oracle lemma file.
- `is_oracle_file` (`job.rs`) lists the reduction oracle files: the job owns them, and translation only creates them when they are missing.

**Job** (`tactics/mod.rs`, `oracles.rs`, `driver.rs`, `check.rs`):

- `JobKind::Reduction(&ReductionReport)`. `reduction_job_report` gives the job's "proof file" as `Red_<L>_<R>.ec`, so records go to `session/Red_<L>_<R>/` and pages to `progress/Red_<L>_<R>/`.
- `check::reduction_setup` builds the setup from the hop's instances, with the reduction's oracles.
- `RunPlan.reductions`. `--gamehop N` selects a reduction hop and does not wait for side-invariant files. Without `--gamehop`, `hop_jobs` runs equivalences and reductions in hop order.
- `tactics_for_oracle` runs no lockstep execution for a reduction (`WalkedTree::blind()`, an empty tree) and does no tree resume. Its unfold and part operators are the lemma's `inv_<L>_<R>` (`_L`/`_R`).
- `Judgement::Reduction`: the prelude is `proc; inline *.`, then `prove_blind(0, 64)`, the walk of §7.4 with the leaf step `leaf_of(_, None)`. Otherwise it behaves as `Equiv` (`one_program()` is now an explicit `Hoare | Package`).
- The report line of a reduction oracle reads "blind walk, no joint tree".

**Overwrite guard**: `is_proof_file` also counts `Red_*.ec`. The router and joining files have no bullet, so they are never listed.

**CLI help** and **docs**: `easycrypt prove` help (`--gamehop`, `--oracle`, `--jobs`); `docs/easycrypt-export.md` §"Translating reductions" (the placeholder, the `_L`/`_R` files, the reduction proof job); `docs/proving-algorithm.md` §1.1 table (only the reduction row, split into the oracle lemma and the run/proposition lemmas).

## Decisions and deviations

- **Split sides get a file each.** When the sides do not share their lemmas (hello-world), `Red_<H>_<O>_L.ec` and `_R.ec` replace story 102's one file holding both. The job proves one lemma per file, and its oracle names are `<O>_L`/`<O>_R` (also for `--oracle`). As a result, an oracle called `Router` no longer collides with the router file in the split case. The test became `a_split_reduction_oracle_called_router_does_not_meet_the_router_file`. In the shared case the name rule still rejects it. This may deserve a note in ADR 0013/0023.
- **Inline exclusions dropped.** The prelude is a plain `proc; inline *.`, as in story 101's prototypes (hello-world included).
- **Where the invariant name comes from.** The export computes `inv_<L>_<R>` once, by the name rule, and passes it in the report. The job does not rebuild it from the stem.
- **An interrupted reduction oracle is walked again from the start.** There is no tree to save. A done oracle is skipped, as for equivalences.
- **Left as is from the review:** the report line detects a reduction by its `Red_` prefix, not by the job kind. The job reuses `EquivalenceReport` (as the side and package jobs do), and `oracle_files`/`oracle_lemmas` are parallel vectors. `cli.rs` carries rustfmt reflows of two existing tests.
- **Loops:** `prove_blind` has no trial for `while`, so a loop ends in `program-mismatch`. No fixture has a loop, so there is no test.
- **Speed:** PKENC of kem-dem takes about 275 s. Most of that is failed `rcondt/rcondf` trials, about 3.4 s each, which spend their time in smt.

## Tests run

All runs were under `systemd-run --user --scope -p MemoryMax=6G timeout …`, with no other domino proving job running, on EasyCrypt r2026.09.

| Command | Result |
|---|---|
| `cargo test -p sspverif --lib writers::easycrypt::reduction` | 6 passed (placeholder, no ladder, split files) |
| `cargo test -p sspverif --lib writers::easycrypt::export::tests -- --skip compiles --skip 4whs --skip 4WHS --skip yao` | 15 passed |
| `cargo test -p sspverif --lib writers::easycrypt::overwrite` | 14 passed (new: proved `Red_*_<O>.ec` listed) |
| `cargo test -p sspverif --lib easycrypt::tactics::tests::reduction_jobs` (unit) | 4 passed: gamehop selects `Reduction` without side files, hop order, setup and invariant, resume skips a done oracle |
| `DOMINO_EASYCRYPT=… cargo test … reduction_jobs::prove_closes_the_reduction_consts` | passed, 9 s: no admit, only `sp`/`if`/`rcond`/`seq`/`auto`, Router, Query, join and both `Prop_*` compile |
| `domino easycrypt export` then `prove --gamehop 1/2/3 --jobs 3` on kem-dem-cca-ssp | hop 1: 35 goals, 0 admits (276 s); hop 2: 33 goals, 0 admits (244 s); hop 3: 33 goals, 0 admits (221 s). Then no `admit` in any `Red_*`/`Prop_*`, and every `Red_*` file and `Prop_Main.ec` compiles on its own (`easycrypt compile -no-eco`) |
| `cargo clippy --workspace --all-targets` | clean |

The CRAP gate: `crap-coverage.sh` ran, but `sdlc crap gate --since-ref d62797a4` fails with `bwrap: loopback: Failed RTM_NEWADDR` (as in story 102), so it was skipped. The new functions are small.

## Written, not run

- `reduction_jobs::prove_closes_one_oracle_of_the_first_kem_dem_reduction` (live, `--oracle PKDEC`). The same work ran through the CLI on hop 1 instead.
- The compile tests of `export.rs` (`assert_tree_compiles` now expects one admit per oracle file) were not rerun in the final run: `cargo test -p sspverif --lib compiles -- --test-threads=1` with `DOMINO_EASYCRYPT`.
- No 4WHS run, by rule.

## Epic §5 "Done when"

- [x] Stories 101–103 done, each with an implementation report.
- [x] No exported file names `RedExp_` or `setup` (story 102's tests, still green).
- [x] `export` + `prove` (hops 1–3) on kem-dem-cca-ssp leaves no `admit` in `Red_*`/`Prop_*`, and those files compile. Hop 0 (the equivalence, `Eq_*`) was not proved here.
- [x] `docs/easycrypt-export.md` and `docs/proving-algorithm.md` describe the layout and the reduction proof job.
