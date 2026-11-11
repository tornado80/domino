# Story 102 — Implementation report: a proposition defines its reduction adversaries

Writer story. Branch `amir/easycrypt-export`, ADR 0023. The implementation is in commit `edf64c1b`, the review fixes follow it.

## What was built

**The reduction's files** (`reduction.rs`, `reduction_lemmas.rs`):

- `Red_<H>_Router.ec`: the clones, the import adapters, the router `Red_<H>(O)` and `inv_<H>` (or `_L`/`_R`). The invariant has no conjunct for a stored constant. `B`, `setup`, `RedExp`, `StoredConst`, `adversary_init`, `b_module`, `red_exp_module` and `param_var_storing` are removed.
- `Red_<H>_<O>.ec`: the oracle lemma `Red_<H>_<O>` (or `_L` and `_R` in one file). The proof is still the story-97 ladder, so no file has an `admit`.
- `Red_<H>.ec`: `declare module A` with the restrictions and `run_<H>` (or `run_<H>_L`/`_R`), proved by `proc (inv ..) => //.` and one `conseq` for each oracle. The statement is the new `EcExpr::RunEquiv` (`={glob A}` in place of `={arg}`).
- `ReductionFile` carries the three files, `run_lemmas` and `RouterUse` (router module, adversary and assumption interfaces, the values of the router's `init` arguments).

**The proposition file** (`proposition.rs`, new `prop_reduction.rs`):

- For each reduction step: if the step leaves a constant of the router's `init` free, the hop is an open hop of kind `reduction`. Otherwise the file gets `B_<H><s>` (one for each (hop, values) pair), `equiv_<H><s>` by the merge rule (or `_L`/`_R` with literals), and `bound_<H><s>`. The term is the bound lemma's right side, in the hop's direction.
- The merge rule and the suffix (`neg<n>`) are pure functions in `prop_reduction.rs`.
- Theorem constants that a `run` argument reads and the path leaves free become binders of the equiv and bound lemmas and of the proposition lemma.

**Report:** `ReductionReport` has `file`, `router_file`, `oracle_files`, `run_lemmas`, `admit_count`. `PropositionReport` has `reduction_steps` (adversary, values, equiv names, bound name). The CLI line for a reduction names the run lemma(s), the oracle file count and the admits.

**Name rule:** the reduction oracle files join the lemma files of `insert_lemma_files`, so an oracle called `Router` collides with the router file (`LemmaFileCollision`).

**Fixture:** `testdata/easycrypt/reduction-consts` gets four instances with `flip` fixed, the conjecture `mod_ideal_false ~ mod_ideal_true`, and the propositions `FlipBound` (fixes `b`, the path of the story-101 prototype) and `Free` (leaves `b` free).

**Docs:** `docs/easycrypt-export.md` §"Translating reductions" and §"Translating propositions".

## Decisions and deviations

- The generated text matches the story-101 prototypes: the unit tests compare the run lemma, invariant, oracle lemma, equiv, bound, B and proposition statements with the files under `layout/`.
- **§3.5 "exports no … constant to the proposition writer":** the proposition must know the router's `init` arguments to write `B`, so `RouterUse.init_values` holds them (a literal or a theorem constant). The proposition also reads the joining file's `declare module` for the restrictions, which it qualifies with `Red_<H>_Router.`. No invariant or oracle lemma name crosses.
- **Free constants that only a `run` reads** (not the router) are lemma binders, not an open hop. The story does not say; no fixture has one except possibly 4WHS.
- Two steps with the same hop and values share the lemmas (checked by the bound lemma's name). Two steps with the same reduction values but different other literals would share a name; no fixture has this.
- The name rule for `Router` works through the file collision; the error names the two files, not a reserved name.
- The story-97 prototypes under `reduction-prototype/hello-world` and `kem-dem` are no longer read by a test. They stay, because `docs/research/reduction-proof-script.md` refers to them.
- `RunArgValue` became `pub` with derives, because `RouterUse` exposes it.

## Tests run

All under `systemd-run --user --scope -p MemoryMax=6G timeout …`, no proving job running, EasyCrypt r2026.09.

| Command | Result |
|---|---|
| `cargo test -p sspverif --lib writers::easycrypt::reduction -- --test-threads=1` | 6 passed |
| `cargo test -p sspverif --lib writers::easycrypt::prop -- --test-threads=1` | 16 passed (merge rule, suffix, propositions) |
| `cargo test -p sspverif --lib writers::easycrypt::export::tests::the_ -- --test-threads=1` | 3 passed (Router name rule, report fields) |
| `DOMINO_EASYCRYPT=… cargo test … --exact` the compile tests of reduction-consts, hello-world, hello-world with a proposition, proposition-open-hop, kem-dem-cca-ssp, and `reduction_prototypes_compile` (now on `layout/`, each file on its own) | 6 passed, 227 s |
| `cargo test -p sspverif easycrypt -- --test-threads=1 --skip 4whs --skip 4WHS` (no `DOMINO_EASYCRYPT`) | one failure, `yao_hybrid_security_reads_declared_theorem_constants_as_parameter_fields` (it finds `easycrypt` on `PATH` and EasyCrypt exits with no output); the run then hit its 1200 s timeout |
| the same yao test at the base commit `f3b4aeb3` (a temporary worktree) | fails the same way: the failure predates this story |
| `cargo clippy --workspace --all-targets` | clean |

CRAP gate: `.sdlc-workspace/crap-coverage.sh` ran, but `sdlc crap gate` fails with `bwrap: loopback: Failed RTM_NEWADDR` (and the repo has no `origin/main`), so the gate was skipped. `reduction_step` was split into `adversary`, `step_sides` and `step_lemmas` to keep each function small.

## Tests written but not run (4WHS: never run on this machine)

- `simple_4whs_reports_the_reduction_hop_and_the_composition_names` (updated for the run lemma and router file): `cargo test -p sspverif --lib simple_4whs_reports -- --test-threads=1`.
- Acceptance §6, by hand: `domino easycrypt export --project example-projects/4WHS --theorem Full4WHS --out <dir>` and check `Prop_main.ec` for `B_.._b_false` and `B_.._b_true` of H1 and H6.

## Notes for story 103

- Replace `oracle_proof` (the ladder in `reduction_lemmas.rs`) with `admit` plus the proof job. Oracle files are `ReductionReport.oracle_files`; `admit_count` counts `admit.` and must then become the oracle count.
- The overwrite guard (ADR 0004) must protect proved `Red_*_<O>.ec` files.
- `assert_tree_compiles` asserts no `admit` in `Red_*` files; relax it for oracle files when they admit.
- `testdata/easycrypt/reduction-prototype/layout/compile.sh` removes all `Prop_*`; reduction-consts now exports `Prop_FlipBound.ec` and `Prop_Free.ec`.
