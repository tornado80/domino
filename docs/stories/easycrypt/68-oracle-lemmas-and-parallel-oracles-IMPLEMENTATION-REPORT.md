# Story 68 — Implementation report: oracle lemmas and parallel oracles

Rust only. The tactics inside an oracle do not change. **The exported `.ec` files change.**

## What changed

### Translation (the exported files)

- **`Eq_<L>_<R>_<O>.ec`** (new, one for each exported oracle, flat in the export directory):
  the same `require`s as the glue (libraries, the two `Comp_` files, the invariant file), and,
  outside any section,
  `lemma Eq_<L>_<R>_<O> : equiv[<L>.Game_<L>.<p> ~ <R>.Game_<R>.<p> : ={arg} /\ inv … ==> ={res} /\ inv …].`
  with the proof `(* <p> *)` / `+ proc; inline. admit.` (the marker that the proof job replaces,
  as before). The statement is laid out over several lines, `inv` as in the `call`.
- **`Eq_<L>_<R>.ec`** (the glue): unchanged up to the base case; it also
  `require import`s every oracle file, and each oracle bullet is now
  `+ by conseq Eq_<L>_<R>_<O> => /#.` instead of `+ proc; inline. admit.`. It holds no `admit`.
- `ast.rs`: `EcItem::Lemma` (a lemma outside a section) and `EcExpr::OracleEquiv`.
  `render.rs`: `render_invariant_block` (shared by the `call` and the oracle statement) and
  `render_oracle_equiv`. `proof.rs`: `OracleProofFile`, `theory_requires`.
- **Name rule** (`export.rs`, `insert_oracle_files`): the oracle files are added after every
  other file; a name that is already taken, ignoring case, is
  `EcExportError::OracleFileCollision`, which names the oracle and the other owner (another file
  of the export, or another oracle).
- `EquivalenceReport::oracle_files`: `(oracle, file)` in oracle order.

### Proof jobs

- **`tactics/oracles.rs`** (new): the proof job of one equivalence. `plan_job` decides from
  the oracles' records; the oracles go to up to `--jobs N` workers (threads, each with its own
  EasyCrypt process). A worker takes `progress/<Eq>/<O>.lock` (held by another job: the oracle is
  skipped with a message), reads the oracle's record under the lock, opens the oracle lemma
  (`sentences_until_proof`), and runs `tactics_for_oracle` unchanged. It writes only the
  oracle's files: the lemma file, `session/<Eq>/<O>.record.json`, `<O>.tree.json`, and
  `progress/<Eq>/<O>/` (page, transcript, report, temporary files).
- The job writes `progress/<Eq>/index.html` (one row for each oracle: pending, running, done,
  proved earlier, skipped) and `progress/<Eq>/report.txt` (the oracles' sections in oracle order)
  — only without `--oracle`; with `--oracle` the oracle's own report is the report.
- With one worker, one progress observer (`SharedProgress`) gets one `tactics` phase with one
  item for each oracle, as before.
- **Records** (`job.rs`): `oracle_record_path`, `SessionRecord::only`, `SessionRecord::join`
  (pending for oracles without a record), `split_equivalence_record` (an old whole record, at
  story 67's or the older path, is split into one record per oracle with `create_if_absent`;
  the old file stays). `--force` removes the oracles' records and both old records; `--force
  --oracle O` removes `O`'s record.
- **Locks**: `ProofLock::acquire(path, job)`, `oracle_lock_path`; `live_jobs` reads
  `progress/*/<O>.lock` and the old `progress/*/lock`; `LiveJob::job` (was `equivalence`).
- `is_proof_file` is replaced by `is_oracle_file(exported, rel)`: the glue is now a translation
  file, created when missing and never rewritten.
- **Seal / respawn**: each oracle has its own EasyCrypt, so the respawn of story
  "tactics-run-survives-an-unanswered-interrupt" is the next oracle's fresh session.
  `Unanswered::respawn` is replaced by `ended_job`; after `MAX_RESPAWNS` (2) unanswered
  interrupts the next one ends the job, as before. `respawn()` and the base-case handling of
  `open_proof` are removed; `base_case_admitted` is removed (the base case is the glue's).
- `OracleTactics::transcript` (the oracle's transcript); `EquivalenceTactics::transcript` is
  removed. `SwallowWatch` is `Arc<Mutex<…>>`. `run_tactics*` need `P: Sync, B: Sync`.
- **CLI**: `prove --jobs N` (default 1); doc of `--oracle`, `--force`, `--write-granularity`.

### Rejected shape

A worker per oracle as a child `domino` process (`prove --oracle O`). Rejected: one live page
and one report would need a second process protocol, and the test EasyCrypt of the unit tests is
per thread. Threads in one process share the plan, the board and the page.

## Deviations

- The glue closes an oracle with `by conseq <lemma> => /#.`, not `by conseq <lemma>.`: the
  `call` goal names the oracle's parameters (`d_U{1} = d_U{2} /\ …`) where the lemma has
  `={arg}`, so `conseq` leaves that side condition (Simple4WHS, found by the compile test).
- A job with `--oracle` writes neither the equivalence's page nor its report (no file has two
  writers).
- A second job on a locked oracle skips it with a message (exit 0); before, a locked equivalence
  was an error.
- **Wall time of H6_1_1 ~ H7_0 with `--jobs 1` and `--jobs 4`: not measured.** The owner asked
  not to run EasyCrypt proofs on the Full4WHS hops.

## Fixed on the way

- The live tests of `tactics/tests.rs` were behind `cvc5-lib` and did not compile (story 61's
  `Session::send(…, Want)`). They now compile without the feature, with the new
  `IncrementalCvc5Backend` (`cvc5 --incremental` as a process) in `process.rs`. Stale
  expectations fixed: the leaf of story 64, the `pragma` of story 61, the unanswering fake (it
  counted from `call (`; now from `proof.`, and hangs at `N0` again).

## Tests

- New: `export.rs` `each_oracle_has_a_lemma_file_and_the_glue_closes_it_with_conseq`,
  `the_name_rule_rejects_an_oracle_called_invariants_and_names_both_files`; the full-tree
  compile tests compile each oracle file, then the glue (Simple4WHS: every oracle admitted,
  `easycrypt compile Eq_<L>_<R>.ec` passes).
- `job.rs`: `only_the_oracle_lemma_files_are_proof_files`,
  `ensure_translation_files_creates_the_missing_glue_and_invariants_but_not_an_oracle_file`,
  `a_record_of_the_whole_equivalence_is_split_into_one_record_per_oracle_on_first_use`, lock
  tests on oracle locks.
- `tactics/tests.rs`: `a_job_resumes_from_an_old_whole_equivalence_record_split_on_first_use`,
  `an_oracle_without_a_record_makes_the_equivalence_partial`; live:
  `two_proof_jobs_on_different_oracles_of_one_equivalence_both_finish_with_their_own_files`,
  `three_jobs_prove_three_oracles_at_once_and_the_report_keeps_oracle_order` (a logging
  EasyCrypt: 4 started, 3 at once).

## Results

- `cargo test --lib`: 736 passed, 0 failed, 5 ignored.
- Live, with `DOMINO_EASYCRYPT` = story 61's `ec.exe` and `cvc5` on `PATH`:
  `cargo test --lib easycrypt` minus 8 tests: 531 passed. The 8 skipped tests use
  `hello-world-oracle-rename-new`, whose lockstep execution hangs in a claim check with the
  process cvc5 (also before this story); they need `cvc5-lib`. **Open.**
- `cargo test -p domino --test easycrypt_overwrite`: 9 passed.
- `cargo clippy --workspace --all-targets`: no warnings in the changed files.
- `cargo build --release --workspace`: OK.
- `--features cvc5-lib`: cannot build here (no cmake). The CLI `prove` path and the integration
  tests behind it (`easycrypt_prove`, `easycrypt_ctrl_c`: paths and the skip updated, not
  compiled; `easycrypt_tactics_writes`, `easycrypt_stage_messages`: not updated, and already on
  `domino-json/2`) are not compiled or run. **Open.**
- Complexity: the sdlc gate does not score Rust; CC is UNMEASURED. The new functions are small;
  `prove_oracle` and `walk_oracle` are the largest (one `match` each, one labelled block).
