# Story 55 — Implementation report: each answer says where EasyCrypt spent its time

**EasyCrypt commit:** `0b9695b2` on `amir/domino-easycrypt-integration` (clone at `easycrypt/`).
The Domino commit moves the submodule pointer to it from `cc719556`.

## What changed (EasyCrypt clone)

- **`src/ecTiming.ml{,i}` (new).** The sums of one sentence, in one global record. `reset`
  starts a sentence. Three wrappers collect the times: `check` (around `EcSmt.check`), `call`
  (around `EcProvers.execute_task`, with a function that gives the outcome of the call) and
  `prepare` (around `Driver.prove_task`). `smt ()` gives the sums, or `None` when no prover was
  called. No argument goes through the tactic engine.
- **`src/system/eunix.c`, `EUnix.monotonic`.** `CLOCK_MONOTONIC` in seconds. OCaml's `Unix` has
  no monotonic clock, and the switch has no `mtime` package.
- **`src/ecSmt.ml`, `src/ecProvers.ml`.** One wrapper each. `execute_task` sets a flag when a
  prover answers `Timeout`. The outcome is `valid` for `Some true`, `timeout` for `None` with the
  flag set, and `unknown` for all other results. A call that raises (an interrupt) counts as
  `unknown`.
- **`src/ecTerminal.ml`.** `next` resets the sums and notes the time after the parse. `answer`
  measures `tactic_ms` up to the start of `Json.proof`, and `serialize_ms` for `Json.proof`. The
  new field `timing` comes after `proof`. The version stays `domino-json/2`.
- **`doc/json-output.md`.** New section "Timing". It says that the final write of the line is
  not in `serialize_ms`.

How the parts are computed:

- `translate_ms` = time in `check` − time of the `call`s made in it. This is the translation
  before the first call, plus the build of the task of each call (`make_task`).
- `prepare_ms` = time in `Driver.prove_task`, summed over all provers of all calls.
- `prover_ms` = time in `call` − `prepare_ms`. Provers that start late from the queue have
  their preparation inside the wait of the others, so with more provers than `pr_maxprocs`,
  `prover_ms` is a little low. EasyCrypt's default has fewer provers than `pr_maxprocs`.
- All times are rounded **down** to whole milliseconds. A first run rounded to the nearest
  value and gave 2 records (of 262) with `tactic_ms + serialize_ms` = `ms` + 1 (for example
  11 + 0 > 10). Domino's `ms` is `as_millis`, which also rounds down, and
  ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋.

## What changed (Domino)

- **`json.rs`.** `Response.timing: Option<Box<Timing>>`, with `#[serde(default)]`.
  `Timing { tactic_ms, serialize_ms, smt: Option<SmtTiming> }`. The box keeps `session::Wait`
  small (the same clippy warning as story 54).
- **Transcript.** No code change: `cap_response` already keeps every field but `proof` verbatim.
  A new test keeps this fact for `timing`.

## Rejected shapes

- **Thread a timing record through `EcSmt.check` and `execute_task` as an argument.** Rejected
  by the story: it changes the signatures of the tactic engine.
- **Measure `translate_ms` with timers at each translation site** (`init`, `select`,
  `make_task`). Rejected: three timers in `ecSmt.ml` in place of one wrapper. "Time in `check`
  minus time in calls" gives the same number.
- **Measure `prover_ms` from the start of the first prover process.** Rejected: Why3 does not
  tell when the process started. "Call minus preparation" needs no Why3 change.
- **A separate `interrupted` count.** Rejected: the story fixes three counts that sum to
  `calls`. An interrupted call is `unknown`.
- The rejected alternatives of the story stay rejected.

## Tests

- Baseline: `cargo test --workspace`: 625 passed, 0 failed, 5 ignored.
- New tests:
  - `json::tests::an_answer_without_timing_parses` and
    `json::tests::an_answer_with_timing_parses_with_and_without_smt` (red before `Timing`).
  - `transcript::tests::both_records_keep_timing_verbatim` (capped and full). It was green at
    once: `cap_response` already kept the field. It is kept as a guard.
  - `session::tests::an_smt_answer_says_where_its_time_went` (real EasyCrypt): a lemma
    statement has `timing` and no `smt`; `smt().` has `calls ≥ 1`, the three counts sum to
    `calls`, and `valid ≥ 1`.
- After: `cargo test --workspace`: 629 passed, 0 failed, 5 ignored. `cargo test --lib easycrypt`
  with `DOMINO_EASYCRYPT` set to the new `ec.native`: 448 passed, 1 ignored.
  `cargo clippy --workspace --all-targets`: no warnings.
- **`--features cvc5-lib` was not checked:** `cvc5-sys` needs `cmake`, which is not on this
  machine (story 52 had the same problem). The change does not touch code under that feature.
- EasyCrypt: `dune build` clean. Unit tests (`scripts/testing/runtest config/tests.config
  unit`, with a temporary `easycrypt.project` for `Z3@4.13` and `CVC5@1.3`, then restored):
  108/108 pass.
- The check of §5 gives, for `smt().`:
  `{"tactic_ms":142,"serialize_ms":0,"smt":{"calls":1,"translate_ms":2,"prepare_ms":5,"prover_ms":134,"valid":1,"timeout":0,"unknown":0}}`,
  and for a lemma statement `{"tactic_ms":0,"serialize_ms":1}`. A false goal gives
  `"unknown":1`.

## Runs on `example-projects/4WHS` (Full4WHS, H0 ~ H1_0)

Both runs use the new `ec.native` and the release `domino` of story 54 (built with
`cvc5-lib`; it writes the answer verbatim, so it writes `timing`).

| run | transcript | result | records | with `timing` | `smt` | tactic + serialize > ms |
|-----|------------|--------|---------|---------------|-------|-------------------------|
| 1 (rounded to nearest) | full | 102 goals closed, 0 admits, 345 s | 262 | 262 | 103 | 2 |
| 2 (rounded down)       | capped | 100 goals closed, 0 admits, 215 s | 258 | 258 | 102 | **0** |

In all records with `smt`, `valid + timeout + unknown = calls`.

### Split of a slow SMT sentence

H0 ~ H1_0 has no slow `smt().`: its `smt()` sentences take at most 118 ms. The SMT calls are in
`auto => /#.`. The slowest one (run 1, leaf `Send4 N6 synchronized`, 5,769 ms wall):

| tactic | serialize | translate | prepare | prover | result |
|--------|-----------|-----------|---------|--------|--------|
| 5,619 ms | 113 ms | 27 ms | 478 ms | 5,088 ms | valid |

Typical slow ones in run 2 (about 2 s, just under the quick-close limit, valid):
`Send3 N25 determined`: translate 36, prepare 1,441, prover 405 ms.

Sum over all SMT sentences:

| run | wall (ms) | translate | prepare | prover | serialize |
|-----|-----------|-----------|---------|--------|-----------|
| 1 | 100,050 | 5,157 | 49,851 | 19,263 | 9,420 |
| 2 | 71,511 | 3,970 | 40,535 | 9,743 | 5,212 |

On this proofstep **Why3's preparation (`Driver.prove_task`), not the prover, takes most of the
SMT time**: about half of the wall time of the SMT sentences, and 2-4 × the prover time. This
time is outside the 3 s prover limit. In run 1, 17 sentences at the 2 s quick-close limit were
interrupted while Why3 prepared the task (`prover_ms` = 0). Story 57 will show this per role.

## Open items

- `--features cvc5-lib` build, test and clippy: not run (no `cmake`).
- The criterion on `ms` is checked on H0 ~ H1_0 only (runs of more than 10 minutes were not
  done). The other proofsteps use the same code path.
- No slow `smt().` exists in H0 ~ H1_0; the split above is of `auto => /#.`, which calls the
  same `EcSmt.check`.
