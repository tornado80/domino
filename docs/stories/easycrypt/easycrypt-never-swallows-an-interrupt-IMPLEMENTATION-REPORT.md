# Story `easycrypt-never-swallows-an-interrupt` — implementation report

**EasyCrypt commits:** `7212a43e` (the work) and `33591d43` (review fixes) on `amir/domino-easycrypt-integration` (clone at `easycrypt/`).
`tactics-run-survives-an-unanswered-interrupt` can cite `7212a43e` in its swallow warning.

## What changed (EasyCrypt clone)

- **`src/ecProvers.ml`**
  - §3.1: `is_interrupt : exn -> bool`. True for `Sys.Break`, and recursively through
    `Trans.TransFailure`, `Strategy.StratFailure` and `Loc.Located`, which are the Why3
    exceptions that wrap an `exn`. `run_prover`'s catch-all now starts with
    `| e when is_interrupt e -> raise Sys.Break`, so the exception is re-raised unwrapped and
    `toperror_of_exn_r` maps it to `interrupted`.
  - `execute_task`'s `try_finally` clean-up runs no matter which `run` raises. It interrupts and
    waits for every prover already stored in `pcs`, so a prover started before the interrupting
    `run` is killed. A prover whose start raised is never stored, so nothing leaks.
  - §3.3: `maybe_start_why3_server` no longer sets `SIGINT` to ignore in the parent. The forked
    child ignores it after `fork` and before `execvp` (the ignore disposition survives `exec`).
- **`src/ecTerminal.ml`** (§3.4)
  - `idle` now means "no sentence in flight". It starts `true`, is set again at the top of
    `next` (so `drain` is covered), and after every answer, including one that raises (in the
    `finally`, so `ec.ml`'s handler cannot write a second line). It is cleared once the sentence is
    parsed.
  - `finish` answers inside a window where `SIGINT` has a no-op handler, so the signal is
    recorded and dropped. The previous behaviour is restored afterwards. An interrupt during
    `answer` can no longer escape to `ec.ml`'s handler and produce a second line. Neither can one
    between the answer and the next parse. `Json.proof` keeps its own catch-all.
- **`src/ecLowGoal.ml`**: not in the §3.2 list, but found by the harness (see below).
  `t_absurd_hyp` turned *every* exception into `InvalidGoalShape`, which `t_try` then caught. A
  `SIGINT` that landed in the reduction run by `auto => />` (crush) was therefore silently lost.
  The same pattern was in `LowApply`'s module-type check (`InvalidProofTerm`). Both now re-raise
  `Sys.Break`.
- **`doc/json-output.md`** (§3.5): an "Interrupts" paragraph with the three guarantees. The format
  and the version `domino-json/1` are unchanged.
- **`scripts/testing/sigint-stress`**: the §4 harness (described below).

## §3.2 audit of the `smt` path

| Handler | Verdict |
|---|---|
| `ecProvers.ml` `run_prover`, `with e ->` | fixed with `is_interrupt` |
| `run_prover` `doit`, `Unix_error (ENOMEM, "fork")` | cannot see an interrupt |
| `maybe_start_why3_server_`: `Unix_error` on close, `ConnectionError` on connect, `Unix_error` on kill | cannot see an interrupt (specific exceptions) |
| `execute_task` clean-up, `try wait_on_call … with _ -> ()` | deliberately kept. It runs only while an exception is already unwinding, and swallowing a second `Break` there lets the clean-up finish and the first exception propagate. |
| `Evictions` (`E.Evict`), `get_prover` (`Not_found`, `CannotFindProver`), `is_prover_known` (`UnknownProver`) | cannot see an interrupt |
| `ecSmt.ml`: `Not_found`, `E.MFailure`, `CanNotTranslate` handlers; `try_finally`s in `check` | cannot see an interrupt (specific exceptions; `try_finally` re-raises) |
| `ecLowGoal.ml` `t_smt` | no handler; a `false` from `EcSmt.check` becomes `cannot prove goal` |
| Why3 `Call_provers.actualcommand`, `Prove_client.connect` `with e ->` | re-raise, harmless |

Catch-alls outside the `smt` path that were seen but left alone, as §3.2 asks: `ecPV.ml:482,988`,
`phl/ecPhlEqobs.ml:483,552`, `phl/ecPhlBDep.ml:113`, `phl/ecPhlFun.ml:210`,
`phl/ecPhlFel.ml:134`, `ecTyping.ml:1065`. Each can turn an interrupt into a tactic error in
`sim`, `proc`, `fel` and similar tactics.

## Verification

### Harness (§4 criteria 1–3)

`scripts/testing/sigint-stress --transcript T --dir D --slow N [-n 50] [-v]` replays every `ok`
sentence of a Domino transcript before line `N`, then sends `SIGINT` to sentence `N` at random
offsets. A synthetic record goal did not work: EasyCrypt took minutes to elaborate it while
Why3 handled it in under a second. So the harness uses the real 4WHS goal: `Eq_H2_1_H3_0`,
line 34, `auto => /> &1 &2 *; smt().`, about 30–50 s uninterrupted.

```
slow sentence: error in 29.3s
during: 50 trials passed; error: 5 (signal to answer: median 0.7s, max 1.6s),
        interrupted: 45 (signal to answer: median 1.6s, max 1.7s)
between: 50 trials passed
print: 50 trials passed; ok: 50
server: why3server survived SIGINT and was reused
```

The 5 `error` answers had their signal sent 26.6–28.8 s into a 29.3 s sentence, so it arrived as
the sentence finished. A debug build that logged where `SIGINT` lands showed no handler run in
that case. Every trial gave exactly one line and no `Sys.Break` message, and the session answered
the next sentence.

Before the `ecLowGoal.ml` fix, about 1 trial in 4 swallowed the signal and ran to completion
(`cannot prove goal (strict)` after about 20 s). The debug build placed every one of those
signals inside `t_absurd_hyp` → `gen_find_in_hyps` → reduction.

### 4WHS `prove` on proofstep 4 (§4 criterion 4)

Release Domino with the fixed `ec.native`: `12 oracles, 123 goals closed, 22 admits, 6605.1s`,
exit 0. No `Unresponsive`.

| | baseline (§1) | this run |
|---|---|---|
| `error when starting … Sys.Break` | 7 | 0 |
| any `Sys.Break` message | — | 0 |
| interrupted 2 s attempts (send to answer) | 3.8–5.0 s | n=128, median 3.2 s, max 9.4 s |
| unanswered | 1 | 0 |

Remaining gap: 8 of 143 interrupted sentences needed more than one signal (Domino's 5 s resend
from the counterpart story): five `auto => /#.` attempts with 2 signals, and three
`auto => /> &1 &2 *; smt().` with 2–4. All 8 are `auto`/crush sentences. The remaining loss is
therefore most likely another catch-all, or a long stretch without poll points, in EasyCrypt's
tactic or reduction code outside the `smt` path this story covers. A follow-up can find it with
the same technique: a `SIGINT` handler that prints `Printexc.get_callstack`.

### Build and tests (§4 criterion 5)

`make` builds clean. `make unit`: 108/108 pass.

## Review

Two-axis review (standards, spec). Fixed: `idle` is set in the `finally` so that an answer that
raises cannot be followed by a second line, and the now-empty `maybe_start_why3_server` wrapper is
gone. Known and not fixed:
- `idle` is still true during `xparse`, inherited from story 25. A `SIGINT` while a sentence is
  only partly read is dropped. Domino writes each sentence in one write, so this does not arise in
  practice.
- The `ecLowGoal.ml` re-raises go beyond §3.2's scope. They are kept because the harness showed
  they were the main cause of lost interrupts on 4WHS. They match a bare `Sys.Break`: no Why3
  wrapper can reach that code.
- The `Strategy.StratFailure` and `Loc.Located` cases in `is_interrupt` come from reading Why3's
  exception declarations (`grep 'exception.*exn'`). Only `TransFailure` was seen in a transcript.

## Upstreaming

The `run_prover` and `why3server` changes, and the two `ecLowGoal.ml` re-raises, are independent
of `cli -json` and worth offering upstream separately. That is not done here.
