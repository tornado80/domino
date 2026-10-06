# Story 55 — Each answer says where EasyCrypt spent its time

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 54 (`domino-json/2`).
**Blocks:** 57 (time by role).

A **logging** story. Work in the EasyCrypt fork (`easycrypt/`, OCaml) and a little in Domino. The
tactics that a run sends do not change.

---

## 1. Why this story exists

Today Domino measures one number per sentence: the wall time from send to answer (`"ms"` in the
transcript). It cannot tell what that time was. In the Full4WHS analysis we had to guess from the
sentence text whether a slow `smt().` spent its time in the prover, in translation, or in writing
the answer. Some facts that the analysis found only by reading the fork's code:

- The SMT time limit is `pr_timelimit` (3 s) × `pr_cpufactor` (1), passed to Why3 as the prover's
  `limit_time` (`easycrypt/src/ecProvers.ml:516`). Only the prover runs under this limit.
- Translation of the goal (`ecSmt.ml`, `check` at line 1684) and `Driver.prove_task`
  (`ecProvers.ml:522`: Why3 transformations such as `eliminate_epsilon`, and the start of the
  prover process) run outside the limit.
- A successful `smt()` had a median of 10.8 s, although the limit is 3 s.

Without numbers from inside EasyCrypt, the owner cannot decide whether to make goals smaller,
change prover options, or change tactics.

Vocabulary (`CONTEXT.md`): **EasyCrypt transcript**.

## 2. Inherited from earlier stories

- **Story 54:** each answer is `domino-json/2` and small. Serialization of the front goal is now
  cheap, but it is still measured here, so that the claim stays checked.
- **Story 25:** the answer is built in `ecTerminal.ml` (the `Assoc` with `version` at about line
  225). `Json.proof` builds the `proof` field.
- **SMT call path in the fork:** `EcSmt.check` (`ecSmt.ml:1684`) translates the goal and calls
  `select` (line 1666), which can call `execute_task` more than once (lemma selection). Each call
  goes to `EcProvers.execute_task` (`ecProvers.ml:552`), then `run_prover` (line 503), then
  `Driver.prove_task` (line 522). The answer is collected with `CP.wait_on_call` (about line 668).
  Up to `pr_maxprocs` (3) provers run at the same time.
- **Transcript record** (`src/easycrypt/transcript.rs:118`, `record`): `file`, `ctx`, `sentence`,
  `ms`, `interrupts` (only when > 0), `response`. In capped mode every field of the answer except
  `proof` is kept verbatim.

## 3. Work to do

### The fork

- Each answer gets an optional field `"timing"`:

  ```json
  "timing": {
    "tactic_ms": 812,
    "serialize_ms": 3,
    "smt": {
      "calls": 2,
      "translate_ms": 140,
      "prepare_ms": 95,
      "prover_ms": 6120,
      "valid": 1, "timeout": 1, "unknown": 0
    }
  }
  ```

  - `tactic_ms`: the time to run the sentence, `smt` included, serialization excluded.
  - `serialize_ms`: the time to build the `proof` field (`Json.proof`). The final string write is
    not in it, because it happens after the field is built; say so in `json-output.md`.
  - `smt`: present only when the sentence called a prover. `calls` counts calls to
    `execute_task`. `translate_ms` is the time in `EcSmt.check` before the first
    `execute_task`, plus the translation of each later call. `prepare_ms` is the time in
    `Driver.prove_task`. `prover_ms` is the wall time from the start of the provers to the end of
    `wait_on_call`, summed over calls. `valid`, `timeout` and `unknown` count the results of the
    calls.
- The field is optional and adds information only. **The version stays `domino-json/2`.**
  Document it in `json-output.md`.
- Use a monotonic clock. Collect the sums in a small record that is reset at the start of each
  sentence; do not thread arguments through the tactic engine.

### Domino

- `json::Response` gets `timing: Option<Timing>`, with `#[serde(default)]`. An answer with no
  `timing` parses.
- The transcript keeps `timing` in capped mode too (it is part of the answer, not of `proof`).
- **Leave alone:** the per-sentence timeout, the prover options, the report (story 57 reads these
  numbers).

### Rejected alternatives

- **One transcript record per SMT call.** Rejected: it makes the transcript longer, and the
  report needs only the sums per sentence. Add it later if a sum looks wrong.
- **Measure only on the Domino side.** Rejected: Domino sees one wall time per sentence and cannot
  split it into tactic, prover and serialization.
- **Bump the version to `domino-json/3`.** Rejected: an optional field that an older Domino
  ignores is not a protocol change.

## 4. Acceptance criteria

- [ ] An answer to `smt().` has `timing.smt` with `calls` ≥ 1 and the three result counts summing
      to `calls`.
- [ ] An answer to a sentence that calls no prover has `timing` with no `smt`.
- [ ] `tactic_ms` + `serialize_ms` ≤ the wall time Domino measures for the sentence, for every
      record of a Full4WHS run.
- [ ] Domino parses answers with and without `timing`. A unit test covers both.
- [ ] The capped and the full transcript both keep `timing`.
- [ ] The implementation report gives, for one Full4WHS leaf, the split of a slow `smt().`:
      translate, prepare, prover.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
- [ ] The EasyCrypt fork builds (`dune build`) and its own tests pass.

## 5. How to verify

```bash
printf 'require import AllCore.\nlemma t (x:int): x + 0 = x.\nproof.\nsmt().\n' \
  | $DOMINO_EASYCRYPT cli -json | tail -1 | jq .timing
# {"tactic_ms": …, "serialize_ms": …, "smt": {"calls": 1, …, "valid": 1, …}}

cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --tactics
jq -c 'select(.response.timing.smt) | [.ms, .response.timing.smt.prover_ms]' <out>/*/ec-transcript.jsonl | head
```
