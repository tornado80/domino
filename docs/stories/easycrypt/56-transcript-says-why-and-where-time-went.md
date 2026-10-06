# Story 56 — Each transcript record says why its sentence was sent, and the transcript accounts for all the time

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 27 (tactic generation), 52 (quick close and fallbacks), the story
`tactics-run-survives-an-unanswered-interrupt` (respawn).
**Blocks:** 57 (time by role). It is independent of 53, 54 and 55.

A **logging** story, Domino only. The tactics that a run sends do not change.

---

## 1. Why this story exists

In the Full4WHS analysis we could not say from the transcript why a sentence was sent, or where a
large part of the time went:

- **`ctx` is free text.** The driver sets it with `Session::set_context`
  (`src/easycrypt/session.rs:405`) at three places: `"<oracle> N<idx> <kind>"`
  (`src/easycrypt/tactics/driver.rs:1110`), `"<oracle> N<idx> <kind> (<resume mode>)"`
  (`driver.rs:1021`) and `"<oracle> router prelude"` (`driver.rs:1632`). It names the node, not
  the reason. To find which sentences were quick closes, leaf fallbacks or admits, we classified
  sentence text with `grep`, and one pattern (`sp `) also matched `split`.
- **The answer size is lost.** The capped transcript cuts the answer. The size of the original
  answer (25–28 MB at Full4WHS leaves) was visible only in a full transcript.
- **Time outside sentences is not recorded.** The report's EasyCrypt time is
  `began.elapsed()` (`src/easycrypt/tactics/mod.rs:1645`). It includes Domino's own work between
  sentences: parsing large answers, checkpoints (`driver.rs:568`), transcript writes. It also
  includes the interrupt grace and resend waits (`INTERRUPT_GRACE` 30 s, `INTERRUPT_RESEND` 5 s,
  `session.rs:41-46`, `interrupt_until_answered` at `session.rs:505`) and respawns
  (`tactics/mod.rs:1134`). For H2_1 ~ H3_0, oracle `Send3`, the sum of `ms` in the transcript was
  936 s less than the report's EasyCrypt time.

Vocabulary (`CONTEXT.md`): **Sentence role**, **Quick close**, **Fallback sequence**, **Leaf**,
**Interrupt**, **Respawn**, **EasyCrypt transcript**.

## 2. Inherited from earlier stories

- **Story 27 / 31:** one transcript record per sentence:
  `{"file", "ctx", "sentence", "ms", ["interrupts"], "response"}` (`src/easycrypt/transcript.rs:118`,
  `record`). Records are only appended; the live page keeps the byte offset of each record
  (`session.rs:173-180`).
- **Story 52:** the names quick close, side-goal fallback, leaf fallback, part fallback. Each
  fallback sequence has an order, so a fallback has a number in its sequence.
- **Respawn story:** a sentence that does not answer within the grace gets EasyCrypt killed and a
  new process started; the accepted sentences are sent again.
- Nothing on the pages reads `ctx` today. Two tests do: `session.rs:1105` and the fixture at
  `tactics/live/tests.rs:375`.

## 3. Work to do

### Structured `ctx`

- `ctx` becomes an object:

  ```json
  "ctx": {"oracle": "Send3", "node": 41, "kind": "leaf", "role": "leaf-fallback", "n": 2, "part": "Domino_invariant"}
  ```

  - `oracle`: always present.
  - `node` and `kind`: the joint node and its kind, when there is one (not in the router
    prelude).
  - `role`: one of `quick-close`, `structure`, `side-goal-fallback`, `leaf-fallback`, `reduce`,
    `split`, `part-fallback`, `admit`, `undo`, `resume`. The router prelude is `structure`. These
    are the **Sentence roles** of `CONTEXT.md`.
  - `n`: the 1-based number of the tactic in its fallback sequence; only for the three fallback
    roles.
  - `part`: the label of the claim, only for `part-fallback` and for an `admit` of a part.
- The driver sets the context through a typed value (for example `SentenceCtx { oracle, node,
  kind, role, n, part }`), not a string. The place in the driver that chooses a tactic also sets
  its role. Do not guess the role from the sentence text.
- `undo` sentences that the session sends itself get role `undo`, with the `node` of the sentence
  they take back.

### Answer size

- Each sentence record gets `"bytes"`: the length of EasyCrypt's answer line before any cap.

### Time outside sentences

- Add **event records**. They have `file`, `ctx`, `event` and `ms`, and no `sentence` or
  `response`:
  - `"event": "interrupt"`: the time from the first interrupt to the answer or to the end of the
    grace, with `"resends"`: the number of signals sent again.
  - `"event": "respawn"`: the time to kill EasyCrypt, start it again, and send the accepted
    sentences again.
  - `"event": "between"`: Domino's own time between the answer to one sentence and the send of the
    next one. Write it when it is ≥ 100 ms, and fold shorter gaps into the next `between` record,
    so that small gaps are not lost and the file does not double in length.
- The `ms` of all records of one oracle (sentences and events) adds up to the report's EasyCrypt
  time of that oracle, within 1 %.
- The live page skips event records where it reads sentence records.

### Rejected alternatives

- **A longer `ctx` string** (`"Send3 N41 leaf leaf-fallback#2"`). Rejected: every reader has to
  parse it again, and a new field changes the format of the string.
- **Guess the role from the sentence text.** Rejected: the same sentence (`smt().`) is a quick
  close, a fallback or a part fallback, depending on where the driver is. The analysis showed such
  guesses go wrong.
- **One `between` record after every sentence.** Rejected: it doubles the number of records for
  little information.

## 4. Acceptance criteria

- [ ] Every sentence record has `ctx` as an object with `oracle` and `role`. A unit test drives a
      small tree with the fake EasyCrypt and checks the roles of a quick close, a leaf fallback, a
      split, a part fallback and an admit.
- [ ] Every sentence record has `bytes`, the length of the uncapped answer.
- [ ] Event records exist for interrupts and respawns. A session test with a fake EasyCrypt that
      does not answer checks an `interrupt` record.
- [ ] For every oracle of a Full4WHS run, the `ms` of its records sums to its EasyCrypt time in the
      report, within 1 %. The implementation report gives the H2_1 ~ H3_0 `Send3` numbers.
- [ ] The live page still shows every sentence, and no event record shows up as a sentence.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --tactics
T=<out>/*/ec-transcript.jsonl
jq -r 'select(.sentence) | .ctx.role' $T | sort | uniq -c
jq -s 'map(select(.ctx.oracle == "Send3")) | map(.ms) | add' $T   # compare with the report
jq -c 'select(.event)' $T | head
```
