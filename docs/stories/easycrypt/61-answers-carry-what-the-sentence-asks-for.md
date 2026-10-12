# Story 61 — Answers carry what the sentence asks for (`domino-json/3`)

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export` (Domino) and `amir/domino-easycrypt-integration` (the fork in
`easycrypt/`).
**Depends on:** 54, 55, 60.
**Blocks:** nothing. Stories 64–66 work without it (they ask for `full` until it lands) and get
faster with it.
**ADR:** 0012 (amends 0009).

A **protocol** story, OCaml and Rust. The sentences that a run sends and the proof files do not
change.

---

## 1. Why this story exists

The answers of the Full4WHS runs of 2026-10-08 total 134 GB for 27.3 h of waiting on EasyCrypt
(count of all transcripts, grilling of 2026-10-09/12):

| Answer | Bytes | Wait |
|---|---|---|
| Error answers (failed fallbacks, failed `rewrite`, …) | 31.8 GB (24 %) | 11.9 h (smt time included) |
| Split role (`split.`, `move =>`, `rewrite /op.`), ok | 65.0 GB (49 %) | 7.0 h |
| Other ok answers | 30.1 GB (22 %) | 7.4 h |
| `admit.` | 6.8 GB (5 %) | 0.9 h |

- A sentence that fails changes no goal, but its answer carries the front goal in full. Each of
  the 1,374 failed `rewrite !get_set_neqE.` answers was about 4.4 MB.
- After a split-role sentence, Domino reads only the head of the conclusion.
- In a leaf answer that we measured (2.15 MB, `Eq_H4_H5.ec` replayed to its first leaf), the `ty`
  fields were 1.51 MB (70 %), with only 48 distinct types. `text` was 2 %.

Vocabulary (`CONTEXT.md`): **Front goal** (already changed for this story: the answer gives what the
sentence asked for; a failed sentence gives no front goal).

## 2. Inherited from earlier stories

- **Story 54 / ADR 0009:** each answer has `front` (the first goal in full, with `pp` only where
  Domino reads it) and `kinds` (one kind for each open goal). The fork writes it in
  `ecTerminal.ml` (`Json.proof`, line ~124) and `ecPrinting.ml` (`PPJson.goal`, line ~4395).
- **Story 55:** `timing`. **Story 60:** `parse_ms` and the linear parser.
- The fork's JSON terminal reads sentences with `EcIo.from_channel` on stdin (`from_json#next`).

## 3. Work to do

### 3.1 The request

Each request is one line of JSON:

```json
{"sentence": "smt().", "want": "status"}
```

- `want` is `status`, `head` or `full`. Without `want`, the fork uses `full`.
- The fork parses the line, then parses `sentence` with the existing sentence parser (from a
  string). A line that is not valid JSON gives an error answer, as a parse error does today.
- The answer's `version` is `domino-json/3`.

### 3.2 The answer

| `want` | `front` | `kinds`, `status`, `messages`, `timing`, `state` |
|---|---|---|
| `status` | `null` | yes |
| `head` | the conclusion down to depth 4 (the root is depth 1); a deeper node is a stub with its `kind` and, for an application, its operator; each hypothesis with its name and kind, and for a formula its head at the same depth | yes |
| `full` | as `domino-json/2`, with the type table of §3.3 | yes |

**An error answer has `front: null` for every `want`.** It still has `kinds` (unchanged).

### 3.3 The type table

A `full` (or `head`) answer has `"types": [ … ]`. Each entry is a type, written one time, with its
`pp`, and its subtypes as indices into the same table. Each formula node's `ty` is an index. No type
node has a `pp` except at its table entry.

### 3.4 Domino

- `Session` sends the envelope. Each caller says what it reads:
  - `status`: fallbacks and closing attempts (`try_close`), `admit.`, `undo`, the exit path of
    story 64, the side goal of `rcondt`/`rcondf`.
  - `head`: the opening loop of story 64 (intro, unfold, `do split`).
  - `full`: program goals (the walk, alignment, `sp_counts`), and the key scan of story 66.
- The driver keeps the last front goal it read. After an error answer, the front goal is the one
  it had. After `undo`, the front goal is the one that it had at that state (keep goals by
  EasyCrypt state number, as long as the run can undo to them).
- `Form.ty` becomes an index into the answer's table. The functions that read types (`goals.rs`,
  `align.rs`) look it up.
- The live page and the transcript show the last goal that Domino has. A `status` answer has no
  goal to cap.
- A fork that answers `domino-json/2` stops the run with an error that names both versions and
  `DOMINO_EASYCRYPT`.

### 3.5 Rejected alternatives (see ADR 0012)

- A sticky `pragma Json:…` mode: state on both sides, and a round trip for each mode change.
- Batches of sentences: the driver would need to handle a failure in the middle of a batch.
- Subterm sharing: every matcher would have to work on a graph. Come back to it if the report
  still shows `full` answers as a cost.
- Dropping `text`: 2 % of the measured answer.

## 4. Acceptance criteria

- [ ] Fork: a test session sends `status`, `head` and `full` requests and checks the fields of
      §3.2. A failing sentence gives `front: null` for each `want`.
- [ ] Fork: a `full` answer has a type table; no formula node has an inline type.
- [ ] Domino: a unit test of the driver shows that after a failed sentence and after `undo`, the
      front goal is the one from before.
- [ ] Domino: each `Session::send` call site states its `want`. A test checks that fallbacks ask
      for `status`.
- [ ] Domino with a `domino-json/2` fork stops with the version error.
- [ ] The implementation report gives, for H2_1 ~ H3_0 and H6_1_1 ~ H7_0, total answer bytes and
      the "rest of round trip" before (2026-10-08) and after, and the same leaf answer as above
      measured again.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean. The
      fork builds with `dune build`.

## 5. How to verify

```bash
cd easycrypt && dune build && cd ..
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --proofstep 4 --tactics
# bytes of error answers and of all answers, as in §1
python3 -c "
import json,sys
ok=err=0
for l in open(sys.argv[1]):
    r=json.loads(l)
    if 'sentence' not in r: continue
    if r['response']['status']=='ok': ok+=r['bytes']
    else: err+=r['bytes']
print('error', err/1e9, 'GB; ok', ok/1e9, 'GB')
" <out>/progress/Eq_H2_1_H3_0/ec-transcript.jsonl
```
