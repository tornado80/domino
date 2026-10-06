# Story 54 — EasyCrypt's answers carry only the front goal (`domino-json/2`)

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 25 (the JSON mode of the EasyCrypt fork), 27 (tactic generation), 41 and 51 (the
capped transcript).
**Blocks:** 55 (timing in each answer), 57 (time by role). It is independent of 53 and 56.
**Decision record:** ADR 0009 (`docs/adr/0009-easycrypt-answers-carry-only-the-front-goal.md`).

Work in **two places**: the EasyCrypt fork (`easycrypt/`, OCaml) and Domino (Rust). They change
together, because the protocol version changes.

---

## 1. Why this story exists

The Full4WHS analysis (eighth design session) found where proving time goes. It does not go to
smt. It goes to the answer that EasyCrypt writes after **each** sentence:

- `Json.proof` (`easycrypt/src/ecTerminal.ml:118-135`) serializes **every** open goal
  (`EcCoreGoal.all_opened pf`).
- `PPJson` (`easycrypt/src/ecPrinting.ml:4025-4401`) puts a `pp` string on **every** node of every
  formula and expression tree. A node's `pp` contains the `pp` of all its subnodes again, so the
  cost of one goal is about O(size × depth).
- At a leaf with 16–17 open goals, one answer is 25–28 MB. `split.` takes about 16 s, `admit.`
  3–42 s, and `undo` up to 10.6 s, although EasyCrypt's own work for these tactics is almost zero.
- The final `Eq_H4_H5.ec` compiles in batch mode (`easycrypt compile`) in **515 s**. The same
  sentences took about **4,366 s** when the tactics run sent them over JSON.

Domino reads almost none of this:

- It reads only `goals[0]` in full (`Driver::front`, `src/easycrypt/tactics/driver.rs:578`).
- Of the other goals it reads only the number (`Driver::count`, `driver.rs:469`;
  `goals_left`, `src/easycrypt/tactics/live/mod.rs:757`) and whether `goals[1]` and `goals[2]`
  are program judgements (`driver.rs:1288-1289`, `1350-1351`, `1648-1649`, `1733`).
- It reads `pp` only on statements, conditions and lvalues (`src/easycrypt/skeleton.rs:116-127`,
  `driver.rs:1369`, `driver.rs:1709`, and `align.rs` through the skeleton), and on the root of the
  front goal's conclusion (the admit label, `driver.rs:702`). It reads the front goal's `text` for
  the transcript and the page (`src/easycrypt/transcript.rs:151-231`).

Vocabulary (`CONTEXT.md`): **Front goal**, **goal kind**, **EasyCrypt transcript** (capped and
full).

## 2. Inherited from earlier stories

- **Story 25:** `easycrypt cli -json` writes one JSON line per sentence. The protocol is described
  in `easycrypt/doc/json-output.md`. Its version string is `domino-json/1`
  (`ecTerminal.ml:119`, `src/easycrypt/json.rs:16` `FORMAT_VERSION`). `Session` refuses any other
  version.
- **Story 27:** the driver's shape checks before `if.` and before a two-sided step look at the
  kinds of the second and third goal.
- **Stories 41 and 51:** the capped transcript keeps the first goal only, cut into its conclusion
  (`GOAL_CONCL_CAP` = 4,000 characters) and its hypotheses (`GOAL_HYPS_CAP` = 1,000). The page
  reads the goal text back from the transcript (`src/easycrypt/tactics/live/page.rs:552-615`).
  `--ec-transcript full` writes each answer verbatim.
- The session tests start fake EasyCrypt scripts that print `domino-json/1` answers
  (`src/easycrypt/session.rs` tests). The version string also occurs in `json.rs`,
  `easycrypt/mod.rs`, `transcript.rs`, `tactics/tests.rs` and `tactics/live/tests.rs`.

## 3. Work to do

### The protocol: `domino-json/2`

- `proof` becomes `{"front": <goal>, "kinds": ["program" | "formula", …]}`. `front` is the first
  open goal, in the same goal shape as today (`id`, `tvars`, `hyps`, `concl`, `text`). `kinds` has
  one entry for **every** open goal, the front goal included. The number of open goals is its
  length. `"program"` means a judgement over two programs (today's `equivS`); every other
  conclusion is `"formula"`. With no open goal, `proof` is `{"front": null, "kinds": []}`; with no
  proof, `proof` is `null`, as today.
- **`pp` stays only where Domino reads it:** the root of the conclusion, the root of each
  hypothesis, and statements, conditions and lvalues of program code. Formula and expression
  subnodes have no `pp`. The front goal keeps `text`.
- A value binder (`GTty`) is written with `"kind": "var"`, not `"type"`
  (`ecPrinting.ml:4265`).
- The version string becomes `domino-json/2`.
- Update `easycrypt/doc/json-output.md`: the new `proof` shape, where `pp` occurs, the binder
  kinds, and a short change note from version 1.

### Domino

- `FORMAT_VERSION = "domino-json/2"`. An EasyCrypt binary that answers with version 1 is refused
  with the existing error, which names the expected version and `DOMINO_EASYCRYPT`.
- `json::Proof` becomes `{ front: Option<Goal>, kinds: Vec<GoalKind> }`. `Form::pp` keeps
  `#[serde(default)]`, so a subnode with no `pp` parses.
- `Session` gives `front()`, `count()` and `kind(i)` in place of `goals()`. Change every caller:
  the driver's `front()` and `count()`, the shape checks at `driver.rs:1288`, `1350`, `1648` and
  `1733`, and `goals_left` (`live/mod.rs:757`). Nothing outside `Session` sees a list of goals.
- **The transcript.** In capped mode, cap `proof.front` as today's first goal is capped, and keep
  `kinds`. In full mode, write the answer verbatim (it is now small). Remove `GOALS_PER_STEP` and
  `goals_dropped`: the answer has no other goals to drop. The page reads the goal from
  `proof.front`. The page's footer text (`page.rs:319`) changes to match.
- Update the fake EasyCrypt scripts and every test fixture that contains `domino-json/1`.
- **Leave alone:** the fallback sequence, the order of tactics, translation, story 53's fix (it
  does not depend on the binder kind).

### Measurement

Replay the sentences of a full tactics run of H4 ~ H5 through `easycrypt cli -json` (version 2),
and compile the final `Eq_H4_H5.ec` in batch mode. Compare the two times, and the size of the
largest answer, against the baseline: batch 515 s, JSON about 4,366 s, largest answer 28 MB.

### Rejected alternatives

- **The first K goals in full.** Rejected: Domino reads only the front goal in full. Any K > 1
  pays for goals that nothing reads.
- **The count, and a command to fetch any goal on demand.** Rejected: the shape checks need the
  kinds of the second and third goal at most steps, so every such check costs one more round trip.
  It also adds a command to the protocol.
- **The front goal and the count, with no kinds.** Rejected: the `if.` and two-sided shape checks
  need to know which of the other goals are program judgements.
- **Keep all goals and only cut `pp`.** Rejected: it fixes the O(size × depth) part, but every
  answer still carries 16 full goals at a leaf.
- **A pragma that asks for all goals again.** Rejected: nothing reads them. Add it if a later
  story needs it.
- **Remove `--ec-transcript full`.** Rejected: the user keeps the verbatim answer for debugging.
  With version 2 that answer is small.

## 4. Acceptance criteria

- [ ] `easycrypt cli -json` answers with `"version": "domino-json/2"`, and `proof` has `front`
      and `kinds` only. `json-output.md` describes this.
- [ ] No formula or expression subnode in an answer has `pp`. Statements, conditions, lvalues,
      the conclusion root and the hypothesis roots have it.
- [ ] A value binder has `"kind": "var"`.
- [ ] Domino refuses a `domino-json/1` binary with an error that names both versions. A session
      test covers this.
- [ ] `Session` has no `goals()`. The driver's shape checks use `kind(i)`. A unit test covers an
      `if.` shape check with a formula front goal and two program goals behind it.
- [ ] The capped transcript record of an answer holds the capped front goal and `kinds`. The
      full transcript record is the answer verbatim. The page shows the front goal and the number
      of open goals.
- [ ] Every Full4WHS equivalence that a tactics run proved before this story is still proved,
      with the same number of admits or fewer.
- [ ] The implementation report gives the measurement: batch time, JSON replay time, largest
      answer size, before and after. The target is a JSON replay at most 2 × the batch time. If
      the target is not met, the report says where the rest of the time goes.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
- [ ] The EasyCrypt fork builds (`dune build`) and its own tests pass.

## 5. How to verify

```bash
cd easycrypt && dune build && cd ..
export DOMINO_EASYCRYPT=<the easycrypt binary that dune built>
printf 'require import AllCore.\nlemma t (x:int): forall (y:int), x = x /\\ y = y.\nproof.\nmove => y.\nsplit.\n' \
  | $DOMINO_EASYCRYPT cli -json | tail -1 | jq '.version, .proof.kinds, (.proof.front.concl | has("pp"))'
# "domino-json/2", ["formula","formula"], true

cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --tactics
ls -l <out>/*/ec-transcript.jsonl      # much smaller than before
```
