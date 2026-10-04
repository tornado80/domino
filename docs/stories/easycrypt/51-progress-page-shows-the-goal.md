# Story 51 — The progress page shows the goal, not just its context

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 41 (the transcript keeps the first goal), 28 (the live page), 31 (the bounded
transcript).
**Blocks:** nothing.

A **progress-page** story. Translation and proving do not change: the same sentences are sent and
the same proof files are written. What changes is what a capped transcript record keeps of a goal,
and how the page shows it.

---

## 1. Why this story exists

The owner: *"In the progress UI, you only put the context of the first goal instead of the goal
itself."*

`capped_proof` (`src/easycrypt/transcript.rs`) keeps the first goal's `text`, the goal as
EasyCrypt's `cli` prints it, and cuts it at `GOAL_TEXT_CAP` = 2 000 characters **from the start**.
`cli` prints the hypotheses first: type variables, memories, module types, every local and
hypothesis. Only after them come the separator rule and the conclusion, which for a program goal
is the pRHL judgment with both programs, `pre` and `post`. On real oracles the hypotheses alone
pass 2 000 characters, so the page shows context and cuts the goal off. The page then says
"N characters cut", which is true and useless.

## 2. Inherited from earlier stories

- `transcript.rs`: `GOALS_PER_STEP` = 1, `GOAL_TEXT_CAP` = 2 000, `cap_response` /
  `capped_proof`. A capped goal is written as `{"id", "text", "text_dropped"}`. Story 41: "a
  capped record holds exactly what the page shows, so the page renders the same from either mode".
- **Byte offsets:** the page remembers where each record starts and reads goal text back from
  there. Records are bounded as they are written and never rewritten (module doc).
- `src/easycrypt/json.rs`: EasyCrypt's `Goal` has `hyps` (each with `name`, `kind`, and `type` or
  `form`, each with `pp`), `concl` (a `Form` with `pp`) and `text`.
- The page (`src/easycrypt/tactics/live/page.rs`, around line 510) renders `GoalTexts`: one
  `<pre>` per kept goal, then "+N goals not kept" and the cut notes.

## 3. Work to do

### 3.1 What a capped record keeps of a goal

Keep the first goal (`GOALS_PER_STEP` is unchanged) as two separately capped parts:

- **conclusion**: what `cli` prints below the separator rule. Take it from `text`. If `concl.pp`
  turns out to hold the whole judgment (both programs, pre and post) on a real pRHL answer, use it
  instead; investigate and record which in the report. Cap it at `GOAL_CONCL_CAP` (4 000
  characters). An over-long conclusion keeps its **head and its tail** (about 60 % and 40 %), and
  records how many characters were cut from the middle. The tail is the post-condition, which is
  usually what the reader is looking for.
- **hypotheses**: what `cli` prints above the rule, one per line. Capped at `GOAL_HYPS_CAP` (1 000
  characters), cut at the end, with the number cut recorded.

The record becomes, for example, `{"id", "concl", "concl_cut", "hyps", "hyps_cut"}`. `text` is no
longer written in capped mode. The per-record bound grows from about 2 kB to about 5 kB of goal
text; update the module doc and story 41's figure in it. In `CONTEXT.md`'s *EasyCrypt transcript*
entry, "capped to its first goal, cut at a fixed length" becomes "capped to its first goal, whose
conclusion and hypotheses are each cut at a fixed length".

`--ec-transcript full` is unchanged: it writes EasyCrypt's answer verbatim, which already holds
every part.

### 3.2 What the page shows

For each embedded goal:

1. **The conclusion first**, in a `<pre>`. If it was cut in the middle, show a marker line at the
   cut: `… 3 412 characters cut here: the full goal is in ec-transcript.jsonl, record 57, with
   --ec-transcript full …`.
2. **The hypotheses** in a collapsed `<details>`: "hypotheses (N lines)", plus "cut" if cut.

From a full-mode record the page derives the same two parts by the same rules, so the two modes
still render identically, as story 41 requires. From a record written before this story (`text`
only), the page shows `text` as today, under a note "older record: context shown first".

### 3.3 Not in this story

- How many goals are kept (still one).
- Naming on the page ("rung"): story 52.

## 4. Acceptance criteria

- [ ] On a real program goal, the capped record's conclusion starts with the pRHL judgment, not with
      a hypothesis, and contains the post-condition.
- [ ] A conclusion longer than `GOAL_CONCL_CAP` keeps its head and tail with the middle cut counted.
      Hypotheses longer than `GOAL_HYPS_CAP` are cut at the end and counted.
- [ ] The page shows the conclusion first and the hypotheses collapsed, for capped and full records
      alike. Rendering one step from a capped record and from the full record of the same answer
      gives identical HTML (Rust test).
- [ ] A transcript written before this story still renders on the new page.
- [ ] Records are still only appended; byte offsets the page holds stay valid.
- [ ] Unit tests in `transcript.rs` for the split, both caps, the middle cut and an answer without
      hypotheses.

## 5. How to verify

```sh
D=target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt prove --theorem <T> --proofstep 0 --oracle PKENC -f
```

Open `_build/easycrypt/<theorem>/progress/<Eq…>/index.html` (the page story 28 writes). Open the
goal being worked on: the first lines are the judgment, the post-condition is visible, and the
hypotheses are folded. Check the size of a few records in `ec-transcript.jsonl` against the new
bound. Repeat with `--ec-transcript full` and compare the two pages' goal blocks.
