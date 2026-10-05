# Story 51 — Implementation report

A capped transcript record now keeps the first goal as two parts: its conclusion and its
hypotheses. The page shows the conclusion first and folds the hypotheses. The sentences sent and
the proof files written stay the same.

## What changed

- **`src/easycrypt/transcript.rs`.**
  - `GOAL_TEXT_CAP` (2 000) is replaced by `GOAL_CONCL_CAP` = 4 000, `GOAL_CONCL_HEAD` = 2 400
    (60 % of it) and `GOAL_HYPS_CAP` = 1 000.
  - New `GoalParts { concl, concl_cut, hyps, hyps_cut }` (serde). `GoalParts::of_text` splits a
    goal's `text` at the first line made only of `-` (10 or more). The text above is the
    hypotheses, the text below is the conclusion. A text without the rule is all conclusion.
    An over-long conclusion keeps its first 2 400 and last 1 600 characters, and `concl_cut`
    counts the middle. Over-long hypotheses are cut at the end, and `hyps_cut` counts the cut.
    `concl_head_tail` gives the two sides of the cut to the page.
  - A capped goal is written as `{"id", "concl", "concl_cut", "hyps", "hyps_cut"}`. `text` and
    `text_dropped` are no longer written in capped mode. `goals_dropped` is unchanged.
  - The module doc gives the new bound (~5 kB of goal text per record) and the story-41 figure.
- **`src/easycrypt/tactics/live/mod.rs`.** `GoalTexts.goals` is now `Vec<GoalView>`, with
  `GoalView::Parts(GoalParts)` and `GoalView::Older { text, cut }`. The separate `cut` vector is
  removed. The reader's `GoalT` is an untagged enum with three shapes: new capped (`GoalParts`),
  older capped (`text` + `text_dropped`), and full (`text`; it goes through
  `GoalParts::of_text`, the same function the capped writer uses).
- **`src/easycrypt/tactics/live/page.rs`.** New `goal_html`. It writes the conclusion in a
  `<pre>`. If the middle was cut, a marker line is at the cut:
  `… 3 412 characters cut here: the full goal is in ec-transcript.jsonl, transcript record 57,
  with --ec-transcript full …`. Then it writes `<details class="hyps"><summary>hypotheses (N
  lines[, cut])</summary>`, collapsed. An older record shows its `text` under the note
  "older record: context shown first", with the old "... N more characters" note. New helper
  `grouped` writes `3 412`. The footer gives the new caps.
- **`CONTEXT.md`**, *EasyCrypt transcript*: "capped to its first goal, whose conclusion and
  hypotheses are each cut at a fixed length".

## Design decisions

- **The conclusion comes from `text`, not `concl.pp`.** On the real pRHL answer
  `testdata/easycrypt/story25/hello_world_useful_oracle_after_inline.json`, `concl.pp` is
  `equiv[ ec_result <- …; if (…) {...} ~ … : pre ==> post]`: EasyCrypt elides the program
  blocks as `{...}`. The text below the rule has both programs side by side, `pre` and `post`.
  Thus `text` is the source.
- **The cut position is a constant, not a stored field.** The page finds the cut at character
  `GOAL_CONCL_HEAD` of a cut conclusion. This keeps the record shape that the story gives. The
  constant is in `transcript.rs`, beside the other caps, which are already a contract between the
  writer and the page.
- **Full and capped records go through the same function.** The reader applies
  `GoalParts::of_text` to a full record's `text`, and the writer applies it before it writes. Thus
  the two modes render the same HTML (story 41).
- **The marker line is in the conclusion's `<pre>`**, as a `<span class="note">`, so the head and
  the tail stay in one block in the reading order.
- No hypotheses `<details>` when the goal has no hypotheses.

## Rejected shapes

- `concl.pp` as the conclusion: it elides the programs (see above).
- `"concl": [head, tail]` or a `concl_head` field in the record. Both put the cut position in the
  record. The story's record shape and a shared constant do the same with fewer fields.
- Splitting the hypotheses from the structured `hyps` array (`name`, `type.pp`, …). That
  re-implements `cli`'s printer, and the full-mode reader would also have to parse the
  structured goal. `text` already holds the printed lines.
- A version field on the record to tell old from new. The untagged enum tells the three shapes
  apart from their fields, and older records stay readable without a migration.

## Tests

- `cargo test`: 616 passed, 0 failed, 5 ignored (baseline 610; six new tests).
- `cargo clippy --all-targets`: no warnings.
- `transcript.rs`, new: `a_goal_splits_at_the_rule_into_hypotheses_and_conclusion`,
  `a_goal_without_hypotheses_is_all_conclusion`,
  `a_long_conclusion_keeps_its_head_and_tail_and_counts_the_middle`,
  `long_hypotheses_are_cut_at_the_end_and_counted`,
  `a_real_program_goal_keeps_the_judgment_with_its_post_condition` (the story-25 real pRHL answer:
  the conclusion starts with `&1 (left ) : {`, holds `pre =` and `post =`, and the hypotheses are
  `Type variables: <none>` and `&m: {}`). Changed: the cap test, the short-goal test and the
  real-answer test now check `concl` / `hyps`.
- `live/tests.rs`, new: `the_conclusion_comes_first_and_the_hypotheses_are_folded` (judgment
  before the `<details>`, post-condition kept, cut marker, "lines, cut", the last hypothesis
  dropped), `a_capped_record_written_before_story_51_still_renders` (replaces a record in place
  with an older capped record of the same length, so the offset stays valid).
  `the_page_is_the_same_from_a_capped_and_a_full_transcript` now uses program goals with
  hypotheses and a cut conclusion, and still asserts identical HTML.
- `session.rs`: the sink test checks the new fields
  (`the_sink_caps_a_large_answer_to_its_first_goal_cut_to_the_caps`).
- Real older transcript: all 86 goals in the kem-dem `PKENC` transcript in `_build` have the
  `text` + `text_dropped` shape that `GoalT::Older` reads.

## Deviations

- `cvc5-lib` does not build on this machine (no `cmake`), so §5's `domino easycrypt prove` run on
  kem-dem was not done. The page was not opened in a browser on a real run, and record sizes were
  not measured on a real transcript. The acceptance criteria are covered by Rust tests on the
  real story-25 pRHL answer and on synthetic goals.
- No headless-Chrome check: no `_build` transcript has the new record shape, and the HTML is
  checked by string tests.

## Open items

- Run §5 on a machine with `cvc5-lib`: open the goal on the page, check the record sizes against
  ~5 kB, and compare the capped and full pages' goal blocks.
- The marker says "transcript record N", the page's existing name for a record, not "record N".
