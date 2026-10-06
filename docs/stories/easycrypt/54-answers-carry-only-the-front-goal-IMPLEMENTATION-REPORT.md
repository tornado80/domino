# Story 54 — Implementation report: EasyCrypt's answers carry only the front goal

**EasyCrypt commit:** `cc719556` on `amir/domino-easycrypt-integration` (clone at `easycrypt/`).
The Domino commit moves the submodule pointer to it (from `b2511afa`; the pointer also takes in
`7212a43e` and `33591d43` of story `easycrypt-never-swallows-an-interrupt`, which were not
recorded before).

## What changed (EasyCrypt clone)

- **`src/ecTerminal.ml`.** `Json.version` is `domino-json/2`. `Json.proof` writes
  `{"front": <goal or null>, "kinds": [...]}`. Only the first open goal goes through
  `goal_to_json`. The kind of a goal is `"program"` for `FequivS` and `"formula"` for every other
  conclusion.
- **`src/ecPrinting.ml` (`PPJson`).** `obj` writes no `pp`. `objp` writes one, and is used for
  types, instructions, lvalues and program variables. `rooted` adds `pp` after the `kind` of a
  node. `jcond` (the condition of `if` and `while`) and `jroot` (the conclusion, a `hyp`'s
  formula, a `let` hypothesis's body) use it. Formula and expression subnodes have no `pp`. A
  value binder (`GTty`) has the kind `"var"`.
- **`doc/json-output.md`.** The new `proof` shape, the list of nodes with `pp`, the binder
  kinds, a new example, and a section "Changes from `domino-json/1`".

Types keep `pp` on every node. The story removes it from formula and expression subnodes only,
and a type tree is small.

## What changed (Domino)

- **`json.rs`.** `FORMAT_VERSION = "domino-json/2"`. `Proof { front: Option<Box<Goal>>, kinds:
  Vec<GoalKind> }`, with `enum GoalKind { Program, Formula }`. The goal is boxed, because an
  inline `Goal` makes `session::Wait` too large for clippy.
- **`session.rs`.** `goals()` is gone. `front()`, `count()` and `kind(i)` replace it. A binary
  that answers `domino-json/1` gets the existing `NotJsonCapable` error, which names both
  versions and `DOMINO_EASYCRYPT`.
- **`tactics/goals.rs`.** New `is_if_split(front, kind)`: an ambient front goal, and program
  goals at positions 1 and 2. The two `if.` shape checks of the driver use it (through
  `Prover::is_if_split`). `two_programs_in_front` reads `kind(0)` and `kind(1)`. The blind `if.`
  check reads the front goal.
- **`transcript.rs`.** `GOALS_PER_STEP` and `goals_dropped` are removed. A capped record holds
  `{"front": {"id", "concl", "concl_cut", "hyps", "hyps_cut"} or null, "kinds": <verbatim>}`. A
  full record is the answer verbatim.
- **Live page.** `GoalTexts` holds the front goal's `GoalParts` and the number of open goals.
  The page shows "goal 1 of N", or "no goal left". The footer says that only the front goal is
  embedded. The `GoalView::Older` path (capped records from before story 51) is removed: a
  version 2 run cannot write such a record.
- **`--ec-transcript` help** (`crates/domino/src/cli.rs`) describes the new content.
- **Fixtures.** The two JSON fixtures (`story25`, `story31`) are converted to the version 2
  shape with `jq`: version, `proof` as `front` + `kinds`, and the binder kind. Their `pp` fields
  are kept. Every fake EasyCrypt script and every inline answer now says `domino-json/2`.

## Rejected shapes

- **Give `Session` a `kinds()` slice.** Rejected: the story asks for `kind(i)`, and a slice lets
  callers read the goal list again by position.
- **A boolean "root" parameter on `jform`/`jexpr`.** Rejected: a flag parameter. `rooted` adds
  `pp` at the few call sites that need it.
- **Keep reading `goals`/`goals_dropped` records on the page.** Rejected: no second code path
  for the old format. A transcript written by a version 1 run shows "the goal text could not be
  read" on a page written by a version 2 run.
- The rejected alternatives of the story and of ADR 0009 stay rejected.

## Tests

- Baseline: `cargo test --workspace` 625 passed, 0 failed, 5 ignored.
- New or changed tests:
  - `session::tests::a_domino_json_1_binary_is_refused_naming_both_versions`.
  - `goals::tests::an_if_split_is_a_formula_in_front_and_two_programs_behind_it` (formula front
    goal and two program goals behind it; also a missing arm, a formula arm, no front goal, and a
    program front goal).
  - `session::tests::goals_lost_to_an_interrupt_are_read_again` now checks `count()`,
    `front()` and `kind(i)`.
  - `transcript::tests`: the capped record holds the capped front goal and `kinds`; an answer
    with `front: null` is kept whole.
  - Live page tests: "goal 1 of N" in place of "+N goals not kept". The test of pre-story-51
    records is removed with that code path.
- After: `cargo test --workspace` 625 passed, 0 failed, 5 ignored. `cargo test --lib easycrypt`
  with `DOMINO_EASYCRYPT` set to the new `ec.native`: 444 passed (the real-EasyCrypt session
  tests run). `cargo clippy --workspace --all-targets`, with and without `cvc5-lib`: no
  warnings. `cargo test --workspace --features cvc5-lib`: 723 passed, 0 failed, 6 ignored.
- EasyCrypt: `dune build` clean. Unit tests (`config/tests.config unit`): 108/108 pass. The
  clone's `easycrypt.project` asks for `Z3@4.16` and `CVC5@1.1`; this machine has `Z3@4.13.4`
  and `CVC5@1.3.4`, so the run used a temporary copy of that file with those versions. The file
  is not changed. `make unit` also needs the Python `yaml` module for its report, which is not
  installed, so `scripts/testing/runtest` was run directly.
- The check of §5 gives `"domino-json/2"`, `["formula","formula"]`, `true`.

## Measurement

The user asked for no runs longer than about 10 minutes. A full tactics run of H4 ~ H5 takes
hours, so the measurement uses H0 ~ H1_0 (proofstep 0 of Full4WHS) in its place. The same
`Eq_H0_H1_0.ec` (produced by the version 2 run, 0 admits, 217 sentences) was given whole to
`ec.native cli -json` on standard input, once with the clone at `33591d43` (version 1) and once
at `cc719556` (version 2).

|                         | version 1 | version 2 |
|-------------------------|-----------|-----------|
| batch (`compile`)       | 36.1 s    | 36.1 s    |
| JSON replay             | 155.9 s   | 47.7 s    |
| JSON replay / batch     | 4.3 ×     | 1.32 ×    |
| largest answer          | 7.4 MB    | 0.67 MB   |
| all answers             | 444 MB    | 71 MB     |

The target (JSON replay at most 2 × batch) is met on H0 ~ H1_0. The remaining 11.6 s are the
printing of the front goal: at most steps it is a pair of programs of several hundred
instructions, each with its `pp` and the `pp` of its type nodes, and the goal's `text`.

The H4 ~ H5 numbers of the story (batch 515 s, JSON about 4,366 s, 28 MB) were not measured
again. See "Open items".

## Runs on `example-projects/4WHS` (theorem Full4WHS)

- **H0 ~ H1_0** (proofstep 0, release build with `cvc5-lib`): 12 oracles, 100 goals closed,
  0 admits, 218 s. Same admit count as before (story 53: 0). Capped transcript: 1.0 MB for
  258 records.

## Open items

- The acceptance criterion "every Full4WHS equivalence that a tactics run proved before is still
  proved" is checked on H0 ~ H1_0 only. The other equivalences take more than 10 minutes each.
  H1_1 ~ H2_0 (0 admits before) is the next one to run.
- The measurement on H4 ~ H5 (the story's baseline) is not done, for the same reason. The H0 ~
  H1_0 numbers above show the same effect at a smaller scale.
