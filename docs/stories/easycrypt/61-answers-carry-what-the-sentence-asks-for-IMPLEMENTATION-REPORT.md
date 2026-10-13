# Story 61 — Implementation report: answers carry what the sentence asks for (`domino-json/3`)

OCaml (the fork in `easycrypt/`) and Rust. The sentences of a run and the proof files do not
change, except for one more sentence, `pragma Goals:printall.`, where Domino must read a goal
that an answer did not carry (see "Deviations").

## Fork (`easycrypt/`, branch `amir/domino-easycrypt-integration`)

- **`ecTerminal.ml`**: each input line is a request `{"sentence": …, "want": …}` (`Json.request`,
  parsed with Yojson). `want` is `status`, `head` or `full`, default `full`. The sentence is
  parsed alone (`EcIo.from_string`), so error locations stay offsets in the sentence. A line
  that is not a request (not JSON, no `sentence` string, an empty sentence, an unknown `want`)
  gives an error answer `invalid request: …`; the state does not change. End of input is still
  an `exit.`. Version `domino-json/3`.
- **`Json.proof ~want ~failed`**: `front` is `null` for `status` and for every failed
  (`error`/`interrupted`) sentence; `kinds` is always there.
- **`ecPrinting.ml`, `PPJson`**:
  - Type table: `jty` returns an index; each distinct type (keyed by its hash-cons tag) is one
    entry of `"types"`, with its `pp` and its subtypes as indices. No type is inline.
  - `head`: formula nodes deeper than 4 (the root is depth 1) are stubs
    `{"kind", "stub": true}`, plus `"op"` for an application of an operator. Hypotheses keep
    name, kind and type; the root `pp`s and `text` stay (the capped transcript and the admit
    comment read them).
- **`doc/json-output.md`**: the request, the table of wants, the type table, "Changes from
  `domino-json/2`".
- **`tests/json/check.py`**: speaks the new protocol. The suite was stale (it still expected
  `domino-json/1` and `pp` on subnodes); fixed. New class `Wants`: `status`, `head` (stubs
  exactly past depth 4), `full` (type table, no inline type), a failure gives `front: null` for
  each want, default `full`, bad requests. 21 tests, all pass on the built binary.

## Domino

- **`json.rs`**: `FORMAT_VERSION = "domino-json/3"`. `Goal::types` and `Goal::ty(index)`;
  `Hyp::ty` and the new `Form::ty` are indices; `Form::stub`. No reader in `goals.rs` or
  `align.rs` reads a type today, so no lookup was needed there.
- **`session.rs`**:
  - `Want` (`Status < Head < Full`). `Session::send(sentence, want)` writes the request line.
  - The front goal is the session's: `fronts`, one goal per EasyCrypt state (the newest 64),
    with the depth it was read at. A failed sentence changes nothing; an accepted one drops the
    states above it; an `undo` (sent with `status`) finds the goal of its state there.
  - When an accepted sentence leaves goals open and no goal is known for the new state, `send`
    reads it at once (`pragma Goals:printall.` at `full`, an exchange in the transcript).
    `ensure_front(want)` reads it again in full when it is known only at `head`.
  - The startup probe is the bare sentence, not a request: a `domino-json/2` fork runs it and
    answers with its version, so it is refused at once with the error that names both versions
    and `DOMINO_EASYCRYPT` (no wait on a request it cannot parse).
  - `SessionEvent::Answered::front_in_record`; answers in `transcript()` no longer carry a
    front goal, and keep their kinds.
- **`driver.rs`**: every send states its want:
  - `status`: `try_close` (quick close, fallbacks, part fallbacks, closings), the closing tail
    of `try_with_premise`, `admit.`, the exit path (`decide_if`), the one-step `rcondt/rcondf`
    with its side goal, the `hints` at the end of a key case. `undo` (in the session).
  - `head`: the opening loop (`move => … /=.`, `rewrite /op /=.`, `do split.`), `auto => &1 &2
    hpre.`, the premise unfolding, `reduce_to_ambient`, the `case` sentence of the key split.
  - `full`: `proc; inline.`, `sp`, `if`, `if{i}`, the plain `rcond`, `seq` attempts, the
    blind fallback's trials, replayed scripts.
  - The key scan (story 66) and the end of a leaf call `full_front` (read in full if the goal is
    known only at `head`).
- **`check.rs`, `tactics/mod.rs`**: opening sentences `full`; base case and `admit.` `status`.
- **Live page**: `Step::goal_record` is the record that holds the goal Domino has after the
  step (its own, or for a failed / `status` / `undo` answer the last one read at that depth).
  The page embeds that goal; a `status` answer has no goal to cap.
- **Test data**: the two `domino-json/2` fixtures were rewritten to `/3` (type table): the
  hello-world goal after `proc; inline.` went from 54,218 to 28,394 bytes (−48 %).

## Tests

- New: `each_request_is_one_json_line_with_its_want`,
  `the_front_goal_survives_a_failure_and_comes_back_with_an_undo` (driver/session: front after a
  failure and after `undo`, the read after a `status` success, `ensure_front`),
  `an_older_binary_is_refused_naming_both_versions` (`/1` and `/2`),
  `fallbacks_and_admits_ask_for_status_and_the_opening_for_the_head` (the requests a leaf
  sends), `a_failed_step_shows_the_goal_from_before` (live page). The real-EasyCrypt test
  `send_error_undo_and_interrupt` now checks the goal after an error and after an undo with no
  re-read.
- The fake EasyCrypts read the request line (the sentence is taken out with `sed`); the leaf
  tests expect the one probe the key scan sends after `do split.` read the goal at `head`.
- `cargo test --lib easycrypt` with `DOMINO_EASYCRYPT` = the fork built here
  (`easycrypt/_build/default/src/ec.exe`): 500 passed, 0 failed (includes hello-world and the
  four-oracles test project). Full `cargo test --lib` (no `DOMINO_EASYCRYPT`): 697 passed,
  0 failed, 5 ignored. `cargo clippy --workspace --all-targets`: no warnings.
  `cargo build --release --workspace`: succeeds.
- Complexity: the sdlc cognitive-complexity gate does not score this Rust change (it answered
  "NotApplicable"), so it is **unmeasured** by the tool. The new functions are small
  (`learn_front`, `Live::goal_record`, `ensure_front`, `Json.request`: a few branches each).
- Fork: `opam exec --switch=easycrypt -- dune build` succeeds;
  `python3 tests/json/check.py --bin _build/default/src/ec.exe`: 21 OK.
- `--features cvc5-lib`: not built (no cmake on this machine).

## Measurements

| What | Before | After |
|---|---|---|
| Smoke goal (one lemma, 4 types), `full` | — | 3,590 B |
| Same goal, `head` | — | 1,945 B |
| A failed sentence (any want) | front goal in full | 237 B |
| Hello-world goal after `proc; inline.` (fixture) | 54,218 B | 28,394 B |

**Not measured**: the bytes and "rest of round trip" of H2_1 ~ H3_0 and H6_1_1 ~ H7_0, and the
2.15 MB leaf answer of `Eq_H4_H5.ec`. The owner asked for no EasyCrypt proof runs on Full4WHS in
this session. Run story 61 §5 with the fork at the new pin to get them.

## Deviations and open points

- **A `status` success is followed by a read of the goal.** The driver reads `front()` from
  `&self` in many places (predicates of `attempt` too), so the session reads the goal at once
  when an accepted `status` sentence leaves goals open and none is known, rather than lazily. So
  `status` saves the bytes of failed sentences (24 % of the measured bytes), of closings that
  leave no goal, and of `undo`; a successful closing still costs one full read (and one more
  round trip). A lazy read would need `&mut` reads across the driver.
- The key scan sends one extra probe when the goal was read at `head` (the expected leaf
  transcripts in the tests now show it).
- `head` answers keep `text` and the root `pp`s: the capped transcript, the live page and the
  admit comment read them. The story's table does not list them; they are small next to the
  tree.
- Stubs carry `"stub": true` in addition to `kind`/`op`, so a reader can tell a cut node.
- The transcript records do not say which want a sentence asked for (only its answer shows it).
