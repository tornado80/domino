# Story 52 — Implementation report: quick close and fallbacks

## What changed

- **Vocabulary.** "Rung 0" is now the **quick close** and "the ladder" is now the **fallback
  sequence**, with **fallbacks** numbered from one (`CONTEXT.md`). This report records the rename
  once. Older stories and reports keep their words.
- **Closing attempts with an outcome** (`live/mod.rs`). `NodeRec.rungs: Vec<String>` is now
  `NodeRec.attempts: Vec<AttemptRec>`. An `AttemptRec` holds what the attempt is
  (`Closing::QuickClose` or `Closing::Fallback { k, of }`), the sentences as shown, the timeout in
  force, the first step it sent, and its outcome (`Closed`, `Failed`, `TimedOut`, or `None` while
  in flight). `Live::rung` is replaced by `LiveHandle::attempt(closing, shown, timeout)` and
  `LiveHandle::attempt_ended(closed)`. A failed attempt is `TimedOut` if one of its steps was
  interrupted by the timeout, else `Failed`.
- **Driver** (`driver.rs`). `note_rung` is replaced by `closing_attempt(closing, shown, f)`, which
  records the start, runs `f`, and records the end. `try_quick_close` and `quick_close_program`
  (the program-goal quick close under its short timeout, off with `--no-quick-close`) replace the
  three copies of `with_timeout(rung0, try_close(["auto => /#."]))`. All four quick closes are now
  recorded: the node's, the router's both-aborted one, `prove_blind`'s, and the side goals'.
  `fn ladder` is `fn fallbacks`, and its four members are `fallback 1/4: smt()`,
  `2/4: smt() (premise unfolded)`, `3/4: smt(<hints>)`, `4/4: smt(<hints>) (premise unfolded)`.
  `FALLBACKS = 4` is the sequence length.
- **Node chip** (`page.rs`, `attempt_chip`): `trying <attempt>: <sentence>` on a node being worked
  on with an attempt in flight; `closed by <attempt>: <sentence>` on a closed node whose last
  attempt closed; no chip otherwise (admitted, kept, open, or closed by structural tactics).
- **Attempts list** (`attempts_list`): a collapsed `<details>` "closing attempts (k)" before the
  steps, one line per attempt: name, sentence, and `✓ closed`, `✗ failed`,
  `✗ timed out (2 s)` or `… in flight`. The timeout is the configured one, not a measured time, so
  the page stays free of timings outside `<script id="timings">`.
- **Names.** `TacticsOptions.rung0` → `quick_close`, `Timeouts.rung0` → `quick_close`,
  `RUNG0_TIMEOUT` → `QUICK_CLOSE_TIMEOUT`, `Resume.skip_rung0` → `skip_quick_close`. Comments in
  `tactics/` use the new words.
- **CLI.** `--no-rung0` is `--no-quick-close`, now visible in `--help` with the text "Skip the
  quick close (`auto => /#.` on every program goal) …". `--no-rung0` stays as a hidden clap
  alias. The integration tests use the new spelling.

## Design decisions

- **The chip uses the node's last attempt.** A node's attempt list also holds the attempts on its
  side goals. If the last attempt closed and the node is closed without an admit, that attempt
  closed the last open goal, so the chip names it. Thus a node whose last goal was a side goal
  closed by a fallback says "closed by fallback 1/4: smt()". A node whose quick close timed out and
  whose structural tactics and children closed it has a failed last attempt, so it has no chip.
- **The outcome comes from the steps, not from the driver.** The driver knows only "closed or
  not". The live model already has each step's status, so it finds a timeout there. This keeps
  `closing_attempt` to one boolean.
- **Start and end are two calls**, so the page shows an attempt in flight during a long `smt()`.

## Rejected shapes

- **Keep `note_rung(name)` and put the outcome in the string** (`"0: auto => /# (timed out)"`).
  Rejected: the chip must tell in-flight from closed, and the list needs the kind and the outcome
  apart. Strings would have to be parsed back.
- **A `closes_node: bool` on each attempt** to tell node-goal attempts from side-goal ones.
  Rejected: a flag for a rule ("the last attempt closed the last goal") that the order already
  gives.
- **Measured time in the timed-out line.** Rejected: it would break the "two runs write the same
  page after `strip_timings`" guarantee.

## Tests

- Baseline: `cargo test` 616 passed, 5 ignored (confirmed before editing).
- After: `cargo test` 620 passed, 0 failed, 5 ignored (one old test removed, five new).
  `cargo test -p domino`: all green, with the new CLI test. `cargo clippy --all-targets`: no
  warnings.
- `live/tests.rs`, new (replace `rungs_are_shown_on_the_goal_and_the_last_one_wins`):
  `a_node_closed_by_its_quick_close_says_so`,
  `a_timed_out_quick_close_is_listed_but_names_no_chip`,
  `every_attempt_is_listed_in_order_and_the_last_closing_one_is_on_the_chip`,
  `the_attempt_in_flight_is_on_the_chip`, `an_admitted_node_has_no_chip`.
- `crates/domino/src/cli.rs`, new:
  `no_quick_close_and_its_hidden_alias_no_rung0_both_skip_the_quick_close`.
- `grep -rni "rung\|ladder" src crates` finds only the alias and its test.

## Deviations

- `cvc5-lib` does not build on this machine (no `cmake`). `domino easycrypt prove` stops at once
  without it, so §5 (proof files byte-identical to the previous commit, the page in a live run,
  kem-dem `PKENC`) was not run. I built the previous commit in a separate worktree, but neither
  binary can prove. The proof files stay the same by construction: `closing_attempt` only notifies
  the live page, and the sentences, their order, the timeouts and the guard order
  (`TerminalPair`, resumed ancestor, flag) are unchanged. The tactics tests in
  `tactics/tests.rs` that check scripts still pass.
- No headless-Chrome check: no `_build` page has the new markup. The HTML is checked by string
  tests.

## Open items

- Run §5 on a machine with `cvc5-lib`: compare the three runs' proof files with the previous
  commit, and open a closed node, an admitted node and the node in flight on the page.
