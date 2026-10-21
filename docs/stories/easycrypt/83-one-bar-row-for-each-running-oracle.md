# Story 83 — One bar row for each running oracle

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 82.
**Blocks:** nothing (84 uses its rows).
**ADR:** 0020 (points 3, 5).
**Decisions:** grilling of 2026-10-21, Questions 2, 4 (the bar addition), 6 and 7.

A **progress** story, Rust only. Test-first.

---

## 1. Why this story exists

Story 82 brings the events back, but in bar mode only one oracle has a bar. The user wants, for
each running oracle, what stories 39 and 40 showed: the debugger's lockstep progress, then the
node, the tactic, and how long EasyCrypt has worked on it.

## 2. Work to do

### 2.1 The layout

```
Eq_H4_H5   tactics ███░░░ 3/7  done 2, running 2
  PKENC    lockstep  node 40 sync-branch  pairs 23 ✓21 ?2       41s
  DEC      N7/23  smt(dec_enc).                                  12s
SideInv_C  tactics █░░░ 1/4  done 0, running 1
  ENC      N3/9   proc; inline.                                   2s
```

- **Header row** for each running job (`JobProgress`): a bar of done oracles, and
  `done <d>, running <r>` from the rows it made and dropped (no status method, ADR 0020 point 2).
  It leaves when the job ends.
- **Oracle row** (`JobProgress::oracle`), under its job's header:
  - during lockstep execution: `lockstep  node <i> <kind>  pairs <n> <tally>` and the elapsed time.
    The row's `lockstep_observer()` returns a `DebugObserver` that writes to **this row**
    (`JointNode`, `JointPairChecked`, the tally of `BarObserver`). It does not register a screen.
  - while proving: `proving_message(oracle, node, total, sentence)` and `{elapsed}`, reset on each
    `NodeStarted` and `SentenceSent`, as `BarExportObserver` does today. `12s` means EasyCrypt has
    worked 12 s on that sentence.
- When an oracle ends, its row leaves the live area and one line prints above it: the
  `lockstep_summary_line` (as today) and the oracle's end (`done, 2 admits`, `interrupted at N7`).
  `⚠ GOAL FAILS at …` and stuck points also print above, as in `BarObserver`.
- No flag limits the rows: `--jobs` already does.

### 2.2 The one screen

`BarProgressBoard` keeps one `MultiProgress`. When it is made, it registers it in `ACTIVE_BARS`
(`debug/progress.rs`); when it is dropped, it clears it. `eprintln_above_bars` and the Ctrl-C handler
(`main.rs:259`) do not change. A `debug_assert!` in the registration checks that no other screen is
active. `domino debug` keeps its `BarObserver`, which registers as before.

Remove the temporary adapter of story 82 §2.4. `BarExportObserver` stays for the export phases.

### 2.3 Rejected alternatives (ADR 0020)

- The old display for each worker, stacked (up to 3 lines for each oracle).
- One shared line that rotates.
- A `Printer` handle passed to each call site.
- A flag for the most rows on screen.

## 3. Tests first

Enable indicatif's `in_memory` feature for tests only (`[dev-dependencies]`). The tests draw the
board on `InMemoryTerm` and compare the screen with the times taken out (as `strip_timings` does
for pages).

- [ ] Two oracle rows under one header: each shows its node, tactic and timer; the header says
      `done 0, running 2`.
- [ ] An oracle row in lockstep shows `node <i> <kind>` and the pair tally; when it goes to
      proving, the same row shows `N<i>/<n>  <tactic>`.
- [ ] A finished row leaves, and its summary line is above the live rows.
- [ ] `eprintln_above_bars` while rows are live prints above them and tears no row.
- [ ] Making a second screen while the board is active fails the debug assertion.

## 4. Acceptance criteria

- [ ] All tests of §3 green; story 82's event tests still green.
- [ ] By hand: `domino easycrypt prove --jobs 4` on `example-projects` shows one row for each running
      oracle, the chain's rows included, and each row shows the tactic and the wait time.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
