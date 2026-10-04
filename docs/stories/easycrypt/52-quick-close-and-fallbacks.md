# Story 52 — "Rung" becomes quick close and fallbacks, and the page says what closed a node

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 27 (tactic generation), 28 (the live page), 40 (the proving line).
**Blocks:** nothing. 51 may land before or after; both touch `page.rs`.

A **progress-page and naming** story. The same tactics are tried in the same order with the same
timeouts, and the proof files are byte-identical. What changes is what the page says about them, the
spelling of one CLI flag, and internal names.

---

## 1. Why this story exists

The owner: *"I also don't understand rung. What does `rung: 0: auto => /#` mean? The term rung is
not very good. Where was it decided to use this term."*

- **Where it came from.** Story 27 §3.3 ("**Rung 0.** Every program goal first tries
  `auto => /#.`") and §3.5 ("The ladder" for side goals). Story 28 copied the word into the live
  page's node chip (`note_rung`), and the CLI has `--no-rung0`. It was never a glossary term.
- **What the chip means.** `NodeRec.rungs` records each closing attempt *as it starts*, and the
  chip shows the **last** one, closed or not. `rung: 0: auto => /#` therefore means "the last
  closing attempt on this node was the opening `auto => /#`", whether or not it worked. On an open
  node whose quick close failed, the chip names a tactic that did not help.

The grilling session settled the vocabulary, and `CONTEXT.md` now has it:

- **quick close**: the opening `auto => /#` every program goal gets;
- **fallback sequence**: the ordered closing tactics for side goals and leaf parts. Its members
  are **fallbacks**, numbered from one.

"Rung" and "ladder" are under _Avoid_.

## 2. Inherited from earlier stories

- `src/easycrypt/tactics/driver.rs`:
  - `note_rung` (line ≈874).
  - The quick close at line ≈1103 (`note_rung("0: auto => /#")`), guarded by `self.rung0` and
    skipped on resumed ancestors (`Resume.skip_rung0`).
  - Two more quick closes (≈1635, ≈1663) that note nothing.
  - Side goals at ≈890 try `auto => /#.` and then `ladder()`, again noting nothing for the first.
  - `ladder()` (≈857) notes `ladder: smt()`, `ladder: premise unfolded, smt`, and the same two
    with hints.
- `src/easycrypt/tactics/live/mod.rs`: `NodeRec.rungs: Vec<String>`, and `Live::rung(name)` pushes
  a name unless it repeats the last.
- `src/easycrypt/tactics/live/page.rs:439`: `<span class="chip">rung: …</span>`.
- `src/easycrypt/tactics/mod.rs`: `TacticsOptions.rung0`, `Timeouts.rung0`
  (`RUNG0_TIMEOUT.min(ec_timeout)`). These are internal, **not** a configuration key.
- `crates/domino/src/cli.rs:185`: `--no-rung0` on `easycrypt prove`, used by
  `crates/domino/tests/easycrypt_tactics_writes.rs`.

## 3. Work to do

### 3.1 Record attempts with their outcome

Replace `note_rung(name)` with a record of each **closing attempt**:

- what it is: quick close, or fallback *k* of *N*, where *N* is the length of the fallback sequence
  in force (4 today: `smt()`, premise unfolded + `smt()`, `smt(hints)`, premise unfolded +
  `smt(hints)`);
- the sentence or sentences sent;
- how it ended: **closed**, **failed** (EasyCrypt rejected it or goals remained), or **timed out**.

Every closing attempt is recorded, including the three that note nothing today (the quick closes at
≈1635 and ≈1663, and the side goals' `auto => /#`). `NodeRec.rungs` becomes `NodeRec.attempts`.

### 3.2 The node chip

| Node state | Chip |
|---|---|
| being worked on, attempt in flight | `trying quick close: auto => /#` / `trying fallback 2/4: smt() (premise unfolded)` |
| closed, and the closing attempt is recorded | `closed by quick close: auto => /#` / `closed by fallback 1/4: smt()` |
| closed by its structural tactics and children, no attempt closed it | no chip (the state already says "closed") |
| admitted | no chip (the admit row already gives the reason) |
| open, not being worked on | no chip |

### 3.3 The attempts list

Inside each node, before its steps, add a collapsed `<details>`: "closing attempts (k)", one line
per attempt in order. For example: `quick close  auto => /#  ✗ timed out (2 s)` and
`fallback 1/4  smt()  ✓ closed`. The steps list is unchanged.

### 3.4 Names everywhere else

- **CLI:** `--no-rung0` becomes `--no-quick-close`, help text "Skip the quick close (`auto => /#.`
  on every program goal) …". `--no-rung0` stays as a hidden alias. Tests use the new spelling, plus
  one test that the alias still works.
- **Identifiers:**
  - `TacticsOptions.rung0` → `quick_close`, `Timeouts.rung0` → `quick_close`,
    `RUNG0_TIMEOUT` → `QUICK_CLOSE_TIMEOUT`;
  - `Resume.skip_rung0` → `skip_quick_close`;
  - `note_rung` → `note_attempt`, `Live::rung` → `Live::attempt`;
  - `fn ladder` → `fn fallbacks`.
- **Comments and doc comments** in `tactics/` use "quick close" and "fallback". Older stories and
  reports keep their words; this story's report records the rename once.

### 3.5 Not in this story

- Changing which tactics are tried, their order or their timeouts.
- The goal text on the page: story 51.

## 4. Acceptance criteria

- [ ] No user-visible "rung" or "ladder" remains: page, CLI help and stderr. `grep -rni
      "rung\|ladder" src crates` finds only the hidden alias and its test.
- [ ] The chip follows §3.2 on a run with at least one quick close that closes a node, one that times
      out and is followed by structural tactics, and one side goal closed by a fallback.
- [ ] The attempts list shows every attempt in order with its outcome, including side-goal quick
      closes.
- [ ] `--no-quick-close` and the hidden `--no-rung0` both skip the quick close. The proof files are
      byte-identical to those written before this story with the same flags.
- [ ] `cargo test` passes.

## 5. How to verify

```sh
D=target/debug/domino
cd example-projects/hello-world-oracle-rename-new
$D easycrypt prove --theorem Proof --proofstep 0 -f
$D easycrypt prove --theorem Proof --proofstep 0 -f --no-quick-close
$D easycrypt prove --theorem Proof --proofstep 0 -f --no-rung0
```

Compare each run's proof file with the same run on the commit before this story (built in a
separate worktree). On the page, open a closed node, an admitted node and the node in flight
during a live run, and check the chip and the attempts list. Repeat the first run on kem-dem-cca-ssp
`PKENC` for a fallback-closed side goal.
