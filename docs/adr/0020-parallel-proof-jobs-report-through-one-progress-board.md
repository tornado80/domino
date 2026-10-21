# Parallel proof jobs report progress through one progress board of rows

**Status:** accepted. Implemented by `docs/stories/easycrypt/82-the-progress-board-and-plain-progress.md`,
`83-one-bar-row-for-each-running-oracle.md` and `84-rows-for-the-fixed-lemmas.md`. Grilling of
2026-10-21, Questions 1–8.

Before story 68 one oracle had the terminal at a time. Its lockstep execution showed the debugger's
two bars, then one `tactics` bar showed `PKENC  N7/23  smt(dec_enc).  12s` (stories 39, 40). The
observer, `BarExportObserver`, keeps one bar for each phase and one current oracle, and it is not
`Send`. Two changes added threads, and each gave its threads `NopExportObserver`:

- the oracle workers of `--jobs N`, N > 1 (story 68, `oracles.rs`);
- the side-invariant and package-invariant chain that runs next to the equivalences (stories 69,
  76, 77, `tactics/mod.rs`). A full `prove` hits this case even with `--jobs 1`.

No test ran parallel work with a recording observer, so no test failed. The fixed lemmas of a
package-invariant job (frame and start lemmas, `fixed.rs`) never sent progress. The debugger's
`BarObserver` keeps one global `ACTIVE_BARS`, so two lockstep displays at once would write over each
other.

We decided:

1. **One progress board for each command run.** `main.rs` makes it from `--progress`. The per-oracle
   factory `&mut dyn FnMut() -> Box<dyn ExportObserver>` moves up one level:
   `ProgressBoard::job(stem, oracles) -> JobProgress`, and `JobProgress::oracle(name) -> Box<dyn
   ExportObserver>`. The board is `Sync`, the job progress is `Send + Sync`, and a worker sees only
   `ExportObserver`, as before. `--jobs 1` and `--jobs N` take the same path.
2. **No status method on the job progress.** It counts the oracle rows it made and dropped (done,
   running, pending = oracles − started). The board of the proof job keeps its own counts.
3. **Bar mode: a header row for each running job, one row for each running oracle.** The row shows
   lockstep (node, node kind, pair tally), then the node, the first line of the tactic sent to
   EasyCrypt, and the time it waits for the answer (reset on each sentence). A finished row leaves
   the live area, and its summary line prints above it. The debugger's own two-bar display stays for
   `domino debug`.
4. **Plain mode: the same lines as before, each with the key `<job>/<oracle>` at the start**, written
   in one call. No cursor control, no timer.
5. **The board is the one screen.** The bar board registers its `MultiProgress` in `ACTIVE_BARS` and
   clears it when it is dropped. The 18 callers of `eprintln_above_bars` and the Ctrl-C handler do not
   change. A debug assertion checks that two screens are never active.
6. **The fixed lemmas are rows too**, made by `JobProgress::oracle` with the file's name. They use
   the events that exist (`ItemStarted`, `SentenceSent`), with no new event kind.

## Considered options

- **A channel to one renderer thread** (the `sitrep`, `prodash` pattern). Rejected: it needs a
  second, owned copy of `ExportEvent` (change amplification for each new event), a map keyed by
  strings, and a thread with a shutdown protocol next to Ctrl-C. indicatif already draws from any
  thread.
- **The old display for each worker, stacked** (a `tactics` bar and two debugger bars for each
  oracle). Rejected: up to 15 lines with 4 workers and the chain, and it keeps the singleton
  `ACTIVE_BARS` for each lockstep run.
- **One shared line that rotates through the running oracles.** Rejected: it hides which oracle is
  slow (GHC issue 20877).
- **`counts(done, running)` on `JobProgress`.** Rejected: a status pushed from outside that the job
  progress can count itself.
- **Plain output kept in a buffer for each oracle, printed when it ends.** Rejected: an oracle can run
  for 11.9 h (ADR 0013), and the log is silent all that time.
- **A heartbeat line in plain mode.** Rejected: a log flood, and a timer thread.
- **A `Printer` handle passed to each call site, no global.** Rejected: the Ctrl-C handler still needs
  a global, and 18 call sites change for no visible gain.
- **A `FixedLemma` event kind.** Rejected: one sender, and all observers must handle it.
- **A flag for the most rows on screen** (nextest's `--max-progress-running`). Rejected: `--jobs`
  already limits the rows.

## Consequences

- `SharedProgress`, `Shared` and the `workers == 1` branch of `oracles.rs` go.
- A new `DebugEvent` must be shown in two places: the debugger's bars and the prove row.
- Tests check the contract at the event level (a recording board, `--jobs 2`, the chain with
  `--jobs 1`) and the layout on indicatif's `InMemoryTerm` (feature `in_memory`, for tests only).
