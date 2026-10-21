# Story 82 — The progress board, and plain progress for parallel jobs

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** nothing new.
**Blocks:** 83, 84.
**ADR:** 0020 (points 1, 2, 4).
**Decisions:** grilling of 2026-10-21, Questions 1, 3, 4, 7 and 8.

A **progress** story, Rust only. Proving and the files it writes do not change. Test-first.

---

## 1. Why this story exists

Since story 68 the terminal shows nothing while parallel work proves:

- `oracles.rs:217-223`: with `--jobs N`, N > 1, each worker gets `NopExportObserver`;
- `tactics/mod.rs:797-799`: the side-invariant and package-invariant chain runs on its own thread
  with `NopExportObserver` whenever the theorem has equivalences too. A full `prove` hits this
  case even with `--jobs 1`.

The cause: `ExportObserver` is not `Send`, and the factory `&mut dyn FnMut() -> Box<dyn
ExportObserver>` can be used by one thread only. No test ran parallel work with a recording
observer.

## 2. Work to do

### 2.1 The seam (`writers/easycrypt/progress.rs`)

```rust
pub trait ProgressBoard: Sync {
    /// A proof job starts. Its oracle rows go under it.
    fn job(&self, stem: &str, oracles: usize) -> Box<dyn JobProgress>;
}
pub trait JobProgress: Send + Sync {
    /// An oracle starts on this thread. Dropping the observer ends its row.
    fn oracle(&self, name: &str) -> Box<dyn ExportObserver>;
}
```

`ExportObserver` and `DebugObserver` do not change. `JobProgress` has **no** status method: it
counts the rows it made and the rows dropped (ADR 0020 point 2).

### 2.2 The callers

- `run_tactics_observed` and `run_jobs`/`run_side_chain` take `&dyn ProgressBoard` in place of the
  factory. `main.rs` makes one board for each command run, not one for each theorem. The export
  phases before the tactics keep their own `ExportObserver`, unchanged.
- `prove_equivalence` calls `board.job(stem, queue.len())` once. Each worker calls
  `job.oracle(name)` for each oracle it takes. This replaces both `NopExportObserver`s.
- Remove `SharedProgress`, `Shared` and the `if workers == 1` branch: `--jobs 1` is one worker on
  the same path.
- The `tactics` phase events (`PhaseStarted`, `ItemStarted`, `PhaseFinished`) of the job now come
  from the job progress, not from each oracle.

### 2.3 Plain mode

`PlainProgressBoard`: each oracle observer writes the lines of `PlainExportObserver` with the key
`<stem>/<oracle>` at the start, in place of the indented oracle name. One `writeln!` on a locked
stderr for each line. The key comes from the observer, not from the event's `oracle` field. When an
oracle ends, the job writes `<stem>  oracles <done>/<total> done`.

```
Eq_H4_H5/PKENC  lockstep: started
SideInv_C/ENC  N3/9
Eq_H4_H5/DEC  N7/23
Eq_H4_H5/PKENC  lockstep: 23 joint paths, 1 stuck point in 41.2s
Eq_H4_H5  oracles 3/7 done
```

### 2.4 Bar mode in this story

A temporary `BarProgressBoard` that gives each oracle today's `BarExportObserver` behavior for
**one** running oracle at a time, and a `NopExportObserver` for the others. With `--jobs 1` and no
chain, the screen is the same as before. Story 83 replaces it.

### 2.5 Rejected alternatives (ADR 0020)

- A channel to one renderer thread, with an owned copy of `ExportEvent`.
- `counts(done, running)` on `JobProgress`.
- Plain output in a buffer for each oracle; a heartbeat line.

## 3. Tests first

A `RecordingBoard` test double records `(job, oracle, event)`. With `FakeEasyCrypt`:

- [ ] `--jobs 2`, an equivalence with 3 oracles: each oracle has `LockstepStarted`,
      `NodeStarted`, `SentenceSent` and `LockstepFinished` on its own key. No oracle is silent.
- [ ] A theorem with an equivalence **and** a side-invariant job, `--jobs 1`: the chain's oracles
      have events on their own keys.
- [ ] For each oracle, `--jobs 1` and `--jobs 2` give the same event sequence.
- [ ] Plain: each line starts with `<stem>/<oracle>` or `<stem>`; a job line after each oracle.

## 4. Acceptance criteria

- [ ] All tests of §3 green. The export tree, the session records, the pages and the reports are
      byte-identical before and after.
- [ ] No `NopExportObserver` is left in `oracles.rs` and `tactics/mod.rs`.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
