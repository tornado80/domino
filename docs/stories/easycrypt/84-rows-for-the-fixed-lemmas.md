# Story 84 — Rows for the fixed lemmas

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 82 (83 for the bar view).
**Blocks:** nothing.
**ADR:** 0020 (point 6).
**Decisions:** grilling of 2026-10-21, Questions 5 and 8.

A **progress** story, Rust only. Test-first.

---

## 1. Why this story exists

After its oracles, a package-invariant job checks the frame lemmas `Frame_<V>_<O>.ec` and the start
lemma `PkgInv_<V>_init.ec` (two attempts). It sends each file whole to an EasyCrypt (story 76,
commit `37780a22`). `src/easycrypt/tactics/fixed.rs` sends no progress event, so this stage is
silent, before and after story 68. A start lemma can take minutes.

## 2. Work to do

`prove_fixed_lemmas` gets the job's `JobProgress`. For each file it checks:

- `job.oracle(<file stem>)` makes a row (`Frame_Ctr_Peek`, `init`);
- `ItemStarted { phase: Tactics, name: "check file" }` before the file is sent; for the start
  lemma, `ItemStarted { name: "attempt k/2" }` before each attempt;
- `SentenceSent` with the first line of what is sent, so the row's timer starts again;
- the row is dropped when the file is accepted or admitted.

```
PkgInv_Ctr  oracles 4/4 done
  Frame_Ctr_Peek   check file                     5s
  init             attempt 2/2                   31s
```

Plain key: `PkgInv_Ctr/Frame_Ctr_Peek`. No new event kind.

Rejected (ADR 0020): a `FixedLemma { file, attempt }` event; no progress for the fixed lemmas.

## 3. Tests first

- [ ] Event level (`RecordingBoard`, `FakeEasyCrypt`): a package-invariant job with a frame lemma and
      a start lemma gives a row for each file, with `ItemStarted` and `SentenceSent`; the start lemma
      has one `ItemStarted` for each attempt.
- [x] Render level (`InMemoryTerm`): the frame row shows `check file` under the job's header.
- [ ] A rerun that skips files already accepted (`37780a22`) makes no row for them.

## 4. Acceptance criteria

- [ ] All tests of §3 green; the frame and start files are byte-identical before and after.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
