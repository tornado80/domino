# Story 68 — Each oracle is a lemma of its own, and oracles are proved in parallel

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 33 (seal), 35–38 (proof job, record, lock, resume), 67 (`session/<Eq>/`), ADR 0008.
**Blocks:** 69.
**ADR:** 0013.

A **translation and proof-job** story, Rust only. The tactics inside an oracle do not change.

---

## 1. Why this story exists

An equivalence's proof is one lemma today: after `call (: inv …)`, each oracle is one bullet
(`+ proc; inline. …`), and one EasyCrypt process proves the oracles one after another. On Full4WHS,
H6_1_1 ~ H7_0 takes 11.9 h and H7_1_1_0 ~ H7_1_1_1 8.7 h, with 12 independent oracles each.
`CONTEXT.md` said that the equivalence is the unit of parallelism, so nothing could prove two
oracles of one equivalence at once.

The `call` rule leaves, for each oracle, the goal
`equiv[G1.O ~ G2.O : ={arg} /\ inv … ==> ={res} /\ inv …]`. It does not mention the adversary, so it
can be a lemma of its own, outside the section. The owner wants one lemma for each oracle, and the
files flat in the export directory (grilling of 2026-10-09/12, Question 9).

Vocabulary (`CONTEXT.md`, already updated): **Oracle lemma**, **Proof job** (the oracle is the unit
of parallelism), **Session record** (one for each oracle lemma), **Seal**, **Respawn**.

## 2. Inherited from earlier stories

- **Story 35 / ADR 0006:** a proof job proves one equivalence against the files of translation, and
  never translates. `is_proof_file` (`job.rs:65`) says which `Eq_*.ec` files a job owns.
- **Story 36:** the lock in `progress/<Eq>/`. **Story 37:** resume from the record. **Story 33:** the
  seal. **ADR 0008:** the saved tree of each oracle.
- **Story 67:** `session/<Eq>/record.json` and `session/<Eq>/<Oracle>.tree.json`.

## 3. Work to do

### 3.1 The files (all flat in the export directory)

- **`Eq_<L>_<R>_<O>.ec`**, one for each oracle `O`: `require`s the two `Comp_` files and the
  invariant file, and holds
  `lemma Eq_<L>_<R>_<O> : equiv[<L>.<O> ~ <R>.<O> : ={arg} /\ inv … ==> ={res} /\ inv …].`
  The proof job owns it. Translation writes it with `admit` as its proof, as a skeleton that
  compiles.
- **`Eq_<L>_<R>.ec`** joins them: `byequiv`, `proc; inline.`, `call (: inv …)`, the base case, and for
  each oracle `+ by conseq Eq_<L>_<R>_<O>.` Translation writes it, and no tactics run touches it:
  its content follows from the oracle list alone. `is_proof_file` no longer counts it.
- **A name rule** rejects an oracle whose file name collides with another file of the export (an
  oracle called `Invariants`, or `Eq_<L>_<R>_<O>` equal to another equivalence's file). The error
  names both.

### 3.2 Records, lock, resume

- `session/<Eq>/<O>.record.json` replaces `session/<Eq>/record.json`: one record for each oracle,
  with the same fields that the per-oracle part of today's record has. An old record of the whole
  equivalence is read and split on first use.
- The lock is for each oracle (`progress/<Eq>/<O>.lock`). Two proof jobs may work on different
  oracles of one equivalence; a second job on a locked oracle skips it with a message.
- Seal, respawn and resume work as today, on one oracle file.

### 3.3 Parallel oracles

- `prove --jobs N` (default 1) proves up to N oracles of the job's equivalences at once, each in its
  own EasyCrypt process. Each worker has its own transcript part, under `progress/<Eq>/<O>/`.
- The live page shows one row for each running oracle.
- The equivalence's report joins the oracles' sections in oracle order, whatever order they
  finished in.

### 3.4 Rejected alternatives (see ADR 0013)

- All oracle lemmas in one file, with one writer in one job.
- No lemma split, workers that replay the prelude (as `reprove.py` does).
- A subdirectory for each equivalence (the owner wants the files flat).

## 4. Acceptance criteria

- [ ] Translation of Simple4WHS writes one `Eq_<L>_<R>_<O>.ec` for each oracle and a glue
      `Eq_<L>_<R>.ec`. With every oracle admitted, `easycrypt compile Eq_<L>_<R>.ec` passes.
- [ ] A test: two proof jobs on different oracles of one equivalence both finish, and each writes
      only its own files.
- [ ] A test: `--jobs 3` on one equivalence runs three EasyCrypt processes; the report lists the
      oracles in oracle order.
- [ ] A test: resume from an old whole-equivalence record.
- [ ] A test: the name rule rejects an oracle called `Invariants`.
- [ ] The implementation report gives the wall time of H6_1_1 ~ H7_0 with `--jobs 1` and
      `--jobs 4`.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --proofstep <step of H6_1_1 ~ H7_0> --tactics --jobs 4
cd <out> && easycrypt compile Eq_H6_1_1_H7_0.ec
```
