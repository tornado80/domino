# The oracle is the unit of parallelism, and each oracle is a lemma of its own

**Status:** accepted. Implemented by
`docs/stories/easycrypt/68-oracle-lemmas-and-parallel-oracles.md`. Changes the rule of ADR 0006
and `CONTEXT.md` that the equivalence is the unit of parallelism.

An equivalence's proof was one lemma: after `call (: inv …)`, each oracle was one bullet, and one
EasyCrypt process proved the oracles one after another. On Full4WHS one equivalence takes up to
11.9 h, and its oracles are independent: the `call` rule leaves, for each oracle, a goal
`equiv[G1.O ~ G2.O : ={arg} /\ … ==> ={res} /\ …]` that does not mention the adversary.

We decided that each oracle is an **oracle lemma** in a file of its own, `Eq_<L>_<R>_<O>.ec`, flat
in the export directory. The equivalence's file `Eq_<L>_<R>.ec` only joins them: the `byequiv`, the
`call`, the base case, and one `conseq` for each oracle. Each oracle has its own session record and
saved tree in `session/Eq_<L>_<R>/`. A proof job proves its oracles in up to `--jobs N` EasyCrypt
processes at once, and two proof jobs may work on different oracles of one equivalence. No file has
two writers.

This is what Rocq and Isabelle do: they check opaque lemmas in parallel, one lemma at a time,
because a lemma's statement is known without its proof.

## Considered options

- **All oracle lemmas in one file, with workers inside one proof job.** Rejected: one writer must
  join the workers' scripts, parallelism exists only inside one job, and the batch compile stays
  serial.
- **No lemma split; each worker replays the prelude and proves one bullet** (how the `reprove.py`
  prototype worked). Rejected: it gives no separate lemma, and each worker pays for the prelude.
- **A subdirectory for each equivalence's oracle files.** Rejected by the owner: the proof files
  stay flat.

## Consequences

- The lock, the session record, sealing, respawn and resume work per oracle.
- The batch compile of each oracle file can also run in parallel, and EasyCrypt caches each one.
- The glue closes each oracle with `by conseq <lemma> => /#.`: the `call` goal names the
  oracle's parameters where the lemma says `={arg}` (story 68).
- A name rule must reject an oracle whose file name would collide with another file of the
  export (for example an oracle called `Invariants`).
