# Answers carry what the sentence asks for

**Status:** accepted. Amends ADR 0009. Implemented by
`docs/stories/easycrypt/61-answers-carry-what-the-sentence-asks-for.md`. Changes the protocol from
`domino-json/2` to `domino-json/3`.

ADR 0009 made each answer carry the front goal in full and the kind of every open goal. The
Full4WHS runs of 2026-10-08 still spent 11.6 h of 29 h in the round trip outside EasyCrypt's
tactic time, over 134 GB of answers. Two kinds of answer carried most of it:

- **Error answers** (24 % of the bytes): a failed fallback, a failed `rewrite`. A sentence that
  fails changes no goal, and Domino already has that goal.
- **Answers that Domino reads only at the head** (49 % of the bytes): after `split.`, `move =>`
  and `rewrite /op.` Domino looks only at the top of the conclusion (`forall`, `=>`, `/\`, an
  operator) and at the names of the hypotheses.

On a measured leaf answer (2.15 MB), the `ty` field of the nodes was 70 % of the bytes, with only 48
distinct types.

We decided:

1. **Each request is one JSON line**, `{"sentence": "...", "want": "status" | "head" | "full"}`.
   `status` gives the status, the kinds, the messages and the timing. `head` also gives the front
   goal's conclusion to a fixed depth and the names and types of its hypotheses. `full` gives the
   whole front goal, as `domino-json/2` does.
2. **A sentence that fails gives no front goal**, whatever it asked for.
3. **A `full` goal has a type table.** The answer lists each distinct type one time, and each node
   refers to it by index.

The caller says what it reads, so EasyCrypt keeps no mode between sentences, and each answer
depends only on its request.

## Considered options

- **A sticky pragma** (`pragma Json:head.`). Rejected: the mode is state on both sides. Domino must
  remember what mode EasyCrypt is in, and each change of mode costs a round trip.
- **Batches of sentences in one request.** Rejected for now: the driver would need to handle a
  failure in the middle of a batch. After story 60 a small answer costs milliseconds, so the
  number of round trips matters much less than their size.
- **Subterm sharing** (a table of distinct subterms, 643 in place of 24,045 nodes on the measured
  answer). Rejected for now: every matcher in `goals.rs` reads a tree. Come back to it if the
  report still shows `full` answers as a cost after stories 60 and 61.
- **Drop `text`.** Not worth it: 2 % of the measured answer.

## Consequences

- An EasyCrypt that speaks only `domino-json/2` does not work with this Domino. The error names
  both versions and `DOMINO_EASYCRYPT`.
- The transcript keeps what each answer had. A `status` answer has no goal to cap.
