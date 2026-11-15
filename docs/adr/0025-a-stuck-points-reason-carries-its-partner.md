# A stuck point's reason carries its partner

**Status:** accepted. Implemented by `docs/stories/easycrypt/110-a-stuck-point-names-its-partner.md`.
Grilling of 2026-11-14 ("skippable randomness mapping"), Questions 1 to 8. The algorithm is in
`docs/easycrypt-symbolic-execution.md` §6.

Lockstep execution already tests, for each head sampling, whether the randomness mapping can pair
it with any draw of the other side (`classify`, `src/debug/lockstep.rs`). If it cannot, the
sampling is independent and goes alone. If no head is independent, the node is a **stuck point**,
and the proof admits it. But a stuck point records only one of four reasons, for the left side
only. It does not name the partner, although `classify` finds it. It does not name a cross. And
the echo of a cross, where the partner was already drawn, reads as `no-partner-reachable`, as if
it were a second problem. The right head's classification, which holds the echo while the left
side still runs, is discarded.

We decided:

1. **The partner data is a diagnosis only.** It goes into the stuck point, the viewer and
   `trace.json`. The proof does not change.
2. **Each reason carries its own data** (Shape 2). `StuckReason` gets the eight rows of §6.4.2:
   - `pairing-unknown`,
   - `mapping-not-injective { partners }`,
   - `partner-already-drawn { partner, drawn_at }`,
   - `no-partner-reachable { partner }`,
   - `crossed { partner, other_partner }`,
   - `partner-not-at-head { partner }`,
   - `pairing-sat-not-valid`.
   
   `partner-not-at-head` keeps its name, with a narrower meaning: the partner is not drawn yet,
   and there is no cross.
3. **A stuck point records the other head's reason:** `other_head: Option<StuckReason>`. It is
   `None` exactly when the other side has ended.
4. **The walk at a stuck point does not change.** The proof admits once, at the stuck point, and
   the admit covers the subtree. The walk lets the first stuck side draw alone and goes on, so
   the admit keeps its Domino view.
5. **The admit comment shows only the reason name** (`stuck/crossed`). The driver reads only
   `as_str()`.
6. **`SavedTree::VERSION` goes to 2.** An old tree gives the existing read error, and the resume
   path restarts that oracle.

## Considered options

- **Fields next to the reason (Shape 1):** `partner: Option<…>` and `caused_by: Option<…>` beside
  the four old reasons. Rejected. It allows invalid states, for example a partner on
  `pairing-sat-not-valid`. Each reader must combine the reason and the fields to get the meaning
  (cognitive load, change amplification).
- **Plan a `swap` for a cross.** The export would move the partner to the head and then send
  `seq 1 1`, with a rollback on failure. Rejected for now. Domino cannot see the data
  dependencies that EasyCrypt checks for `swap`, and no project has a `stuck/...` admit to test
  it on. The partner data of this ADR is the input for a later decision.
- **Do nothing.** Rejected. The viewer then cannot tell a cross from its echo, and a
  non-injective mapping stays hidden.
- **Stop the walk at a cross.** Rejected. The admit loses its Domino view below.
- **Consume both heads at a cross.** Rejected. It gives two echoes instead of one, because both
  partners are then in the past.
- **Free variables for the partner, in place of the finite candidate list.** Rejected. The solver
  can find a partner that does not exist in the oracle, for example a draw number above the
  maximum count, so an independent sampling looks stuck. A model of the OR query is still a
  possible speed-up for stage 2 (§6.6).
- **"If one side's head has a partner, the other side's head is independent."** Rejected as
  unsound. With crossed samplings (L1↔R2, L2↔R1), R1 has a partner and L1 is not independent.
  Each head must be tested separately.
- **Pick the first of two valid partners** (no `mapping-not-injective`). Rejected. It hides a
  mapping defect.
- **Read the old reason names of a version 1 tree.** Rejected. `partner` would become an `Option`
  again, which brings back the invalid states of Shape 1, for one migration only.
- **The reason data in the admit comment.** Rejected. It couples the driver to the reason data
  (change amplification). The stuck id already links the admit to the data.

## Consequences

- `trace.json`, the viewer, `describe_stuck` and the tests that match the old reason strings
  change.
- An interrupted oracle that has a version 1 tree is proved again from the start, one time.
