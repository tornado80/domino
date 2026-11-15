# Story 110 — A stuck point names its partner, a cross and the other head

**Epic:** none. This is a follow-up of the 4WHS `program-mismatch` analysis (session
`program-mismatch_in_4WHS-mac_and_4WHS-prf-mac`).
**Branch:** `amir/easycrypt-export`
**Depends on:** —
**Blocks:** —
**ADR:** `docs/adr/0025-a-stuck-points-reason-carries-its-partner.md`.
**Decisions:** the owner, 2026-11-14, grilling "skippable randomness mapping", Questions 1 to 8.

A **debugger** story: `src/debug/lockstep.rs`, `src/debug/lockstep_report.rs`,
`src/debug/lockstep_viewer.rs`, `src/easycrypt/job.rs`, tests and fixtures. Test-first. No proof
behaviour changes.

---

## 1. Why this story exists

When no head sampling is independent, lockstep execution records a stuck point, and the proof
admits it. Today the stuck point has one of four reasons, for the first stuck side only. Thus:

- The partner is not recorded, although `classify` finds it (the valid premise `i`).
- A cross (**crossed samplings**, `CONTEXT.md`) is not named. It shows as `partner-not-at-head`.
- The echo of a cross (the partner was already drawn) shows as `no-partner-reachable` or as
  `partner-not-at-head`. It looks like a second problem.
- The other head's reason is not recorded, so the viewer cannot tell why the other side did not
  go first.
- A mapping that pairs one draw with two draws is hidden: `classify` uses the first valid
  premise.

## 2. The facts this story uses

- `decide` resolves branches before samplings. So `decide_sampling` sees two samplings, or one
  sampling and a side that has ended (§6.1 of `docs/easycrypt-symbolic-execution.md`).
- A stuck point exists only where no head is independent.
- `classify` asks one OR query, then one or two queries for each premise (§6.2).
- The `Pairing` of each candidate has `left_sample`, `right_sample`, `offset_left` and
  `offset_right`. The partner's draw number is the offset on the other side.
- A path condition only gets more conjuncts down a path. So a draw that is now paired for certain
  was drawn at an earlier stuck node or synchronized node, never as independent (§6.4.2).
  `drawn_at` always exists.
- The injectivity check of the mapping is opt-in on `prove` (`injective_randmap`). The debugger
  does not assume it.
- `SavedTree::VERSION` is 1 (`src/easycrypt/job.rs`). The resume path turns a read error into a
  restart of the oracle (`src/easycrypt/tactics/mod.rs`, `restart(...)`).
- The driver reads a stuck point only through `reason.as_str()`, for the admit claim
  `stuck/<reason>` (`src/easycrypt/tactics/driver.rs`, `NodeKind::Stuck`).

## 3. What to build

### 3.1 The reason carries its data

`StuckReason` holds the data of its row:

| Reason (`as_str`) | Data |
|---|---|
| `pairing-unknown` | — |
| `mapping-not-injective` | `partners: Vec<Partner>` |
| `partner-already-drawn` | `partner: Partner`, `drawn_at: usize` (node) |
| `no-partner-reachable` | `partner: Partner` |
| `crossed` | `partner: Partner`, `other_partner: Partner` |
| `partner-not-at-head` | `partner: Partner` |
| `pairing-sat-not-valid` | — |

`Partner` is `{ side, sample, draw }`. `sample` uses the same `<instance>.<oracle>.<name>` form as
`StuckPoint::sample`. `as_str()` stays the one name of each reason, with no data.

### 3.2 `classify` selects the row

Both heads are classified before a reason is selected. Rows 6 and 7 need the other head. The order
is the table of §6.4.2:

1. pairing-unknown,
2. mapping-not-injective,
3. partner-already-drawn,
4. no-partner-reachable,
5. crossed,
6. partner-not-at-head,
7. pairing-sat-not-valid.

Rule for "already drawn": the partner's draw number is lower than the number of times the other
side has drawn that sample on this path. `drawn_at` is the node where it was drawn. The engine
keeps, for each side, which node drew each `(sample, draw)` on the current path.

The OR query and the per-premise loop do not change. All premises are still asked, so row 3 sees
every valid premise.

### 3.3 The stuck point records the other head

`StuckPoint` gets `other_head: Option<StuckReason>`. It is `None` exactly when the other side has
ended. `crossed` stays its own reason.

### 3.4 Readers

- `describe_stuck` (`lockstep_report.rs`): show the partner, `drawn_at` as `N<k>` and the other
  head's reason.
- The viewer (`lockstep_viewer.rs` and its page): the same data on the stuck node. An echo links
  to `drawn_at`.
- The driver: no change in logic. The admit claim gets the new names through `as_str()`
  (`stuck/crossed`, `stuck/partner-already-drawn`, …).
- `SavedTree::VERSION = 2`.

### 3.5 Docs

- `docs/easycrypt-symbolic-execution.md` §6: remove the status note when it is done, and remove
  §6.4.1, or mark it as history.
- `docs/proving-algorithm.md`: the `stuck` admit row names the new reasons, if it lists them.

## 4. Tests first

In `src/debug/lockstep_run.rs`, on the `testdata/lockstep/rules` project:

1. **Change** `samplings_in_opposite_orders_are_stuck_with_the_reasons_of_their_places`
   (`StuckOrder`). Expected:
   - S1 `left` `crossed { partner: right s1#0, other_partner: left s2#0 }`, with
     `other_head: partner-not-at-head`,
   - S2 `right` `partner-already-drawn { partner: left s1#0, drawn_at: N1 }`, with
     `other_head: None`.
2. **Keep** `a_mapping_that_depends_on_an_argument_is_a_stuck_point` (`StuckArg`). S1 also gets
   `other_head: pairing-sat-not-valid`.
3. **New fixture, row 3:** a custom mapping that pairs left `s` with right `s` and also with right
   `t`, with no condition. Expect `mapping-not-injective` with two partners.
4. **New fixture, row 7:** left `s1` is paired with right `s2` for certain, and right `s1` is
   paired with left `s2` only when `x > 0`. Expect S1 `partner-not-at-head`, with
   `other_head: pairing-sat-not-valid`.
5. **New fixture, echo while the other side runs:** the left draws `s1, s2, s3`, the right draws
   `s2, s1, s3`, and the mapping is `simple`. Expect:
   - S1 `left` `crossed` at N1,
   - N2 synchronized (`s2`),
   - S2 `left` `partner-not-at-head { partner: right s3#0 }`, with
     `other_head: partner-already-drawn { partner: left s1#0, drawn_at: N1 }`,
   - S3 `right` `partner-already-drawn { drawn_at: N1 }`,
   - S4 `right` `partner-already-drawn { drawn_at: N3 }`.
   
   Today, the right head's echo at N3 is discarded, and S3 and S4 are `no-partner-reachable`.
6. **Change** the progress and summary tests (`progress_events_report_nodes_pairs_and_stuck_points`,
   `the_summary_names_stuck_points_failures_and_the_stop_reason`), the viewer rollup tests and
   `src/easycrypt/job.rs` (`stuck/partner-not-at-head` claim) to the new names.
7. **New, `job.rs`:** a version 1 tree is refused with "version 1, but this Domino reads
   version 2". A tree with a stuck point of each new reason round-trips through `to_json` and
   `read`.

## 5. Acceptance criteria

- [ ] All tests of §4 green, with filtered test runs only. `cargo clippy` clean.
- [ ] Complexity: `classify` and `decide_sampling` within budget
      (`.sdlc-workspace/crap-coverage.sh <filter>`). If not, the row selection becomes a function
      of its own.
- [ ] `domino easycrypt debug` on `testdata/lockstep/rules`, oracle `StuckOrder`: the viewer shows
      S1 as `crossed` and S2 as `partner-already-drawn` with a link to N1.
- [ ] No change in any `.ec` proof text except the `stuck/<reason>` names.
- [ ] `docs/easycrypt-symbolic-execution.md` §6 describes the code as built.

## 6. Rejected alternatives

See ADR 0025, "Considered options". In short:
- fields next to the reason (Shape 1),
- a `swap` plan for a cross,
- do nothing,
- stop the walk at a cross,
- consume both heads at a cross,
- free variables in place of the candidate list,
- "one head has a partner, so the other head is independent",
- pick the first of two valid partners,
- read version 1 trees,
- the reason data in the admit comment.
