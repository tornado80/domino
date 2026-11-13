# Story 104 — A sampled variable that `#pre` mentions gets a `seq-post` admit

**Epic:** EasyCrypt export: the reduction walk — `docs/stories/easycrypt/epic-the-reduction-walk.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** —
**Blocks:** 106.
**ADR:** `docs/adr/0024-a-reductions-oracle-lemma-is-proved-by-a-strict-reduction-walk.md`
(decision 5).
**Decisions:** owner's grilling session of 2026-11-12/13, Question 11.

A **prover** story: `src/easycrypt/tactics/goals.rs`, `src/easycrypt/tactics/driver.rs`, tests.
Test-first.

---

## 1. Why this story exists

At a synchronized sampling, the prover sends `seq 1 1 : (#pre /\ x{1} = y{2})`. This is correct only
if `x{1}` and `y{2}` do not occur in `#pre`. If they occur, the sampling writes over a value that
`#pre` speaks about, and EasyCrypt refuses the side goal.

EasyCrypt does not prevent this. `inline` renames a local only when its name clashes with a name in
the caller. A variable keeps its name when the code samples into it again:

- an oracle argument that the oracle samples into (`MAC.Init` and `key`, diagnosis of 2026-10-30:
  after `sp`, `#pre` holds `key{2} = kmac{2}`);
- a local that the oracle assigned before;
- a state field (a global `M.x`). Then `#pre` holds `(glob M){2}` as an argument of the invariant
  operator, not `M.x{2}`.

In the 4WHS-mac runs, the sentence `seq 1 1 : (…); 1: auto => />.` failed at once, the blind fallback
tried its trials on the same sampling, and the goal was admitted `program-mismatch`. The place was
correct; the reason was wrong.

## 2. The facts this story uses

- `json.rs:279`: an `equiv` goal has `pre: Option<Box<Form>>`. A program variable is a `pvar` node
  with `name`, `scope` (`local` or `global`) and its memory.
- `goals.rs:241` `mentions_binder`: a free-variable walk over a `Form`.
- `driver.rs:2022` `sampling()`: builds the `seq 1 1` post from the heads' `lvalue.pp`, and calls
  `seq_post_admit` when assignments come before the sampling (`kl + kr > 0`).
- `driver.rs:2080` `seq_post_admit`: reason `seq-post`, claim `sampling`, view `Verified`.

## 3. What to build

1. **A pure check** in `goals.rs`: `sampled_in_pre(goal, side, lvalue) -> bool`. It is true when the
   precondition mentions the variable in the memory of `side`:
   - a local or global `pvar` with the same name; or
   - for a global `M.x`, a `glob M` term (or `glob` of a module that contains `M`).
2. **`sampling()`** calls it before it sends `seq 1 1`. If it is true on either side, it calls
   `seq_post_admit` with the claim `sampling: <x>{<side>} in #pre` and sends no `seq`.
3. The check is public in the crate, because story 106 calls it too. It takes the goal and
   gives a Boolean. It knows nothing about the walk that calls it.
4. **Docs:** `docs/proving-algorithm.md` §9.1 and §9.2: `seq-post` also means "the sampled variable is
   in `#pre`". Remove the word "defensive" from that case in §9.2.

## 4. Tests first

- [x] Unit test: a goal whose `pre` has `pvar key` in memory `&2`, and a right head `key <$ dbits_n`:
      the check is true for side 2 and false for side 1.
- [x] Unit test: a goal whose `pre` has `(glob Pkg_MAC.MAC){2}` and a right head
      `Pkg_MAC.MAC.k <$ d`: the check is true.
- [x] Unit test: the `Send2` goal at the nonce (`ni1 <$ dbits_n` on both sides, `ni1` not in `pre`):
      the check is false.
- [x] Unit test: `sampling()` on the first goal writes `seq-post` with the claim
      `sampling: key{2} in #pre` and sends no `seq` (with a goal handed to the function, no
      EasyCrypt).

## 5. Acceptance criteria

- [x] All tests of §4 green, with filtered test runs only. `cargo clippy` clean.
- [x] Complexity: every touched function within budget (`.sdlc-workspace/crap-coverage.sh <filter>`).

## 6. Rejected alternatives

- **No check:** the side goal fails, and the admit says the proof needs work when the real cause is
  the shape of the translated code.
- **Rewrite the postcondition** (drop the conjuncts of `#pre` that mention the variable). `#pre` after
  `sp` is one large existential formula. Later, if the case occurs again.
