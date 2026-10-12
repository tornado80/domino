# Story 66 — A case split on updated keys (part fallback 4)

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 64, 65.
**Blocks:** nothing.
**Supersedes:** story 29 (a design record that was never scheduled; its method is no longer
possible, see §3.4).

A **tactics** story, Rust only. Translation does not change.

---

## 1. Why this story exists

A relation that quantifies over a table's keys, `forall c, … m.[c] …`, usually defeats smt after
a write `m.[k <- v]`. The proof must split on whether the bound key is the written one. Hand-written
proofs do this all the time (433 `case` uses in `~/Research/ec4whs`, story 29 §1).

After story 64, the leaf runs `auto` (wp), so the writes are in the goal as `m.[k <- v]`. The
opening loop introduces the relation's binders (`move => ctr1 /=.`).

Evidence: the `reprove.py` prototype on H2_1 ~ H3_0 (`Eq_H2_1_H3_0_Reproved.ec`) has 30
`case (ctr1 = ctr{2}) => [->|?].` sentences. Each one was kept only because every one of its cases
closed. In each of them, the key is a program variable at a memory.

The owner asked if the debug effect (`src/debug/effect.rs`, the new state of a path) can give this
information. It has it, as a rendering, but the module says that it is "human-facing, deliberately
lossy … never fed to the solver", and it uses SMT names (`old.Prot.ctr`). The EasyCrypt goal has
the same information in the terms that EasyCrypt accepts (grilling of 2026-10-09/12, Question 3).

Vocabulary (`CONTEXT.md`): **Leaf part**, **Fallback sequence**.

## 2. Inherited from earlier stories

- **Story 64:** the opening loop introduces the binders, so the driver knows their names and
  types.
- **Story 65:** the sequence keeps place 4 for this fallback.
- **Story 61:** `want: full` gives the whole front goal (with its type table).

## 3. Work to do

### 3.1 Finding the pairs

On the part's conclusion (`want: full`):

- an **updated map** is an application of the map-update operator (FMap `set`, printed
  `_.[_ <- _]`), with its key `k`;
- a binder `b` that the opening loop introduced is **over the keys** of that map when `b` is the
  index of a read (`m.[k <- v].[b]`) or of a membership test (`b \in m.[k <- v]`) on it;
- `k` must be an **atom**: a program variable at a memory (the JSON `pvar` node, with its `mem`;
  printed `Comp_H3.Pkg_Inst_KX.ctr{2}`) or a local (an introduced name). Skip a key that is not an
  atom.

The pairs `(b, k)` are in the order in which they occur in the goal, without duplicates. At most
**6** pairs (at most 64 cases). With more, this fallback does not run.

### 3.2 The split

For the first pair, send `case (b = k) => [->|?].` Then, in each case, go on with the next pair
(in the `->` case, drop the pairs of `b`), and at the end send `smt(<hints>).` If every case closes,
the part is closed. If one case fails, undo to the state before the first `case`, and the part goes
on to the admit. The sentences are bullets, one for each case.

### 3.3 Admits

The admit comment of story 65 shows the outcome of fallback 4's last `smt`. When fallback 4 did not
run (no pair, or more than 6), `smt:` shows fallback 3's outcome.

### 3.4 Rejected alternatives

- **Keys from the debug effect.** It needs a second copy of the naming rule from SMT names to
  EasyCrypt terms (the bug class of story 53). It makes a lossy rendering the input of a proof.
  After wp, the key in the goal is in program variables at `&1`/`&2`, not in the effect's names.
- **EasyCrypt prints the key** (the fork adds `pp` to each map-update key). This covers keys that are
  not atoms, but it changes the fork. Add it later if the report shows that skipped keys matter.
- **Story 29's method** (`rewrite get_setE`, then copy the `pp` of the `if` condition). ADR 0009
  removed `pp` from formula subnodes, so the condition has no text.

## 4. Acceptance criteria

- [ ] A unit test on a JSON goal with `forall c, (m.[k{2} <- v]).[c] <> None => …`: one pair
      `(c, Comp….k{2})`.
- [ ] A unit test: a key `k{2} + 1` gives no pair; a binder used only outside an updated map gives
      no pair; 7 pairs gives no split.
- [ ] A unit test with a scripted session: two pairs give the sentences of §3.2, in order, with
      bullets; one failing case undoes the whole split.
- [ ] The implementation report gives, for H2_1 ~ H3_0 and H6_1_1 ~ H7_0, how often fallback 4 ran
      and closed, and the admits before and after.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --proofstep 4 --tactics --no-quick-close
grep -c 'case (' <out>/Eq_H2_1_H3_0*.ec
```
