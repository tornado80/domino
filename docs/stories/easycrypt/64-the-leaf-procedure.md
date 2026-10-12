# Story 64 — The leaf procedure: exit path, `auto`, then open the goal

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 53, 62, 63.
**Blocks:** 65, 66.

A **tactics** story, Rust only. Translation does not change. The proof files change shape at the
leaves.

---

## 1. Why this story exists

At a leaf the run does this today (`leaf_of`, `reduce_leaf`, `solve_ambient`, `atom`;
`src/easycrypt/tactics/driver.rs:1570-1710`):

1. three leaf fallbacks, each "all or nothing" (`auto => /> &1 &2 *; smt().`, the same after `sp.`,
   the same with hints);
2. reduce: `sp. skip => &1 &2 hpre.`, else `auto. move => &1 &2 hpre.`, then the premise unfold;
3. a binary `split.` with a label for each part (the first conjunct is equal-output by position),
   `rewrite /op.` for the invariant's operators, `move =>` for binders and premises;
4. the part fallbacks.

What the transcripts of 2026-10-08 (all hops) show:

| Sentence | Sent | Kept | Time |
|---|---|---|---|
| Leaf fallback 1 | 673 | 470 | 2,004 s |
| Leaf fallback 2 (`sp.` + fallback 1) | 197 | 47 | 4,282 s |
| Leaf fallback 3 (with hints) | 156 | 7 | 1,545 s |
| Split role: `split.` / `move` / `rewrite` | 3,671 / 2,123 / 1,938 | all | 25,347 s |

And from `Proof_Statistics.md` and `Eq_H2_1_H3_0_Reproved.md`:

- `sp` at the leaf runs over the exit path. Each exit guard and the router's tail `if` become a
  disjunction with existentials. `sp.` and `auto.` hit the 60 s limit on 6 leaves, and each of them
  was admitted whole.
- Of the 840 admits, **560 have a `let` at the head** of the admitted goal, and **782 have a record
  literal** (`{| … |}.\`l_pkg_KX…`) in it. The walk cannot open a `let`, and nothing simplifies the
  projections.
- The `reprove.py` prototype decided the exit path with `rcondt`/`rcondf`, used `wp`, and opened
  the goal with `/=`. On 15 leaf blocks of H2_1 ~ H3_0 it went from 70 admits to 44, and closed the
  three whole-leaf admits in 3–7 s each.

The owner decided (grilling of 2026-10-09/12) that leaf parts do not need the labels that the
binary split exists for. The owner also decided that a part is admitted with the verdict of the
last claim operator that the run unfolded, or of the whole leaf.

Vocabulary (`CONTEXT.md`, already updated): **Exit path**, **Leaf part**, **Leaf budget**,
**Sentence role** (*exit path*, *reduce*, *split*; *leaf fallback* is gone).

## 2. Inherited from earlier stories

- **Story 50:** exit guards: the done-flag guard, the call-result guard, and the router's
  abort-flag guard. `src/writers/easycrypt/lower.rs` (module doc): a done-flag guard holds on every
  path that reaches it; the router's tail is `if (ec_result = None) { abort_flag <- true; }`.
- **Story 53:** `ambient_step`, `part_of_op`, `invariant_ops` as the one owner of operator names.
- **Story 62:** `invariant_ops` in call order. **Story 63:** no `sp` before a determined node, so
  the leaf can still hold straight-line code.
- **§3.6:** a leaf where Domino says that equal-output and invariant both fail is admitted at once.
- **Story 46:** the leaf budget is opt-in.

## 3. Work to do

### 3.1 The procedure

At a leaf (a terminal pair):

0. **§3.6 for the whole leaf**: unchanged.
1. **Decide the exit path** (role *exit path*). While either program still has an `if` (read from
   the front goal, `want: full`), send `rcondt{i} ^if; 1: by auto.` or
   `rcondf{i} ^if; 1: by auto.` for the first `if` of side *i*. Try first the decision that Domino
   predicts, then the other one:
   - a done-flag guard after the side's terminal: `rcondf`;
   - the router's tail `if (ec_result = None)`: `rcondt` when that side's terminal is an abort,
     else `rcondf`;
   - any other `if`: no prediction, try `rcondf` first.

   If neither decision is accepted, stop deciding: step 2's wp takes the `if` into the formula.
   Bound the loop by the number of `if`s that the goal shows.
2. **Reduce** (role *reduce*): `auto => &1 &2 hpre.` (`auto` runs wp, then `skip`). Then the
   premise unfold of story 62. If `auto` fails, or leaves a goal that is not a formula (`auto`
   accepts when `skip` cannot apply), the leaf is admitted whole, as today
   (`equal-output+invariant`).
3. **Open** (role *split*), on each goal, in a loop, until nothing changes:
   - `forall`: `move => <names> /=.`
   - `=>`: `move => hpreN /=.`, then the premise unfold on `hpreN` if it mentions the invariant's
     operators.
   - an application of an operator of `invariant_ops`: `rewrite /<op> /=.` If the operator stands for
     a claim (`part_of_op`: a state relation, a `PkgInv_` wrapper, a `GameInv_`), the part now
     belongs to that claim. **§3.6 for each claim:** if Domino says that this claim fails on this
     pair, admit the part at once, with no EasyCrypt time.
   - otherwise: `do split.` If it gives more than one goal, each one is a bullet and goes through the
     loop again with the same claim. `do split` can unfold an operator by itself (it reduces to find
     a `/\`). Such an operator gives no claim, because the run did not unfold it.
   - if nothing applies, the goal is a leaf part. Send it to the part fallbacks (`atom`; story 65
     replaces the sequence).
4. The **leaf budget**, if set, starts after step 2, as today.

`/=` (zeta, iota, beta) removes the `let`s and the record-literal projections, so the loop can open
the goals that it cannot open today.

### 3.2 What goes away

- Leaf fallbacks 1–3 and `Role::LeafFallback`.
- `sp. skip => &1 &2 hpre.` in `reduce_leaf`.
- The binary `split.` with two bullets, and the position rule (`Part::EqualOutput` for the first
  conjunct). `Part::Whole`, `Part::Relation` and `Part::SideInvariant` stay. A part with no claim
  is `Whole`, whose verdict is the worse of equal-output and invariant.
- The nested indentation of the binary split. Bullets nest only where the loop opens a part again.

### 3.3 Constraints

- `--no-quick-close` does not change.
- The number of parts is not predictable. The driver reads it from the kinds of each answer, and
  never predicts it.
- Each sentence is one round trip. Do not join sentences with `;` beyond what §3.1 shows.

### 3.4 Rejected alternatives

- **`split *` with labels** (decided earlier on 2026-10-07/09 in
  `~/Research/ec4whs/autogenerated/Full4WHS/split-star-leaf-splitting.md`, Questions 1–3; this
  story supersedes them). The labels only gave admit reasons. The owner accepts losing them.
- **Crush at the leaf**: `auto => /> &1 &2 *; split *.` Crush joins every goal that it cannot close
  into **one** conjunction (`t_crush`, `ecLowGoal.ml:2362`; tested on the fork), so a split must
  follow. The owner chose no crush at the leaf; crush is a part fallback (story 65).
- **`wp. skip => &1 &2 />.`** in two sentences: one more round trip for the same goals.
- **Keep leaf fallback 1 first**: it gives nothing that the new procedure does not give, and pays a
  second smt on each leaf that it does not close.
- **A portfolio** (several variants for each leaf, keep the best): multiplies leaf time. Later, with
  data from this story.

## 4. Acceptance criteria

- [ ] Unit tests of the driver with a scripted session:
  - [ ] the exit path: the predicted decision first; the other one when the first is refused; the
        loop stops when neither is accepted;
  - [ ] `auto` that leaves a program goal gives a whole-leaf admit;
  - [ ] the loop: `forall`, `=>`, an operator with a claim (and §3.6 for it), `do split` into three
        goals, and a goal that nothing opens;
  - [ ] no `split.` and no leaf fallback are sent.
- [ ] The admit of a part that the loop unfolded `StateRelation_x` in has claim
      `invariant/StateRelation_x`. A part with no unfolded claim operator has the whole leaf's
      verdict.
- [ ] The implementation report gives, for H2_1 ~ H3_0, H4 ~ H5 and H6_1_1 ~ H7_0: admits, whole-leaf
      admits, wall time and time by role, before (2026-10-08) and after.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt prove --theorem Full4WHS --proofstep 4 --tactics --no-quick-close
grep -c 'admit\.' <out>/Eq_H2_1_H3_0*.ec
```
