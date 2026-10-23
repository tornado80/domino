# Story 93 — Invariant selection keeps the conjuncts that share a table with the conclusion

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 69 and 77 (side invariants, `side_inv_<C>`), 92 (the pruned crush, `drop_ops`).
**Blocks:** nothing.
**ADR:** none. The rejected alternatives are in §4.
**Decisions:** owner's grilling session of 2026-10-23. The terms **pruned crush**, **footprint** and
**invariant selection** are in `CONTEXT.md`.

A **tactics** and **translation** story, Rust only. Test-first.

---

## 1. Why this story exists

Story 92 leaves 19 of the 62 side-goal admits: 1 `branch-condition` and 18 `side-goal`. The pruned
crush drops each `side_inv` premise. But some side goals need one or two conjuncts of a side
invariant, for example "two accepted sessions with the same `sid` have the same key" (H2_1 ~ H3_0
SameKey) or "a written MAC key is well formed" (H6_1_0 ~ H6_1_1 Reveal).

### 1.1 The recipe that closes 5 of them (experiments of 2026-10-22)

Keep only the `side_inv` of the memory in the conclusion. Open it with the abort premise. Keep only
the conjuncts that read a table that the conclusion also reads. Unfold them, revert them, and call
`smt`:

```
move=> /> &hr h0 h1 h2 h3 _ hs5 h6 h7 h8 h9;
have := hs5; rewrite /Comp_H6.side_inv_H6 /= => /(_ h6) [#] _ _ _ g5_3 _ g5_5 _ _ _ _ _ _;
clear hs5;
move: h0 h1 h2 h3 g5_3 g5_5 h6 h7 h8 h9;
rewrite /Comp_H6.GameInv_kmac__is__wellformed_of_H6 /Comp_H6.GameInv_no__overwriting__prf_of_H6 /=;
smt().
```

(`Eq_H6_1_0_H6_1_1_Reveal.ec:157`, one sentence.) This closed 5 goals that the pruned crush leaves:

| Goal | Kind |
|---|---|
| `Eq_H2_1_H3_0_SameKey.ec:115` | side-goal |
| `Eq_H6_1_0_H6_1_1_Reveal.ec:157` | side-goal |
| `Eq_H7_1_1_0_H7_1_1_1_Send2.ec:298` | side-goal |
| `Eq_H7_1_1_0_H7_1_1_1_Send2.ec:307` | side-goal |
| `SideInv_H7_Send2.ec:280` | side-goal (side-invariant lemma) |

The files compiled whole with `-timeout 10`. A second rule (one more step outwards, without
`d_State`) closed **no** more goal.

This is one step of symbol-based premise selection, as in SInE (Hoder, Voronkov) and Sledgehammer's
MePo filter: keep the facts that share a symbol with the goal.

## 2. What goes wrong

- The side invariant is one operator: `side_inv_<C> s = !abort => PkgInv_… s /\ … /\ links_<C> s /\
  GameInv_… s` (`invariant/side.rs`, `composition_items`). The solver gets all of it or none of it.
- All of it makes `smt` fail (story 92 §1.1). None of it leaves out the fact that the goal needs.
- The driver does not know which conjunct reads which table, and does not know the order of the
  conjuncts.

## 3. What to build

### 3.1 The conjuncts and their footprints (translation)

For each composition with side invariants, the translation gives the driver an ordered list:

```rust
pub struct SideConjunct {
    /// `Comp_<C>.GameInv_<N>_of_<C>`, `Comp_<C>.links_<C>`, `Comp_<C>.PkgInv_<N>_of_<C>_<I>`
    pub op: String,
    /// the module variables the conjunct reads, as goals print them (no memory)
    pub footprint: BTreeSet<String>,
}
```

- The order is the order of the conjuncts in `side_inv_<C>`. **One function** makes the list, and
  `composition_items` builds `side_inv_<C>` from it, so the two cannot get out of order. Without
  this, the `[#] _ g …` pattern of §3.2 opens the wrong conjuncts.
- The footprint of a game invariant comes from the state fields its translated body reads
  (`game_lookup` in `composition_items`). The footprint of a package invariant comes from the fields
  of its instance that the template reads. The footprint of the links comes from the fields that
  `links_body` reads.
- A field becomes the module variable that the precondition's record literal uses for it (the same
  function as `instance_state_lit` / `module_var` in `proof.rs`). Then the driver compares strings
  only and needs no name mapping.

`mod.rs` gives `Prover` the list for each composition in `drop_ops` (story 92), keyed by the
`side_inv` operator.

### 3.2 The invariant selection (driver)

A new fallback, **5**, directly after the pruned crush (`FALLBACKS` becomes 5). It uses the goal that
the pruned crush read (no new read sentence):

1. The conclusion's memories (`{1}`, `{2}`, `{hr}`) and its tables (the module variables of its
   projections).
2. For each `side_inv` premise whose record literal is in one of those memories: find the abort
   premise `!<theory>.Game_<C>.abort_flag{m}` of the same memory. Without it, skip this premise.
3. Select the conjuncts whose footprint meets the conclusion's tables. Without one, skip this
   premise.
4. Intro as the pruned crush does, but name the kept `side_inv` premise `hs<i>`, and add for each:
   `have := hs<i>; rewrite /<side_inv op> /= => /(_ h<abort>) [#] <g<i>_<j> or _ per conjunct>;
   clear hs<i>`.
5. `move: <kept, with the g's in place of hs>; rewrite <the selected ops> /=; smt().` One sentence;
   roll back on failure.
6. If no premise is kept (step 2 or 3 skipped all), send nothing and return `false`.

As in story 92, the sentence comes from a pure function, `selection_sentence(concl, drop_ops,
conjuncts) -> Option<String>`.

Role `SideGoalFallback(5)`; the live page shows `invariant selection`.

### 3.3 A risk to check

The prototype compared bare field names (`d_State`). §3.1 compares module variables, which is more
exact: if two instances of a composition have a field with the same name, the prototype kept both
and this story keeps one. If one of the 5 goals of §1.1 stays admitted for this reason, report it;
do not widen the match without a decision.

## 4. Rejected alternatives

- **Ask EasyCrypt for the conjuncts** (`rewrite /side_inv_C in hs.` with `Want::Full`). No new input,
  but this is the large formula that ADR 0012 avoids, and the driver must match formula text back to
  operator names.
- **A regex on the generated `Comp_<C>.ec`** (the prototype). A hidden coupling to the file text.
- **Selection, then one more step outwards (sel2).** One more `smt` timeout on each open goal; it
  closed nothing in the experiments.
- **A SInE-style tolerance or a ranking of conjuncts.** A knob we cannot set from data; the goals that
  remain need instances, not more facts (§8).
- **Selection last, after the old fallbacks.** The selection is a stronger pruned crush and uses the
  same goal read; directly after the pruned crush it needs no new read.

## 5. Tests first

- [ ] The conjunct list of a composition with links and two game invariants has the order of the
      `side_inv_<C>` body that `composition_items` writes (locks §3.1).
- [ ] The footprint of a game invariant that reads two tables of one instance holds the two module
      variables, as the precondition's record literal writes them.
- [ ] `selection_sentence`, a side goal over `&hr` with `!abort{hr}`, a `side_inv` premise and a
      conclusion that reads `d_Kmac`: the `[#]` pattern has one item per conjunct, `g…` exactly at
      the conjuncts whose footprint holds `d_Kmac`, and the `rewrite` unfolds just those.
- [ ] No abort premise → `None`. A conclusion without a table → `None`. No conjunct selected →
      `None`.
- [ ] A branch condition (`&1 &2`) whose conclusion reads only `{2}` keeps only the `side_inv` of
      `{2}`.
- [ ] Sequence: after a failed pruned crush, the selection sentence is sent with no new read; it
      closes → no admit; it fails → rolled back, then the admit.

## 6. Acceptance criteria

- [ ] All tests of §5 green; `cargo clippy` clean.
- [ ] The owner's check, the runs of story 92 §6 with this story: at most **14** `branch-condition` and
      `side-goal` admits together (19 after story 92).
- [ ] The 5 goals of §1.1 are closed by the invariant selection, or the report explains each miss from
      its transcript record (a timeout, a failure, or the risk of §3.3).
- [ ] No oracle has an admit it did not have after story 92.
- [ ] The report's per-hop table of story 92 §6 gets a row for fallback 5.
- [ ] Complexity **UNMEASURED** (no Rust recipe for `sdlc crap`); keep the logic in the pure functions.

## 7. Open questions

1. **Use the selection for leaf parts too?** Like story 92 §7 Q1: measure first.

## 8. Not in this story: the 14 goals that need instances

The 14 goals left need a conjunct **applied at a key that the goal does not show** (a tuple key of a
table, or a pair of sessions). Neither the pruned crush nor the selection gives such an instance.

| Goal | What it needs |
|---|---|
| `Eq_H2_1_H3_0_AtMost.ec:117` | `own_nonce_unique` for all 6 ordered session pairs (a hand proof in the style of story 86 §8 compiled on 2026-10-22) |
| `Eq_H6_1_0_H6_1_1_Reveal.ec:201`, `:205`; `SideInv_H6_Reveal.ec:223` | a `d_PRF` invariant at a pair key |
| `SideInv_H6_Test.ec:376` | `d_PRF` at a pair key is `None` |
| `Eq_H6_1_1_H7_0_AtLeast.ec:164` (branch) | `d_Fresh` at a key taken from `d_First` |
| `Eq_H6_1_1_H7_0_Reveal.ec:167`, `:230`, `:234` | `d_LTK <> None` at the session's key |
| `Eq_H6_1_1_H7_0_Send4.ec:586`, `:660` | negations of MAC equalities |
| `Eq_H7_1_1_0_H7_1_1_1_Send4.ec:315`, `:319`; `SideInv_H7_Send4.ec:290` | `d_First.[oget sid0] <> None` |

**Idea, not a story yet:** cvc5 already proved each of these claims. Its proof holds the
instantiations it used (cvc5's unsat-core manager collects the conclusions of its `INSTANTIATE` steps,
`getRelevantInstantiations`). Domino could turn them into `have := g <key>.` sentences, as story 86 §8
does by hand. Related work: Clune, Barbosa and Avigad (2026) use cvc5 hints and an unsat core to guide
Lean's automation. Open points: how the debugger keeps the instances, how a cvc5 term maps to an
EasyCrypt term, and whether the instances of a cvc5 refutation suffice for EasyCrypt's `smt`.
