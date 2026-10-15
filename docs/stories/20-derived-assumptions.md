# Story 20 — Derived assumptions: well-founded reduction checking

**Epic:** none (standalone). Not part of the `domino debug` epic in `00-overview.md`.
**Decision record:** `docs/adr/0001-derived-assumptions-fail-open-with-summary.md` — read it first.
**Glossary:** `CONTEXT.md` (Assumption, Base assumption, Derived assumption, Established,
Proposition, Conjecture). Use these words in code, comments and diagnostics.
**Depends on:** nothing. **Blocks:** nothing.

---

## 1. Why this story exists

A theorem can list a claim in `assumptions` and also prove it in `propositions`. The simple-binding
project (`~/simple-binding-example/theorem/Main.ssp`) does this for about 23 claims (`KSEarly`,
`KSLate`, `KEM`, `PRF_Check`, `PRF_Unique_Input_*`, …). Reductions cite these claims by name.

Today nothing connects a reduction's cited assumption to a proof of that assumption.
`Proof::try_new` (`src/proof.rs:55`) does a BFS over **all** game hops and never looks at which
assumption a reduction cites (`src/proof.rs` does not contain the word "assumption"). So a
proposition `KSEarly` whose path uses a reduction with `assumption KSEarly` is accepted. That is
circular reasoning, and the tool must reject it.

## 2. Settled decisions (do not relitigate)

| Topic | Decision |
|---|---|
| **Syntax** | `assumption_entry` gets an optional leading keyword `derived`: `derived KSEarly: KSEarly_0_0_0_0 ~ KSEarly_0_0_0_1`. No other grammar change. |
| **Default** | Unmarked = **base assumption** (trusted, same as today). Existing `.ssp` files do not change. |
| **Established** | Base assumptions are established. A `derived` assumption `A: G0 ~ G1` is established if there is a hop path from `G0` to `G1` whose reductions all cite assumptions established in an **earlier fixpoint round**. File order has no effect. |
| **Edges** | Equivalence and hybrid hops: always. Reductions: only if the cited assumption is established. Conjectures: allowed, but the result is "established modulo conjecture" and the conjectures are listed in the summary. |
| **Propositions** | Checked with the same edge filter, **after** the fixpoint, against the final established set. A proposition that repeats a derived assumption is allowed, with no warning. Names of propositions and assumptions are independent. |
| **Scope** | One theorem. Another theorem never establishes an assumption. |
| **When** | At load time, at the end of `handle_theorem` (`src/parser/theorem.rs`), after **all** blocks are parsed. This happens before any SMT work. |
| **Failure** | A hard load error. Report **all** unestablished derived assumptions and propositions in one diagnostic run, not only the first. Each one says either "no path" or names the cycle. |
| **Summary** | Always shown, no flag: `Main: proven relative to N base assumptions: …; M derived assumptions established (max depth d); modulo conjectures: …`. |

## 3. Algorithm

```
E      := { all base assumptions }           // round 0
depth  := { a -> 0 | a in E }
loop:
    changed := false
    for a in derived assumptions, a not in E:
        if path(a.left, a.right, edge allowed iff not reduction or cited(hop) in E):
            add a to E with depth = 1 + max depth of cited assumptions on the path
            changed := true
    if not changed: break
check every proposition with the same filter and the final E
for every derived a not in E (diagnostics only, never for acceptance):
    p := path(a.left, a.right, all reductions allowed)
    none  -> "no path between G0 and G1"
    some  -> edges a -> cited(r) for the unestablished reductions r on p;
             find the cycle with DFS / Tarjan SCC and print it with the reduction hops
```

Cost: at most k rounds × k searches, k ≈ 35 for Main. Graph work only, no solver calls. Do not
optimize past this until a measurement shows a need.

Important: newly established `a` in one round may enable others in the **same** round; that is fine
(the result is the same least fixpoint), but compute depth from the set at the moment of the search.

## 4. Where the code goes

- **Grammar:** `src/parser/ssp.pest:260` `assumption_entry` — add an optional `kw_derived`.
- **`Assumption`** (`src/gamehops/reduction.rs:36`): add the kind (base / derived). Parse it in
  `handle_assumptions` (`src/parser/theorem.rs:895`). Note that `handle_string_triplet` reads three
  identifiers; the keyword must be handled before it.
- **Path search:** give `Proof::try_new` an edge predicate (for example `impl Fn(&GameHop) -> bool`).
  Keep the **original** hop slice and indices so that `Proof::game_hops()` and the HTML writer
  (`src/writers/html.rs`) still show the right hops. Do not pass a filtered copy of the slice.
- **Fixpoint:** one new function in or next to `src/proof.rs`, called once at the end of
  `handle_theorem`. It owns the established set; nothing outside it needs to know about rounds.
- **Propositions:** `handle_propositions` (`src/parser/theorem.rs:929`) must only record the
  name and games. Move the path search to after the fixpoint. This also fixes a current bug:
  the grammar allows `propositions` before `gamehops` (`ssp.pest:254`), but then today every
  proposition fails as unproven because no hops are parsed yet.
- **Errors:** new diagnostics in `src/parser/error.rs` next to `UnprovenTheoremError` (`:502`),
  with spans on the assumption entry and on the reductions of a cycle. Collect them all, then
  return them together (miette `related`).
- **Summary:** printed at load time for each theorem. Find the existing UI that prints per-theorem
  lines (`src/project/mod.rs`, `crates/domino/src/ui.rs`) and add it there; it must not depend on
  `--theorem` / `--gamehop` selection to appear for the theorem being proven.

## 5. Tests (TDD — write each one red first)

Put parser-level tests with the existing theorem tests (`src/parser/tests/theorems.rs`,
`src/parser/tests/sound/theorems.rs`) and small fixtures in `testdata/` or `test-projects/`.

1. **Self cycle rejected:** `derived A: X0 ~ X1`, the only path from `X0` to `X1` uses a reduction
   citing `A`. Load fails; the error names `A`.
2. **Two-cycle rejected:** `derived A`, `derived B`, A's path needs B and B's path needs A. Both
   are reported, and the cycle `A → B → A` is printed.
3. **Chain accepted, any order:** base `P`; `derived B` uses `P`; `derived A` uses `B`. Write the
   hops and assumptions in reverse order in the file. Load succeeds; depths are A=2, B=1.
4. **No path:** `derived A` with no path at all → "no path" error, not a cycle error.
5. **All failures together:** two independent bad `derived` assumptions → both in one error.
6. **Proposition through an unestablished reduction rejected:** a proposition whose only path
   uses a reduction citing an unestablished `derived` assumption fails.
7. **Default unchanged:** an existing test project with no `derived` marks loads exactly as
   before, and the summary lists all its assumptions as base.
8. **Specialization:** `derived A: G_0 ~ G_b` (free const `b`) is **not** established by a hop
   that only holds for `b = 0`.
9. **Block order:** `propositions` before `gamehops` now works.
10. **Conjecture:** a derived assumption established through a conjecture is accepted and the
    summary lists the conjecture.

Then mark the derived assumptions in `~/simple-binding-example/theorem/Main.ssp` (the block at
`Main.ssp:2919`–`2946`, the ones the comments call "discharged") with `derived`, load the project,
and confirm the summary shows exactly the base assumptions at `Main.ssp:2898`–`2917`. Do not run
the full SMT proof for this check; loading is enough. Ask the owner before you commit to that
repository — it is not this repo.

## 6. Out of scope

- Establishing assumptions across theorem files.
- Changing the default to fail-closed (see the ADR).
- Any change to the per-hop structural reduction checks in `src/parser/reduction.rs` or to SMT.

## 7. Done when

- All tests in §5 pass; `cargo test` and `cargo clippy` are clean.
- `Main` from simple-binding loads with `derived` marks and prints the expected summary.
- An `-IMPLEMENTATION-REPORT.md` next to this file records what was done, deviations, and the
  summary output for `Main`.
