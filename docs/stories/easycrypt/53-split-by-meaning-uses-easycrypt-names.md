# Story 53 — Splitting a leaf by meaning uses the names EasyCrypt knows

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 27 (tactic generation), 47 (`inv` guards only the invariant).
**Blocks:** nothing. It is independent of story 54. Do it first: it is small and it changes which
goals a tactics run can close.

A **Rust-only bug-fix** story. Translation does not change. The EasyCrypt fork does not change.

---

## 1. Why this story exists

The Full4WHS analysis (eighth design session, runs of 2026-10-03 and 2026-10-04) found two bugs.
Both make every split of a leaf by meaning fail before it starts. They are a large part of the
reason why the partial proofs admit goals: H2_1 ~ H3_0 has 24 admits, H4 ~ H5 has 19, and
H5 ~ H6_0 has 33.

**Bug 1 — the relation ops are unfolded under the wrong name.** The tactics run unfolds the
invariant in the premise with `rewrite /inv /params_inv /Domino_<relation> … in hpre`. It builds
the op names at `src/easycrypt/tactics/mod.rs:1621-1624`:

```rust
let unfold_ops: Vec<String> = ["inv".to_string(), "params_inv".to_string()]
    .into_iter()
    .chain(walked.relations.iter().map(|r| format!("Domino_{r}")))
    .collect();
```

`r` is the raw SMT name, for example `relation-keys-computed-correctly`. The writer names the op
with `mangle_smt_def_name` (`src/writers/easycrypt/invariant.rs:870`, called from
`OpRegistry::define` at about line 840). That function changes `-` to `_`, `=` to `_eq_`, and so
on. So the sentence contains `/Domino_relation-keys-computed-correctly`. EasyCrypt reads the `-`
as a minus sign, and the sentence is a parse error every time. `unfold_premise`
(`src/easycrypt/tactics/driver.rs:810`, the list is built at line 822) then falls back to
`rewrite /inv in hpre`, which leaves every relation folded. smt then sees an opaque op where it
needs the relation's body.

**Bug 2 — `move =>` drops the value binders.** `goals::as_forall`
(`src/easycrypt/tactics/goals.rs:89-100`) collects the names of a `forall` with:

```rust
.filter(|b| b.kind != "type")
```

The filter was meant to skip type binders. But EasyCrypt serializes a **value** binder
(`GTty`) with `"kind": "type"` (`easycrypt/src/ecPrinting.ml:4265`). So for a relation such as
`forall (ctr : int), …` the list is empty, and the driver sends `move => .`, which is a parse error.
This happens at `driver.rs:791` (`admit_ec_failed`), `driver.rs:837` (`unfold_premise`) and
`driver.rs:1493` (`solve_ambient`). Every claim of the form `forall …` fails its first step.

## 2. Inherited from earlier stories

- **Story 06:** every `define-state-relation` becomes `op Domino_<mangled> (l, r)`. The mangling
  rule lives in one place: `mangle_smt_def_name`. Its unit test is
  `mangle_smt_def_name_examples` (`invariant.rs:2222`).
- **Story 27:** `solve_ambient` splits a leaf's formula into its claims and labels each part by
  the op at its head. `unfold_ops` is passed to the driver as `Driver::unfold_ops`
  (`driver.rs:431`).
- **Story 47:** `inv` guards only `Domino_invariant`. Unfolding `Domino_invariant` exposes the
  relations it calls. Those relations are unfolded by their `Domino_` names, so the names must be
  right.
- **Story 52:** the fallback names (quick close, leaf fallback, part fallback) are the current
  names in code and on the page.

## 3. Work to do

- Make the writer's naming rule usable from the tactics module. Either make
  `mangle_smt_def_name` `pub(crate)`, or add a small `pub(crate) fn relation_op_name(raw: &str) ->
  String` beside it that returns `format!("Domino_{}", mangle_smt_def_name(raw))`, and use it in
  `OpRegistry::define` too. There must be **one** rule for the op name.
- Build `unfold_ops` at `tactics/mod.rs:1621` with that function.
- In `goals::as_forall`, remove the `kind != "type"` filter. Keep every binder's name. A `forall`
  in a goal of Domino's never binds a type, so nothing must be filtered.
- Check the name that `move =>` needs for a memory binder (`"kind": "mem"`). If the JSON name has
  no `&`, add it for that kind. Add a test for the case that you find.
- Update the doc comment of `as_forall` so that it says why no binder is skipped.
- **Leave alone:** the EasyCrypt fork (story 54 renames the binder kind to `"var"`; this fix does
  not depend on it), the fallback sequence, translation.

### Rejected alternatives

- **Read the op names from the goal** (walk the premise for ops that start with `Domino_`).
  Rejected: it puts a second source of truth beside the writer, and a folded op that the premise
  does not show at the top would still be missed.
- **Copy the mangling rule into the tactics module.** Rejected: two copies of one rule drift
  apart (change amplification). Bug 1 is exactly such a drift.
- **Keep the filter and test for `"mem"` and `"modty"` only.** Rejected: it still depends on the
  kind names that story 54 changes.

## 4. Acceptance criteria

- [ ] `unfold_ops` for relations named `relation-a-b` and `state=` gives `Domino_relation_a_b` and
      the name that `mangle_smt_def_name` gives for `state=`. A unit test covers both.
- [ ] The writer and the tactics run call the same function for the op name (grep: only one
      `format!("Domino_{}"` for relation ops).
- [ ] `as_forall` on `forall (ctr : int), P ctr` gives `["ctr"]`, and the driver sends
      `move => ctr.`. A unit test covers this, with the binder written as EasyCrypt writes it
      today (`"kind": "type"`).
- [ ] A memory binder gives a name that `move =>` accepts. A unit test covers this.
- [ ] A tactics run on `example-projects/4WHS` (theorem Full4WHS) proves the equivalences
      H0 ~ H1_0, H1_1 ~ H2_0 and H3_1 ~ H4_0 with no admits, as before.
- [ ] The implementation report gives the admit counts of H2_1 ~ H3_0, H4 ~ H5 and H5 ~ H6_0
      before (24 / 19 / 33) and after this story, and the number of `rewrite … in hpre` and
      `move =>` sentences that EasyCrypt refused, before and after.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt export --theorem Full4WHS --force
$D easycrypt prove --theorem Full4WHS --tactics
# no parse errors of this kind are left:
grep -c '"sentence":"rewrite /inv /params_inv /Domino_relation-' <out>/*/ec-transcript.jsonl   # 0
grep -c '"sentence":"move => \."' <out>/*/ec-transcript.jsonl                                   # 0
grep -c 'admit\.' <out>/*/Eq_H2_1_H3_0.ec <out>/*/Eq_H4_H5.ec <out>/*/Eq_H5_H6_0.ec
```
