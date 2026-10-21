# Story 88 — A goal formula keeps every sub-formula

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 27 (reading goals from EasyCrypt's JSON), 61 (`head` and `full` answers), 66 (the
key case split).
**Blocks:** 89 (the case split keeps the cases it closes), which only pays off once the split
reaches the side invariants.
**ADR:** none (ADR 0009 and ADR 0012 do not change: the answers stay as they are, Domino reads
more of them).
**Decisions:** owner's request of 2026-10-22: "write a separate story for the JSON parser gap".
Open questions in §7. §3 uses the recommended answers.

A **tactics** story, Rust only. Test-first.

---

## 1. Why this story exists

In the `ec4whs` runs of 2026-10-21 (commit `952a168`), part fallback 4 (the key case split, story
66) never runs in a side-invariant lemma. 108 parts fail fallbacks 1–3 there (SideInv_H2 14,
SideInv_H6 86, SideInv_H7 8) and none gets a `case`. Yet their goals have exactly the shape story 66
splits on. An admitted part of SideInv_H6 Send3 (J1, `GameInv_stuff__not__initialized__early_of_H6`):

```
(oget Comp_H6.Cloned_Pkg_KX.KX_noprfkey.d_State{hr}.[ctr0{hr} <- state{hr}].[ctr1]).`7 <> None<:bits_n>
```

`ctr1` is a binder the leaf procedure introduced (`move => ctr1 /=.`), and `d_State{hr}.[ctr0{hr}
<- state{hr}]` is an updated map with an atom key. `goals::key_pairs` should return `(ctr1,
ctr0{hr})`. It returns nothing, so `key_case_split` returns `false` without sending anything, and
the transcript shows no attempt.

In the hops the split does run (12 times, all `StateRelation_relation_state_equality` in Send3 of
H5 ~ H6_0 and H6_1_1 ~ H7_0). There the read is at the top of the conclusion:
`d_State{2}.[ctr0{2} <- state{2}].[ctr1] = d_State{1}.[ctr0{1} <- state{1}].[ctr1]`.

## 2. What goes wrong

EasyCrypt's JSON (`easycrypt/src/ecPrinting.ml`, `jform_node`, line 4283; the schema is
`easycrypt/doc/json-output.md`, "Kinds") puts the sub-formulas of a node in fields named after the
kind:

| kind | sub-formula fields |
|---|---|
| `app` | `head`, `args` |
| `quant` | `body` |
| `tuple` | `items` |
| `proj` | `arg` |
| `if` | `cond`, `then`, `else` |
| `match` | `scrutinee`, `branches` |
| `let` | `bound`, `body` |
| `pr` | `args`, `event` |
| `hoareS` … `equivF` | `pre`, `post`; phoare also `bd`; hoare also `exn` |

Domino's `Form` (`src/easycrypt/json.rs`) has only `head`, `args`, `body`, `pre` and `post`. serde
drops every other field without a word. A `proj`, `tuple`, `if` or `match` node arrives with no
children, a `let` without its bound term, a `pr` without its event.

The two tree walks of `goals.rs` therefore stop at those nodes:

- `collect_key_pairs` (`key_pairs`, part fallback 4). Every state field the game invariants talk
  about is a projection `(oget State.[ctr1]).`k`, so the read under it is never seen; the
  `d_Fresh{hr}.[ctr1]` of `GameInv_kmac__is__wellformed_of_H6` sits under an `if`.
- `mentions_op` (`unfold_premise`): an `inv` under a `let`, `if`, `match` or tuple is not seen.
  Today `inv` sits under a `/\` chain, which is read, so this has not shown up yet. Story 86's
  `may_mention_op` would inherit the same blind spot.

Nothing fails loudly: a walk that finds nothing reads as "no key pair" or "no `inv`".

## 3. Work to do

### 3.1 `Form` reads every sub-formula

Add to `Form`, all `#[serde(default)]`:

```rust
/// `proj`: the tuple projected, and the index.
pub arg: Option<Box<Form>>,
pub index: Option<usize>,
/// `tuple`.
pub items: Vec<Form>,
/// `if`.
pub cond: Option<Box<Form>>,
#[serde(rename = "then")]
pub then_form: Option<Box<Form>>,
#[serde(rename = "else")]
pub else_form: Option<Box<Form>>,
/// `match`.
pub scrutinee: Option<Box<Form>>,
pub branches: Vec<Form>,
/// `let`: the bound term (the body is `body`).
pub bound: Option<Box<Form>>,
/// `pr`: the event.
pub event: Option<Box<Form>>,
/// `phoareS`, `phoareF`: the bound.
pub bd: Option<Box<Form>>,
```

`exn` (a list of `{exn, form}`) stays unread: no walk needs the exception postconditions of a
hoare goal, and Domino's goals have none.

Update the `Form` doc comment: which fields each kind fills, with a pointer to `json-output.md`.

### 3.2 One list of children

Add `Form::children(&self) -> impl Iterator<Item = &Form>`, the sub-formulas in the order of the
schema (`head`, `args`, `items`, `arg`, `cond`, `then`, `else`, `scrutinee`, `branches`, `bound`,
`body`, `event`, `bd`, `pre`, `post`). `mentions_op` and `collect_key_pairs` use it instead of their
own `head … post` chains, so a walk cannot miss a field again. Story 86's `may_mention_op` uses it
too.

### 3.3 A schema check

A test that parses a recorded `full` answer containing each of `proj`, `tuple`, `if`, `match` and
`let` (§5) and checks, for each node, that the number of children `Form::children` gives equals the
number of formula-valued fields in the raw JSON (the walk of `easycrypt/tests/json/check.py`'s
`nodes`: every object with a `kind`). A field EasyCrypt adds later then fails this test instead of
being dropped.

## 4. Rejected alternatives

- **A generic `serde_json::Value` walk.** Robust to new fields, but every reader of `Form` today
  uses typed fields (`op`, `args`, `binders`), and the type table (`ty`) would have to be handled
  apart. The schema check of §3.3 gives the same safety.
- **`#[serde(deny_unknown_fields)]` on `Form`.** Catches new fields, but it also fails on fields no
  walk needs (`ident`, `tyargs`, `mem_ident`, `pattern`, `exn`), so every answer would need them all
  modelled.
- **Search the `pp` text.** Only the root formula has `pp` (`json.rs`), and text matching is what
  story 27 replaced.

## 5. Tests first

- [ ] Red: `goals::key_pairs` on the conclusion above, built with the helpers of the existing
      `key_pairs` tests plus a `proj` node (`{"kind":"proj","arg":…,"index":7}`) around an `oget`
      of the read, finds `(ctr1, ctr0{hr})`. Today: empty.
- [ ] Red: the same read under an `if` (`cond`), a tuple (`items`), a `let` (`bound`) and a `match`
      (`scrutinee`): one pair each.
- [ ] Red: `mentions_op(f, "inv")` with `inv` under `let`, `if`, `match`, `proj`, `tuple`: `true`.
- [ ] A stub `proj` (a `head` answer past depth 4) has no children; `key_pairs` and `mentions_op` treat
      it as today (story 86 §3.2 handles the "maybe").
- [ ] §3.3: a recorded `full` answer (new fixture under `testdata/easycrypt/story88/`, made with
      `easycrypt llm` on a lemma whose goal has each kind) parses with `children` matching the raw
      count on every node.
- [ ] Existing `goals.rs` and `tests.rs` tests stay green.

## 6. Acceptance criteria

- [ ] All tests of §5 green; `cargo clippy` clean.
- [ ] `ec4whs`: `domino-ec easycrypt prove --project 4WHS --out autogenerated --theorem Full4WHS
      --side-inv H6 --force` (the job with 86 of the 108 parts). In its transcripts, part fallback 4
      sends `case (ctr1 = ctr0{hr}) => [->|?].` on the parts of §1. Report how many parts it closes
      and the change in the job's EasyCrypt time; with today's split (stop at the first failing
      case, story 66) each attempt costs one `case` and at most one `smt`.
- [ ] The same for `--side-inv H2` and `--side-inv H7`, and for proofsteps 8 (H5 ~ H6_0) and 11
      (H6_1_1 ~ H7_0), whose parts with reads under projections get the split too.
- [ ] `Proof_Statistics.md` in `ec4whs` gets the new part fallback 4 row.

## 7. Open questions

1. **Read `exn`?** Recommended: no (§3.1). Domino never writes exceptions.
2. **Keep `MAX_KEY_PAIRS` at 6?** More reads are visible now, so a conclusion can have more pairs.
   Recommended: keep 6 and report in §6 how many parts were skipped for having more.
