# Story 111 — A Bits distribution is declared lossless

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** nothing.
**Blocks:** nothing. Story 112 is independent of this story.
**ADR:** none. The change is easy to undo. The rejected alternatives are in §6.
**Decisions:** owner's grilling session of 2026-11-14/15
(`program-mismatch_in_4WHS-mac_and_4WHS-prf-mac`), Questions 1, 1b, 4, 5, 6 and 7.

A **writer** story: `src/writers/easycrypt/typesfile.rs`, `src/writers/easycrypt/ast.rs`,
`src/writers/easycrypt/render.rs`, the golden `Types.ec` files and their tests. Test-first.

---

## 1. Why this story exists

At an **independent sampling** (a sampling on one side only), the prover sends:

```
seq 0 1 : (#pre); 1: auto => />.
```

(`sampling()` in `src/easycrypt/tactics/driver.rs`; `seq 1 0` for the left side.) The one-sided
`rnd{2}` in `auto` makes the side goal `is_lossless dbits_n`. No closer proves it: `auto => />` and
`auto` leave it open, and `auto => /#` fails. The step is rolled back, the blind walk finds nothing,
and the goal is admitted `program-mismatch`.

In the runs of 2026-10-30 (diagnosis of that day), this is the cause of these admits:

| Job | Project | Admits |
|---|---|---|
| hop 11 (`H6_1_1 ~ H7_0`), `Send2` | 4WHS-mac | N33 |
| hop 11, `Send3` | 4WHS-mac | N94 ×4, N181, N187, N192, N199 |
| hop 11, `Send2` | 4WHS-prf-mac | N33, N64 |
| hop 11, `Send3` | 4WHS-prf-mac | N61, N80, N99, N125, N213 ×4 |

A synchronized sampling (`seq 1 1`) does not need losslessness, because the two-sided `rnd`
couples the samplings. This is why the error occurs only where one side samples more often than
the other. In Full4WHS, this is only in the hops with `H7`, where `MAC.Init` samples a second time.

## 2. The facts this story uses

- **What the writer emits today.** `bits_type_items` (`typesfile.rs:108`) gives, for each bits type:

  ```
  op dbits_n : bits_n distr.

  axiom dbits_n_ll : is_lossless dbits_n.
  ```

  The axiom is a fact in scope. A tactic uses it only if the script names it
  (`rewrite dbits_n_ll`, `smt(dbits_n_ll)`).
- **How `rnd` closes a lossless goal.** `rnd` calls `t_solve ~bases:["random"] ~depth:2` on its side
  goal (EasyCrypt `src/phl/ecPhlRnd.ml:466`). It applies the lemmas of the hint base `random`. The
  standard library puts its own lossless lemmas into this base, for example
  `hint exact random : dunifin_ll dunifin_fu dunifin_funi.` (`theories/distributions/Distr.ec:925`).
- **What `op [lossless]` does.** For `op [lossless] d : t distr.`, EasyCrypt declares the axiom
  `d_ll : is_lossless d` (the name is `<op>_<suffix>`, `src/ecScope.ml:1474`; the suffix of
  `lossless` is `ll`, `ecScope.ml:1493`). It puts the axiom into the hint bases `lossless` and
  `random`. The name is therefore `dbits_n_ll`, the same as today.
- **Tested on 2026-11-14** (a small file with `seq 0 1 : (#pre); 1: auto => />.` over a one-sided
  sampling):

  | Declaration | Result |
  |---|---|
  | `op d : int distr. axiom d_ll : is_lossless d.` | fails: incomplete proof |
  | the same, plus `hint exact random : d_ll.` | closes |
  | `op [lossless] d : int distr.` | closes |

  The two forms that close also close when the declaration is in a separate theory that the
  proof loads with `require import`, as `Types.ec` is loaded.
- **Tested on 2026-10-30** at N33 of hop 11 `Send2` (4WHS-mac):
  `seq 0 1 : (#pre); 1: by auto => />; rewrite dbits_n_ll.` closes, and the next goal is the
  program goal that the joint tree expects.
- **Only Bits types are sampled.** `sample_distr` (`package.rs:907`) rejects every other type.
  `dbits*` are the only distributions in an export.
- **Golden files.** Seven files under `testdata/easycrypt/story0{2,3,4}/` hold
  `axiom …_ll : is_lossless …`. The golden tests in `typesfile.rs` (`*_types_file_matches_golden`)
  and the compile tests (`*_types_file_compiles`) read three of them.

## 3. What to build

1. **`EcItem::OpDecl` gets a list of tags** (`ast.rs:46`), for example `tags: Vec<String>`, empty by
   default. `render_item` (`render.rs:78`) prints `op [t1 t2] name : ty.` when the list is not
   empty, and `op name : ty.` as today when it is empty. Every other `OpDecl` (zero, one, the
   functions of `typesfile.rs:55`) has no tags and gives the same text as before.
2. **`bits_type_items`** emits the distribution as `op [lossless] dbits_n : bits_n distr.` and does
   not emit `EcItem::Axiom` for it. The doc comment of the function says why: EasyCrypt declares
   `dbits_n_ll` and puts it into the hint bases `random` and `lossless`, so `rnd` closes a
   one-sided lossless goal by itself.
3. **The prover does not change.** `sampling()` and `sampling_hoare()` keep their sentences.
4. **Docs.** `docs/easycrypt-export.md`: the section on `Types.ec` shows the new line.
   `docs/proving-algorithm.md` §9.2: in the row of `program-mismatch`, say that an independent
   sampling no longer gets it because of a lossless goal (story 111).

## 4. Tests first

- [ ] Unit test in `render.rs`: an `OpDecl` with the tag `lossless` renders as
      `op [lossless] dbits_n : bits_n distr.`, and an `OpDecl` with no tag renders as before.
- [ ] Unit test in `typesfile.rs`: `bits_type_items` for `Bits(n)` gives no `Axiom` item, and its
      distribution item has the tag `lossless`. The same for `Bits(*)` (`dbits`) and a numeric
      count (`dbits_256`).
- [ ] The seven golden `Types.ec` files are regenerated: the `op dbits…` line gets `[lossless]`,
      and the `axiom dbits…_ll` line goes away. Nothing else in them changes.
- [ ] The compile tests `*_types_file_compiles` stay green.
- [ ] A new compile test (fixture under `testdata/easycrypt/story111/`): a `Types.ec` as the writer
      emits it, and a second file that does `require import Types` and proves an `equiv` whose right
      side samples `dbits_n` once, with `seq 0 1 : (#pre); 1: auto => />.` It skips without
      `easycrypt`, as `assert_compiles` does.
- [ ] The existing full-tree compile tests stay green. A hand-written proof that names
      `dbits_n_ll` still finds it.

## 5. Acceptance criteria

- [ ] All tests of §4 green, with filtered test runs only. `cargo clippy` clean.
- [ ] Complexity: `bits_type_items`, `render_item` and every other touched function within budget
      (`.sdlc-workspace/crap-coverage.sh <filter>`).
- [ ] The proof runs: see §7. They run once, after Stories 111 and 112 are both merged.

## 6. Rejected alternatives

- **The prover names the axiom** (`seq 0 1 : (#pre); 1: by auto => />; rewrite dbits_n_ll.` in
  `sampling()`). The prover would then have to know how the writer names a distribution
  (`dbits_<suffix>_ll`) and which distribution the head samples. That is writer state leaking into
  the prover (change amplification and cognitive load). It also fixes only the call sites that the
  story edits. The blind walk, the side tree and the hand-written proofs stay without the fact.
- **The axiom, plus `hint exact random : dbits_n_ll.`** This works (§2), but it is two items where
  one is sufficient, and it puts the lemma only into `random`, not into `lossless`. The `lossless`
  base also lets `islossless` goals of procedures that sample `dbits_n` close by themselves.
- **A corrected fact.** During the grilling, the first reason against `op [lossless]` was "the lemma
  may not be called `dbits_n_ll`". That was wrong: `ecScope.ml:1474` names it `<op>_ll`.

## 7. The proof runs (after Stories 111 and 112)

The owner's decision (Questions 5 to 7): one run of each job, after both stories are merged, in
the `ec4whs` repository itself (`autogenerated/4WHS-mac` and `autogenerated/4WHS-prf-mac`), not on
a copy. The jobs run one at a time, in this order:

1. 4WHS-mac, hop 11 (`H6_1_1 ~ H7_0`), oracle `Send3`;
2. 4WHS-prf-mac, hop 11, oracle `Send3`;
3. 4WHS-mac, side-invariant job `SideInv_H7`, oracle `Send2`;
4. 4WHS-prf-mac, `SideInv_H7`, oracle `Send2`.

Before the jobs, the translation files are written again (`domino-ec easycrypt export --force`),
because `prove` never rewrites a translation file. Each job runs with `--force` and `--oracle`.

**The baseline** is the reports of 2026-10-30 in the same directories. No baseline run is made.
Stories 104 to 109 changed the prover after that date (for example, story 104 labels the case of
story 112 `seq-post`). The report says where these stories can explain a difference.

**The report** gives one table per job: the admits of the baseline and of the new run, per reason
and per claim, and the difference. It also lists the other admits that closed or opened. For
this story: no admit at an independent sampling with the reason `program-mismatch`. Node ids can
change, so the report finds these admits by their place (an independent sampling), not by their id.
If an admit of this cause stays, the report diagnoses it. It does not fix it in this story.
