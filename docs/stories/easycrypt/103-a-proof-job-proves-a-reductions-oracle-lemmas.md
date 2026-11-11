# Story 103 — A proof job proves a reduction's oracle lemmas

**Epic:** EasyCrypt export: reductions without an experiment —
`docs/stories/easycrypt/epic-reductions-without-an-experiment.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 102 (the oracle files).
**Blocks:** —
**ADR:** `docs/adr/0023-a-proposition-owns-its-reduction-adversaries.md` (decisions 5 and 7).
**Decisions:** owner's grilling session of 2026-11-10/11, Decisions 3 and 7.

A **prover** story: `src/easycrypt/tactics/` (job kind, driver), the export's placeholders and
overwrite guard, the CLI help, and tests. Test-first.

---

## 1. Why this story exists

After story 102, each `Red_<L>_<R>_<O>.ec` holds a generated tactic ladder: about 50 long lines
that try every tactic. Nobody can read it. The blind walk of the proving algorithm reads the goals
from EasyCrypt and writes one line for each program step, as the `_Lotta` proofs do. The grilling
showed by hand that these steps close a reduction oracle lemma.

## 2. The facts this story uses

- `prove_blind` (`src/easycrypt/tactics/driver.rs`): at each program head it runs `sp_front`
  (`sp k l` with counts from the goal), the quick close `auto => /#`, then the trials `rcondt{i}` and
  `rcondf{i} ^if; 1: auto => /#.`, `if.`, `if{1}.`/`if{2}.`, and `seq` at samplings. It admits
  `program-mismatch` when nothing applies. It works without a joint tree.
- `leaf_of` with `pair: None`: `decide_exit_path`, `reduce_leaf`, then `open_part`, which unfolds
  the invariant operator and splits it into conjuncts. A conjunct that fails is admitted with a
  reason.
- `JobKind` (`src/easycrypt/tactics/mod.rs`) has `Equivalence`, `SideInvariants` and
  `PackageInvariants`.
- `EcProve` (`crates/domino/src/cli.rs`): `--gamehop`, `--oracle`, `--jobs`, the fresh start and
  resume. Records are in `session/<stem>/`, pages in `progress/<stem>/`. An equivalence waits for
  its side-invariant files.
- ADR 0006: a proof job never translates. ADR 0018: invariant operator names come from a name rule.
- The export's overwrite guard (`src/writers/easycrypt/overwrite.rs`) reports proof progress only
  for `Eq_*.ec` files.
- The research note of story 101: the script of a reduction oracle lemma and what the leaf needs.

## 3. What to build

1. **Export:** each `Red_<L>_<R>_<O>.ec` gets the same placeholder as an equivalence oracle file
   (an `admit` after the prelude) instead of the ladder. Remove `oracle_proof` and the ladder code.
   The run lemma, the `equiv`, `bound` and proposition lemmas stay complete.
2. **A new job kind** `JobKind::Reduction`: for each oracle, the prelude `proc; inline *.` (or what
   story 101 found), then `prove_blind` from the root, with the walk's leaf step. No lockstep
   execution, no solver, no side-invariant files. The job finds `inv_<L>_<R>` (or `_L`/`_R`) from
   the stem by the name rule.
3. **Selection:** a reduction hop is a game hop. `--gamehop N` selects it. Without `--gamehop`,
   `prove` runs it in order with the other hops. `--oracle`, `--jobs`, resume and the fresh start
   work as they do for equivalences, with `session/Red_<L>_<R>/` and `progress/Red_<L>_<R>/`. Update
   the CLI help, which today says "each oracle of an equivalence".
4. **Failures** give named `admit`s: `program-mismatch` for a step that nothing closes, or the
   failed conjunct at a leaf. A loop in a package stops the walk with `program-mismatch`.
5. **The overwrite guard** (ADR 0004) also reports proof progress for `Red_*` oracle files.
6. **Report:** the reduction entry's `admit` count is one for each oracle after `export`.
7. **Docs:** `docs/proving-algorithm.md` (the table row that says reduction lemmas are
   "Translation; no admit") and `docs/easycrypt-export.md`.

## 4. Tests first

- [ ] Unit test: after `export`, each `Red_*_<O>.ec` of kem-dem-cca-ssp has the placeholder and no
      ladder; `Red_<L>_<R>.ec` and `Prop_*.ec` have no `admit`.
- [ ] Unit test: `--gamehop N` on a reduction hop selects `JobKind::Reduction` and does not wait for
      side-invariant files.
- [ ] Unit test: the overwrite guard lists a proved `Red_*_<O>.ec` with its progress.
- [ ] Live test (needs `DOMINO_EASYCRYPT`): `prove --gamehop <hop>` on `reduction-consts` closes the
      oracle lemma with no `admit`. The proof has only `sp`, `if`, `rcondt`/`rcondf`, `seq` and
      `auto` steps, and the whole tree then compiles.
- [ ] Live test: `prove` on the first kem-dem-cca-ssp reduction, with `--oracle` on one oracle,
      closes it with no `admit`. Small fixture only.
- [ ] Unit test: resume skips an oracle that its session record holds as proved.

## 5. Rejected alternatives

From the grilling of 2026-11-10/11 (ADR 0023):

- **Translation writes the walk itself.** It must predict EasyCrypt's inlining, positions and names
  (ADR 0002). A bare `sp` goes through `if`s, so the counts are necessary.
- **Keep the ladder and make it shorter.** Still a blind search, and not readable.
- **Full lockstep execution.** It needs a synthetic right composition and an SMT invariant, and the
  assumption game's abort guards break the alignment.
- **A separate `--reduction` flag.** A second way to select work, and propositions keep `admit`s
  with no hint why.
- **Prove the oracles inside `export`.** ADR 0006: a proof job never translates, and `export` runs
  no EasyCrypt.

## 6. Acceptance criteria

- [ ] All tests of §4 green, with filtered test runs only. `cargo clippy` clean.
- [ ] Complexity: every touched function within budget (`.sdlc-workspace/crap-coverage.sh <filter>`).
- [ ] No `prove` run on a 4WHS-size project.
