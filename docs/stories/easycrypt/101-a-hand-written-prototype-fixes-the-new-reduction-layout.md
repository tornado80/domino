# Story 101 — A hand-written prototype fixes the new reduction layout

**Epic:** EasyCrypt export: reductions without an experiment —
`docs/stories/easycrypt/epic-reductions-without-an-experiment.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** —
**Blocks:** 102.
**ADR:** `docs/adr/0023-a-proposition-owns-its-reduction-adversaries.md`.
**Decisions:** owner's grilling session of 2026-11-10/11, Decisions 1–6.

A **prototype** story: hand-written EasyCrypt under `testdata/easycrypt/reduction-prototype/` and a
research note. No Rust change.

---

## 1. Why this story exists

Story 102 generates the new layout, and story 103 generates the oracle proofs. Both must generate a
script that EasyCrypt accepts. The grilling compiled the shape only on `reduction-consts`, with one
Boolean binder and one oracle that has no sampling. Before translation generates it, a hand-written
prototype must compile on the fixtures that have the other cases.

## 2. The facts this story uses

- The probe of the grilling (`reduction-consts`, one oracle) compiled with:
  - a router file with no `B`, no `RedExp` and no conjunct C3;
  - `run_<L>_<R>` proved by `proc (inv_<L>_<R> ..) => //.` and `by conseq <oracle lemma> => /#.`;
  - in the proposition file, `B_<L>_<R>_b_false (A) (O)` that calls `Red_<L>_<R>(O).init(false)`
    and runs `A(Red_<L>_<R>(O))`, then a merged lemma over `(ideal : bool)` proved by
    `byequiv (: ={glob A} /\ arg{1} = (false, ideal) /\ arg{2} = ideal ==> ={res}) => //.`,
    `proc; inline *; wp.`, `call (<run lemma> A).`, `by auto => /#.`, and a bound lemma proved by
    `by rewrite !(<equiv> &m).`;
  - the oracle lemma proved after `proc; inline *.` by `sp k l`, `if`, `rcondt{i} ^if` and
    `rcondf{i} ^if` steps, each side goal closed by `auto => /#`, with leaves closed by `auto => /#`.
- A bare `sp` goes through `if` statements. The walk needs the counts `sp k l`, which only
  EasyCrypt's goal shows.
- The proposition file's adversary restrictions name modules with their file prefix
  (`Red_<L>_<R>.Red_<L>_<R>`). It does not need `-B_..`.
- The `_Lotta` files in Full4WHS have the same tactic shapes, with `seq 1 1 : (#pre /\ x{1} = y{2})`
  at samplings.

## 3. What to build

Hand-write the new layout for each case and compile it:

1. **kem-dem-cca-ssp, first reduction** (literal constants, same compositions on both sides): one
   adversary with an empty suffix, a merged `equiv` lemma, oracle lemmas with samplings.
2. **hello-world** (two different assumption compositions): `run_<L>_<R>_L` and `_R`, and `_L` and
   `_R` equivalence lemmas with literals, because the merge rule does not apply. hello-world has no
   proposition: write a small proposition file for the prototype only, or add one to a copy of the
   fixture.
3. **reduction-consts** with a proposition path that fixes `b`: two adversaries `_b_false` and
   `_b_true`, each with its merged lemma.
4. If a fixture has a hop with two differing assumption arguments, prototype the merge with two
   binders. If none has one, record this in the note.

Write each oracle proof as the blind walk would write it: `proc; inline *.`, then only the walk's
steps, in the walk's order of trial (`rcondt{1}`, `rcondf{1}`, `rcondt{2}`, `rcondf{2}`, `if`,
`if{1}`, `if{2}`, `seq` at samplings). Record each case where the walk's step does not close a goal,
and what closes it.

Record in `docs/research/reduction-proof-script.md` (a new section that replaces §5 for this layout):

- the script of each lemma kind, as story 102 and story 103 will generate it;
- what the walk's leaf must do with `inv_<L>_<R>` (is `auto => /#` enough, or must it unfold the
  operator first?);
- every place where a hand-written step differs from the walk.

## 4. Tests first

- [ ] Each prototype directory compiles with `easycrypt compile`, with no `admit` (by hand; the
      compile tests of story 102 take over).
- [ ] The note lists each lemma kind with its script.

## 5. Rejected alternatives

- **No prototype; generate directly.** Story 97 showed that a hand-written proof finds the script's
  problems sooner and cheaper than generated code.

## 6. Acceptance criteria

- [ ] The three cases of §3 compile.
- [ ] The note answers the leaf question and lists every difference from the walk.
