# Story 101 — Implementation report: a hand-written prototype fixes the new reduction layout

Prototype story. There is no Rust change. Branch `amir/easycrypt-export`, ADR 0023. The implementation is in commit `9d00cc70` and the review fixes are in `485745d8`.

## What was built

The new layout is under `testdata/easycrypt/reduction-prototype/layout/`. Each case has a router file, one file for each oracle, the joining file with the run lemma, and a small proposition file. No file has an `admit`.

- `kem-dem/`: the first reduction of kem-dem-cca-ssp.
  - `Prop_FirstReduction.ec` has one adversary with an empty suffix, a merged `equiv_<H> &m (key_idealization : bool)`, the bound lemma and the proposition lemma.
  - It has oracle lemmas for PKGEN, PKENC and PKDEC. PKGEN and PKENC have samplings.
- `hello-world/`: two compositions.
  - `run_<H>_L`/`_R`, and `equiv_<H>_L`/`_R` with literals.
  - Each oracle file holds both side lemmas, `Red_<H>_<O>_L` and `_R`.
- `reduction-consts/`: `B_mod_real_mod_ideal_b_false` and `_b_true`, each with its merged lemma over `ideal`.
  - The proposition `FlipBound` uses the hop twice, the second time in reverse, with an open hop in the middle.
- `compile.sh`: exports the fixture, replaces the `Red_*`/`Prop_*` files, and compiles every prototype file on its own.
- `blind_walk.py`: a throwaway Python version of the blind walk (§7.4 of `proving-algorithm.md`) over `easycrypt cli -json`. It wrote every oracle proof. No test uses it.

The note `docs/research/reduction-proof-script.md` has a new section 8, and a banner says that section 8 replaces sections 3–5 for this layout. Section 8 gives:
- the script of each lemma kind;
- the answer to the leaf question;
- the differences from the walk;
- the missing two-argument case.

## Findings for stories 102 and 103

1. **Leaf:** `auto => /#` is enough everywhere: quick closes, side goals, leaves, and the `by auto => /#` after `call (run A)`. `inv_<H>` is never unfolded.
2. **The quick close shortens the walk a lot.** reduction-consts `Query`, kem-dem `PKDEC` and hello-world `UselessOracle` close with a single `auto => /#.` after `proc; inline *.`. PKGEN takes 15 lines and PKENC 34.
   - `seq 1 1` at a sampling was needed only once (PKENC).
   - `if{i}`, `seq 1 0` and `seq 0 1` were never needed.
   - The walk never admitted a goal.
3. **`inline *` inlines the mapped packages too.** Story 97 needed an exclusion list; this walk does not.
4. **`sp k` goes through an `if` when `k` is larger than the number of leading assignments.** The counts must be read from the goal.
5. **`require` does not check a required file's proofs again.** Compile tests must compile every `Red_*`/`Prop_*` file on its own. I checked this: a broken oracle file passed when only the `Prop` file was compiled.
6. **Two differing assumption arguments:** no fixture has one, 4WHS included. The note records this.

## Decisions and deviations

- **Names:** oracle file `Red_<H>_<O>.ec`, lemma `Red_<H>_<O>[_L|_R]`, `run_<H>[_L|_R]`, `equiv_<H><s>[_L|_R]`, `bound_<H><s>`. With two sides, both lemmas of an oracle go in one file.
- **Merged binder name:** the game's `run` parameter at the position that differs.
- **Restrictions in the proposition file:** they use the prefix `Red_<H>_Router.`, not `Red_<H>.` as story §2 says, because the router now has its own file.
- **The story 97 prototypes stay in place**, because `reduction_prototypes_compile` reads them. Story 102 should replace them with `layout/`.
- **§3 says the new section "replaces §5".** I read this as replacing §3–§5, the sections about the old layout.

## Tests run

All runs were under `systemd-run --user --scope -p MemoryMax=6G timeout`, with EasyCrypt r2026.09 and no proving job running.

| Command | Result |
|---|---|
| `layout/compile.sh target/debug/domino <project> <theorem> layout/<case>`, for each of the 3 cases | all files compile (kem-dem 29 s, hello-world 5 s, reduction-consts 4 s) |
| a broken copy of the kem-dem PKENC file | rejected |
| a broken copy of the reduction-consts proposition file | rejected |
| `blind_walk.py` on each oracle | 0 admits |

No cargo command was run, because no Rust changed.

## Open for story 102

- Update `reduction_prototypes_compile` so that it uses `layout/` and compiles each file.
- Decide whether to keep or delete `blind_walk.py` once story 103's walk exists.
