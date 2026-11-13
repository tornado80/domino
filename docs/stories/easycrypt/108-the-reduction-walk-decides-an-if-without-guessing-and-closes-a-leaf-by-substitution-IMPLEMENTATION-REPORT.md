# Story 108: implementation report. The reduction walk decides an `if` without guessing and closes a leaf by substitution

A prover story on branch `amir/easycrypt-export`, under ADR 0024. Commits: `b42703aa` (the
implementation) and `7e58dcf2` (the review fixes).

## Result

`Send2` and `Send4` of hop 12 (`Red_H7_1_H7_0`) close with **no admit**. Each needs less than
half of story 107's EasyCrypt time:

| Oracle | Story 107 EC time | Story 108 EC time | Change | Goals 107 → 108 | Undone 107 → 108 | Admits |
|---|---:|---:|---:|---:|---:|---|
| Send2 | 1132.3 s | **536.5 s** | −53 % | 234 → 94 | 433 → 223 | 0 → 0 |
| Send4 | 1899.6 s | **842.2 s** | −56 % | 439 → 167 | 674 → 316 | 0 → 0 |

The target was half or less (566 s and 950 s), and both oracles meet it. **These runs were made
under load.** The owner's `prove --theorem Full4WHS --game H7 --jobs 12`, a side-invariant job
with several `easycrypt cli` processes, ran on the same machine for the whole of both runs, as
the owner asked. Story 107's runs used `--jobs 3`, which also put other EasyCrypt processes on
the machine, so the two sets of numbers are comparable but not exact.

## What was built

- **The `decide` order** (`reduction_walk.rs`, `decision_order`): `/>` in both directions
  before any `/#`. The first direction is the one `exit_decisions` predicts. A sentence counts
  only when its side goal is closed, as before.
- **The right exit guard repeats the left decision.** After side 1 is decided with `d`, side 2
  tries `d` with `/>` and then `/#`, and the other direction only after both fail
  (`following`). If either side is undecided, both are rolled back and the walk goes to `if.`,
  as before.
- **The tail branch** uses the order of item 1 on side 2, then the `rcondt{2} ^if.` step as
  before.
- **No `sp` before classifying.** `classify` and `head_cond` read each program after its
  leading assignments (`from_head`). `walk` no longer sends `sp`. `sp k l.` is sent only in
  `branches` (before `if.`) and in `samplings` (before story 104's `#pre` check and
  `seq 1 1`). An `rcond` goes out with no `sp` in front of it. A non-program front goal is
  admitted as a mismatch with the claim `not-a-program` (it was `sp` before).
- **Substitution on a reduction leaf** (`driver.rs`, `substitute_premise`): after `auto => &1
  &2 hpre.` and the unfolding of the invariant, `move: hpre => />.` is sent. It is kept when it
  closes the goal or leaves one ambient goal; then the leaf has no named premise left
  (`premises` is empty), and `open_part` opens what remains. If it is refused, or splits the
  goal into several, it is undone and the leaf goes on with `hpre`. The guard is
  `judgement == Judgement::Reduction`: equivalence, side-invariant and package-invariant
  leaves send nothing new.
- **Docs:** `docs/proving-algorithm.md` §6.2 gets the substitution line, and §10.1 and §10.2
  describe the order, the repeated decision, the heads read after assignments, and `sp` only
  before `if.` and `seq`.

## Decisions and deviations

- **"No failed `rcond… /#.`" (§4) is tested as "no wrong guess".** In `reduction-two-calls`,
  one pair of exit guards is a real decision. Both `rcondf{1} … /#` and `rcondt{1} … /#` fail
  there, and the walk splits it with `if.`. That is two failures, about 9 s, and no guess can
  avoid them. So the live test asserts that no failed `rcond… /#.` is directly followed by an
  accepted one, which is the wrong-guess pattern of §2. Hop 12 shows the same thing: 2 failed
  `/#` sentences per oracle, down from 76 (`Send2`) and 85 (`Send4`).
- **The leaf's `move: hpre => />.` is checked with the quick close turned off.** In
  `reduction-two-calls`, the quick close closes every leaf. A second run in the same test, with
  `quick_close: false`, sends every leaf through the leaf procedure. It asserts the
  substitution, 0 admits, and that the file compiles.
- **The test `other_heads_are_a_mismatch_with_both_kinds` changed** from `call/asgn` to
  `none/call`. An assignment is no longer a head, so the old case cannot occur.
- **A `/>` that splits the goal is undone.** It is not followed with bullets, which keeps the
  leaf code unchanged. On hop 12 every accepted substitution left at most one goal.
- **Not re-exported.** The story changes only the prover, so the acceptance run used a copy of
  the existing `Full4WHS` translation in the scratchpad, as the coordinator instructed. The
  owner's `ec4whs` tree was not touched.

## Tests run

| What | Command | Result |
|---|---|---|
| Walk unit tests: order, repeated decision, heads after assignments | `cargo test -p sspverif --lib reduction_walk` | 21 passed |
| Fake-EasyCrypt prover tests, including the new leaf test (Equiv sends no `move: hpre => />.`, Reduction does) | `cargo test -p sspverif --lib easycrypt::tactics::tests -- --skip reduction_jobs` | 138 passed |
| Leaf and lockstep equivalence tests | `cargo test -p sspverif --lib` with filters `tactics::tests::the_leaf`, `the_exit_path`, `leaf_`, `lockstep` | 2 / 1 / 6 / 22 passed |
| `reduction` filter | `cargo test -p sspverif --lib reduction -- --test-threads=1` | 62 passed (the one failure in that run was the first draft of the new leaf test, fixed and re-run green) |
| Live: `reduction-two-calls` | `DOMINO_EASYCRYPT=… systemd-run --user --scope -p MemoryMax=6G timeout 1200 cargo test -p sspverif --lib prove_closes_the_reduction_two_calls` | ok: 0 admits, no `sp` directly before an `rcond`, no wrong guess, `move: hpre => />.` in the no-quick-close run |
| Live: `reduction-consts` | same, with `prove_closes_the_reduction_consts` | ok, 0 admits |
| Live: story 106 mismatch | same, with `an_extra_if_on_the_left` | ok, exactly one `left-only-if` |
| Clippy | `cargo clippy -j 2 --workspace --all-targets` | clean |
| Hop 12, `Send2` / `Send4` | `systemd-run --user --scope -p MemoryMax=8G timeout 3h target/release/domino easycrypt --project …/ec4whs/4WHS --out <scratch>/full-copy prove --theorem Full4WHS --gamehop 12 --oracle <O> -f --progress plain` | 0 admits, 536.5 s and 842.2 s |

## Time by category (hop 12, from `progress/Red_H7_1_H7_0/<O>/ec-transcript.jsonl`)

The time is the sum of `ms` per sentence. In the table, "smt" means `smt…` sentences outside
the `structure` role, and "quick close" means `auto => /#.`.

| What | Send2 (107) | Send2 (108) | Send4 (107) | Send4 (108) |
|---|---|---|---|---|
| leaf-part `smt` that succeeds | 176 / 493 s | 32 / 62 s | 308 / 902 s | 28 / 46 s |
| leaf-part `smt` that fails (part fallback follows) | — | 24 / 115 s | — | 46 / 195 s |
| part fallback (other sentences) | — | 10 / 26 s | — | 23 / 45 s |
| `move: hpre => />.` | — | 20 / 11 s | — | 15 / 13 s |
| `rcond… /#` that fails | 76 / 349 s | 2 / 10 s | 85 / 377 s | 2 / 9 s |
| `rcond… /#` that succeeds | 20 / 39 s | 0 | 18 / 32 s | 0 |
| `rcond… />` (kept or undone) | 258 / 45 s | 246 / 52 s | 405 / 83 s | 351 / 72 s |
| quick close, interrupted or failed | 55 / 69 s | 69 / 100 s | 134 / 268 s | 121 / 242 s |
| quick close that closed | 49 / 79 s | 37 / 97 s | 99 / 132 s | 88 / 138 s |
| `sp` | 129 / 15 s | 20 / 6 s | 197 / 21 s | 30 / 6 s |
| `pragma` | 262 / 23 s | 122 / 16 s | 481 / 43 s | 206 / 23 s |
| undo (count) | 125 | 85 | 146 | 95 |
| **Total** | 1130 s | 537 s | 1895 s | 840 s |

What the table shows:

- **The wrong guesses are gone.** Failed `/#` time went from 349 s and 377 s to about 10 s each.
  What is left is one real decision per oracle.
- **The leaf parts went from about 500 s and 900 s of `smt` to under 200 s and 300 s.** Most
  leaves now have one part after the substitution. But that part often fails plain `smt().`
  (24 and 46 failures, about 4.5 s each) before a part fallback closes it. This is now the
  largest remaining cost after the quick close.
- **The quick close is now the largest category** (169 s and 380 s). The story kept its 2 s
  timeout unchanged (item 9), and the machine was loaded.
- `sp` fell from 129 and 197 sentences to 20 and 30.

## Written, not run

- The CRAP gate (`.sdlc-workspace/crap-coverage.sh`) collected coverage, but `sdlc crap` and
  `sdlc crap gate` failed in this sandbox with `bwrap: loopback: Failed RTM_NEWADDR: Operation not
  permitted` (the known AppArmor issue). So the complexity box of §5 stays open. Every new or
  changed function is small: `decision_order`, `following`, `decide`, `exit_guards`, `from_head`
  and `substitute_premise` each have one or two branches.
- The other 10 oracles of hop 12 were not re-run, per the rule against proving whole big hops.

## For the owner

1. **The part that remains after `move: hpre => />.` often fails plain `smt().`**, then a part
   fallback closes it. Two options: start the remaining part with the fallback that closes it
   (from the transcripts this looks like the hint `smt(…)` or the crush), or skip the plain
   `smt().` on a reduction leaf. Either would save about 100 to 200 s per oracle.
2. **The quick close's 2 s timeout** is now the largest category. The story left it alone on
   purpose (§6). After the substitution, a reduction leaf might do better skipping the quick
   close and going straight to the leaf procedure (about 1.5 s, independent of load).
