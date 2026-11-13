# Reduction-walk goals (story 105)

Front goals (`equivS`) in the shape of EasyCrypt's `domino-json/3` answers, read by the unit tests of
`src/easycrypt/tactics/reduction_walk.rs`. Only the fields the recognizers read are filled: each
statement's `kind`, `pp`, `cond.pp`, `then`/`else` and `lvalue.pp`.

**These goals are hand-made, not captured.** The story asked for the `Want::Full` answers of a live
EasyCrypt on a reduced copy of `Red_H7_1_H7_0_Send2` (Full4WHS); that capture was not possible in the
session that wrote story 105 (the exported Full4WHS files lie outside the worktree, and big projects
are not exported there). The statement texts are the ones EasyCrypt printed in
`Red_H7_1_H7_0_Send2` after `proc; inline *.` on 2026-11-12, as story 105 §2 quotes them. Replace
each file with the captured answer when one is taken; the tests read only the program heads.

| File | Where in `Red_H7_1_H7_0_Send2` | Expected head |
|---|---|---|
| `root.json` | after `proc; inline *.`: the router guards `if (!Comp_H7.Game_H7.abort_flag)` / `if (!Red_H7_1_H7_0.abort_flag)` | rule 6, `ExitGuards` |
| `nonce.json` | line 53 of the 2026-11-11 file: `ni1 <$ dbits_n` on both sides | rule 8, `Samplings { ni1, ni1 }` |
| `assumption-guard.json` | the *then* arm of `if (hon)`: the guard `if (!Comp_MAC.Game_MAC.abort_flag)` around `Init` (right) | rule 2 |
| `tail-branch.json` | after `rcondt{2}` and the `Init` body: `if (ec_result4 = None<:unit>) { Comp_MAC.Game_MAC.abort_flag <- true; }` (right) | rule 3 |
| `mac-key.json` | inside `Mac`: `if (key0 <> None<:bits_n>)` | rule 7, `Branches` |
| `prf-table.json` | `if (Comp_H7.Cloned_Pkg_PRF.PRF.d_H.[kid1] <> None<:bool>)` | rule 7, not an exit guard |

The generator was a throwaway script; edit the JSON directly.
