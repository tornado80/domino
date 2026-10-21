# Story 85 — A game instance can have the name of its composition

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 69, 77, symbolic-execution 25.
**Blocks:** nothing.
**ADR:** none (ADR 0014 gives the side-invariant lemma; this story does not change it).
**Decisions:** grilling of 2026-10-21. The questions are not yet answered: see §7. §3 uses the
recommended answers.

A **debugger** story, Rust only. Test-first.

---

## 1. Why this story exists

In `ec4whs/4WHS`, `theorem/Full4WHS.ssp` had `instance H4 = H4 { … }` and `instance H5 = H5 { … }`.
`domino-ec easycrypt prove --project 4WHS --theorem Full4WHS --side-inv H4` gave, for each oracle:

```
NewKey: no tactics (lockstep execution failed: theorem `Full4WHS` already has a game instance
named `H4`, the name one-sided execution gives the composition with free parameters)
```

The error is `DebugError::SideInstanceNameTaken` (`src/debug/side_run.rs`, `free_theorem`). H2, H6
and H7 have only instances with suffixes (`H2_0`, `H6_1_0`, …), and their side-invariant jobs work.
The owner renamed the instances to `H4_b` and `H5_b` as a workaround. A theorem must not need that.

## 2. What goes wrong when the names are the same

- **Why the free instance is named `C`.** `free_theorem` clones the theorem and adds two game
  instances of `C` with free parameters: `C` and its copy `C$side`. The owner of a claim name is the
  name of the game instance: `smtrewrite.rs` makes `SmtStatementKind::GameInvariant { game:
  inst.name() }`, and `game_invariant_claim_name` gives `game-invariant!<N>!<owner>!`. On the
  EasyCrypt side, `GameInv_<N>_of_<C>` stands for the claim `game-invariant!<N>!<C>!`
  (`side_invariant_ops`, `invariant.rs`). The side-invariant job matches the claims of the side
  tree to these operators by name. Thus the free instance must have the name `C`.
- **Every lookup takes the first instance with that name.** `Theorem::find_game_instance` is a
  `Vec::find`. The free instance is added last. With a theorem instance `C`, all these lookups get
  the theorem's instance, with its fixed parameters: `EquivalenceContext::left_game_inst_ctx`
  (the SMT vocabulary, the invariants, the claims), the aux of `DebugTransform`
  (`sample_info`), `EasyCryptTransform` with `inline_oracle_ec` (the listing), and
  `Fingerprint::of_side`. Nothing reads the free instance.
- **The result if the check were removed.** The side tree would execute `C` with the parameters of
  one game instance, not free parameters. A branch on a literal parameter folds (see the fold test
  "`bprf` is free: the ideal branch stays"), so the tree has fewer paths than `SideInv_<C>_<O>`,
  which is a hoare lemma for all parameters. The debugger can then say "all claims hold", and the
  walk gives tactics that EasyCrypt rejects. The fingerprint is of the wrong instance. The error is
  silent. Thus the check prevents a real fault.
- **What does not break.** There is no SMT symbol clash: the context declares only its left and
  right instances (`<<game-consts-C>>`, `<<game-consts-C$side>>`). There is no EasyCrypt name clash:
  the side names are per composition, and the proofstep operators drop their claim names
  (`leaf_part_ops`). There is no path clash: `!debug!/SideInv_<C>/` is not a proofstep directory.
  `C$side` cannot clash: `$` is not in the `identifier` rule of `ssp.pest`.
- **The fault is in the implementation, not in the theorem.** The copy of the theorem puts the free
  instances in the same name space as the theorem's instances, but one-sided execution never reads
  the theorem's instances. In Full4WHS, `H4` binds each parameter to the theorem constant of the same
  name, and `free_params` selects exactly these constants. The free instance was equal to the
  theorem's instance, so the run would have been correct, but the check stopped it.

## 3. Work to do

### 3.1 The free theorem holds only the free instances

`free_theorem` returns a theorem whose instances are only `C` and `C$side`, with no game hops and no
proofs. It keeps the name, the constants (`free_params` adds to them), the packages and the
assumptions. A theorem instance with the name `C` is then not in the theorem that one-sided
execution reads, so the names cannot clash.

- Delete `DebugError::SideInstanceNameTaken` and its check. ("Define errors out of existence":
  `free_theorem` owns the problem and solves it; no caller sees a condition.)
- Claim names, SMT symbols, the base frame, the fingerprints, the records and the EasyCrypt export do
  not change. `EquivalenceContext::types` reads only the left and right aux and the theorem
  constants, so the base frame of a theorem without a clash is byte-identical. Saved side trees
  resume (ADR 0008).
- The same pattern exists: the package tree walks its own one-game theorem (`open_game_theorem`,
  symbolic-execution 29).
- Also: the three transforms in each run, and `side_fingerprint`, process 2 instances, not all of
  the theorem's instances (27 in Full4WHS).
- Update the module documentation of `side_run.rs` ("adds to the theorem a game instance named `C`").

### 3.2 The error prefix of a side-invariant job

`src/easycrypt/tactics/mod.rs` (`OracleTactics::empty(…, "lockstep execution failed: …")`) gives the
same prefix to a side-invariant job, which runs one-sided execution. A side-invariant job (and a
package-invariant job) says `one-sided execution failed: …`. A proofstep job does not change.

## 4. Rejected alternatives

- **A mangled name `C$free`, like `C$side`.** No clash, but the claim names would be
  `game-invariant!<N>!C$free!` and would not match `GameInv_<N>_of_<C>`. The owner of the claim name
  must then come from somewhere other than the instance name: `side_run` would give the composition
  name through `EquivalenceContext` to `SmtRewrite` and `SmtStatementKind`. That is state escaping
  its owner and change amplification across `smtrewrite.rs`, `emit.rs` and the claims; the debug
  pages would show `C$free` in states and constants.
- **The free instance wins the lookup** (add it first, or `find` from the end). One line, but every
  lookup by name stays a trap: an unknown unknown for the next reader.
- **Rename the theorem's instance in the copy** (`C` to `C$theorem`). The game hops and proofs that
  name it must also change, for no use.
- **Keep the error with a better message** (report it once for each composition, not for each
  oracle, and tell the user to rename). Safe but the theorem must change for a fault of the tool.

## 5. Tests first

- [x] Red: a new fixture `testdata/debug/se25-name-taken`, which is `testdata/debug/se25` with the
      instance `s` renamed to `S` (`n: 1`) and `equivalence S s2`. Today `run_side_command(…, "S",
      "O", …)` gives `SideInstanceNameTaken`. After: the run succeeds, the root is a `Split` on
      `n > 0` and there are four terminals, as for `se25`. This shows that the free instance is
      executed, not `S` with `n = 1` (that would fold the branch).
- [x] `free_theorem` of `se25`: the instances are exactly `[S, S$side]`, and the game hops are empty.
- [x] `se25` without a clash: the `trace.json` claims, the base frame and the fingerprint are
      byte-identical before and after.
- [x] A side-invariant job whose one-sided run fails reports `one-sided execution failed: …`; a
      proofstep job still reports `lockstep execution failed: …`.

## 6. Acceptance criteria

- [x] All tests of §5 green; no reference to `SideInstanceNameTaken` is left.
- [ ] The owner's check: on a copy of `4WHS` with `instance H4 = H4 { … }` again,
      `domino-ec easycrypt prove --side-inv H4` gives tactics for the oracles (not "no tactics"),
      as with `H4_b`.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 7. Open questions

The grilling could not ask the owner directly. Each question has its recommended answer first.

1. **Must a game instance with the name of its composition work with `--side-inv`?**
   Recommended: yes, the theorem's names are the user's (§2: the check stops correct runs).
   Other: keep the error and improve the message (§4).
2. **Which fix?** Recommended: the free theorem holds only the free instances (§3.1).
   Others: a mangled name with a separate claim owner; the free instance wins the lookup (§4).
3. **What does the free theorem keep?** Recommended: the name, constants, packages and assumptions;
   no other instances, no game hops, no proofs. Other: keep all and drop only the instance named `C`
   (less change, but the copy keeps hops that name a missing instance).
4. **Is the error prefix of §3.2 in scope?** Recommended: yes, it is one line and the report misled
   the reader. Other: a separate story.
5. **The red test fixture?** Recommended: a new directory `testdata/debug/se25-name-taken` (§5).
   Other: build the theorem in memory in the test.
6. **Full4WHS after the fix?** Recommended: the owner decides if `H4_b`/`H5_b` go back to `H4`/`H5`;
   the acceptance check uses a copy, not `ec4whs`.
7. **ADR or glossary entry?** Recommended: no ADR (the behaviour of one-sided execution does not
   change, only its inner theorem). Update the `side_run.rs` module doc and the row in
   `00-overview.md`.
