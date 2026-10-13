# Story 69 — Implementation report: side-invariant lemmas of the composition

Rust only. **The exported `.ec` files change.** ADR 0014 is implemented.

## What changed

### Translation (the exported files)

- **`Pkg_<V>.ec`**: the first variant of each package (discovery order) now declares
  `type <Pkg>_pkgstate` (when the package has state) and the template `op PkgInv_<Pkg>` (when
  it has a package invariant). `invariant.rs`: `StateOwners` (which file declares each type;
  one type for the whole theorem, else `PackageStateMismatch`).
- **`Comp_<C>.ec`**, for a composition with a side invariant: `require import` of the package
  files with the state types, then `type <C>_side` (`<C>_pkg_<Inst>` for each instance with
  state, `<C>_abort_flag`), `op PkgInv_<C>_<Inst>`, `op GameInv_<C>`, and
  `op side_inv_<C> s = !s.<C>_abort_flag => PkgInv_… /\ GameInv_<C> s`
  (`invariant/side.rs`: `package_items`, `composition_items`).
- **`SideInv_<C>_<O>.ec`** (new, `sideinv.rs`):
  `lemma SideInv_<C>_<O> : hoare[Comp_<C>.Game_<C>.<o> : Comp_<C>.side_inv_<C> {| … |} ==> …]`,
  proof `+ proc; inline. admit.`. The record fields are qualified with `Comp_<C>.`, so no file
  imports a composition theory. **`SideInv_<C>.ec`** requires each oracle file.
- **`Eq_<L>_<R>_Invariants.ec`**: no `<Pkg>_pkgstate`, no `PkgInv_`/`GameInv_` operators;
  `require import` of the package files; `inv` guards only `StateRelation_invariant`.
- **Oracle lemma** `Eq_<L>_<R>_<O>.ec`: precondition
  `={arg} /\ inv … /\ Comp_L.side_inv_L {|…{1}|} /\ Comp_R.side_inv_R {|…{2}|}` (only sides
  that have side invariants); postcondition unchanged. It requires the package files, not the
  `SideInv_` files.
- **Glue** `Eq_<L>_<R>.ec`: `call (: inv … /\ side_inv_L … /\ side_inv_R …)`; requires
  `SideInv_<L>` / `SideInv_<R>`; each bullet
  `+ by conseq Eq_…_<O> SideInv_L_O.SideInv_L_O SideInv_R_O.SideInv_R_O => /#.`
  (`_` in place of a left side without side invariants).
- AST/render: `EcExpr::OracleEquiv { assumed }`, new `EcExpr::OracleHoare`,
  `ProofLine::InvariantCall { also }`.
- **Name rule**: `insert_oracle_files` became `insert_lemma_files`; it covers oracle lemmas,
  side-invariant lemmas and `SideInv_<C>.ec`. `OracleFileCollision` is renamed
  `LemmaFileCollision` and names both owners.
- `ExportedTheorem::side_invariants` (`SideInvReport`), `EquivalenceReport::side_compositions`.

### Lockstep execution

- The EasyCrypt `invariant` check no longer contains the package and game invariant claims, and
  they are no longer parts of it (`easycrypt_invariant_query`, `easycrypt_check_names`). The
  base frame already assumed them on the old state. Trees saved before this story are stale
  (the `claims` fingerprint part changed) and still used.

### The side-invariant job

- `TacticsOptions::side_inv`; `JobKind::{Equivalence, SideInvariants(C)}`. A side-invariant job
  is the story 68 job machinery on a report whose proof file is `SideInv_<C>.ec`, so records,
  saved trees, locks and pages are `session/SideInv_<C>/<O>.record.json`, `<O>.tree.json`,
  `progress/SideInv_<C>/<O>.lock` and `progress/SideInv_<C>/<O>/`; seal, respawn, resume and
  `--jobs N` are the same code. One-sided execution is `run_side_command` (SE-25), artifacts
  under `!debug!/SideInv_<C>/<O>/`; `side_run::side_fingerprint` (new) checks a saved tree.
- **The walk** (`driver.rs`, `Judgement::Hoare`): `proc; inline.`, `sp k.`, `if.` (the
  not-aborted arm walks the side tree, the aborted arm gets the quick close or the fallbacks);
  determined node `rcondt ^if`/`rcondf ^if`; split `if.` with a bullet for each arm; sampling
  `seq 1 : (#pre); 1: auto…`; leaf: exit path `rcondt/rcondf ^if; 1: by auto.`,
  `auto => &hr hpre /=.`, then the leaf procedure of story 64 with the part fallbacks (65) and
  the key case split (66). Unfolded `PkgInv_<C>_<Inst>` / `GameInv_<C>` give their claim; a
  side-tree terminal's view is its claim's verdict (`side_pair_view`). The whole-leaf shortcut
  (§3.6) admits only when every claim fails, labelled `side-invariant`.
- `goals::is_program` accepts `hoareS`; `json::Form::program`.
- **`prove`** (`plan_run`): `--side-inv C` runs only that job (unknown composition:
  `TacticsError::NoSideInvariants`). `--proofstep P` checks `SideInv_<C>.ec` and every
  `SideInv_<C>_<O>.ec` of its compositions on disk; if one is missing the equivalence does not
  start and stderr says `warning: side invariants of <C> are not proved: run prove --side-inv <C>
  first` (also in the report; the CLI exits 1). Neither: the side-invariant jobs run on a thread
  of their own, in parallel with the equivalences' proof jobs. `TheoremTactics::side_invariants`,
  `unproved_side_invariants`; the report header of a side job is
  `tactics for SideInv_<C>.ec (side invariants of <C>)`.
- CLI: `domino easycrypt prove --side-inv <C>` (conflicts with `--proofstep`).

### Rejected shape

A separate driver for `hoare` judgements. Rejected: the walk, seal, resume, leaf procedure and
fallbacks are the same; the differences are a few tactics, which `Judgement` selects.

## Deviations

- **When a whole-theorem run starts a side job.** §3.3 says "every composition whose
  `SideInv_` files are missing". Export writes those files, so taken literally no side job
  would ever run. A whole-theorem run starts the side-invariant job of every composition with
  side invariants, and that job skips what its records say is proved (as proof jobs do).
- `<Pkg>_pkgstate` goes to the file of the package's **first variant**: a package with several
  variants would otherwise declare the type twice. The type is one for the theorem.
- The `conseq` keeps `=> /#` (the story 68 reason) and uses `_` for a left side without side
  invariants (checked with EasyCrypt on Simple4WHS `Hybrid1 ~ Hybrid2`).
- Lemma names in the glue are qualified (`SideInv_C_O.SideInv_C_O`): the glue requires only
  `SideInv_<C>`, whose requires are not imports.
- EasyCrypt's `kinds` say `program` for `equivS` only, so after a `hoare` `if.` only the front
  goal's kind is checked.
- **Not measured** (the owner asked not to run EasyCrypt proofs on the Full4WHS hops): admits
  and wall time of H6_1_0 ~ H6_1_1 and H6_1_1 ~ H7_0 before and after, and the admits of
  `SideInv_H6_*`. Open for the owner.
- `--features cvc5-lib` cannot be built here (no cmake): the CLI `prove` path and the updated
  cvc5-lib-only test `the_side_invariants_are_not_checked_by_lockstep_execution_on_the_easycrypt_listing`
  are not compiled. **Open.**

## Tests

- `invariant::side::tests`: definitions in package and composition files, the PRF body only in
  `Pkg_PRF.ec`, `OneSided` goldens (`testdata/easycrypt/story69/OneSided/`), the five error
  cases (now through export), op-name collision, the **name rule** test
  (`testdata/easycrypt/story69`: composition `A` oracle `B_x` against `A_B` oracle `x`), the
  unfold order, the claims of `side_invariant_ops`.
- `invariant::tests`: invariant files compiled after the exported package files; state types in
  their package files. Goldens regenerated: story06, story42, story58 invariant files.
- `export` compile tests compile every `SideInv_` file before the equivalences (Simple4WHS,
  story58, kem-dem, **Full4WHS: every glue compiles with every proof admitted**).
- `tactics::tests::side_invariant_jobs`: the `--proofstep` warning and no job started (plan and
  full run), `--side-inv` / whole-theorem plans, file ownership; live: the `OneSided` side job
  proves `SideInv_Game_Inc` with no admit along the side tree, then the equivalence and the glue
  compile; SE-25's `S` (branches on a free parameter): `if.` per branch, the two terminals where
  `k >= 0` breaks admitted as `invariant/PkgInv_S_p; domino-fails`; **a whole-theorem run has
  two EasyCrypts at the same time** (side job and proof job).

## Results

- `cargo test --lib`: 749 passed, 0 failed, 6 ignored. `cargo test -p domino --test easycrypt_overwrite`: 9 passed. `cargo clippy --workspace --all-targets`: no warnings in the changed files. `cargo build --release --workspace`: OK.
- Live (`DOMINO_EASYCRYPT` = `easycrypt/_build/default/src/ec.exe`, `cvc5` on `PATH`),
  `cargo test --lib easycrypt`: 540 passed, 8 failed. The 8 are the `hello-world-oracle-rename-new`
  tests that story 68's report lists as open (they need `cvc5-lib`); not changed by this story.
- `easycrypt::session::tests::the_interrupt_is_sent_again_until_it_is_answered` failed once
  under the load of the full suite and passed three times alone: a timing-sensitive test,
  not changed here.
- Complexity: the sdlc gate does not score Rust (`NotApplicable`); CC is UNMEASURED.
