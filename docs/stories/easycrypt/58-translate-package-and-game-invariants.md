# Story 58 — Translate package and game invariants

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 06 (invariant translation), 42 (`<Pkg>_pkgstate`, game-state records, ADR 0007),
47 (`inv` guards only the invariant), 23 (lockstep execution), 53 (`relation_op_name`).
**Blocks:** nothing.
**Decision record:** `docs/adr/0010-package-and-game-invariants-are-conjuncts-of-inv.md`.

---

## 1. Why this story exists

The owner asked: *"In our EasyCrypt translation, do we translate game and package invariants?"*
The answer was no.

Domino has two kinds of one-sided invariant (`CONTEXT.md`): the **package invariant** and the
**game invariant**. A package template declares a package invariant (`invariant:` in
`PRF.pkg.ssp`). A composition declares a game invariant (`invariant:` in `Hybrid2.comp.ssp`).

Domino's SMT path uses them as follows (`src/gamehops/equivalence/mod.rs`, `load_invariants`;
`src/writers/smt/contexts/equivalence/emit.rs`):

- It makes one predicate for each (game instance, package instance) that has a package
  invariant: `package-invariant!<GameInst>-<Inst>!`. It makes one predicate for each game
  instance that has a game invariant: `game-invariant!<GameInst>!`.
- Every claim assumes all of these predicates on the **old** states of both sides.
- `generate_game_or_package_invariant_claims` makes one claim for each predicate on the **new**
  state, with the dependency `no-abort`.
- Domino also checks each predicate on the initial state.

The EasyCrypt translation does not read these files. `build_invariant_file` reads only
`Equivalence::invariants()`. If one of the two forms is in an equivalence's file, the translator
skips it with a comment (`handle_define_game_invariant`, `handle_define_package_invariant`,
`src/writers/easycrypt/invariant.rs`). So:

1. The EasyCrypt `inv` is weaker than what Domino assumes. An oracle whose proof needs the PRF
   invariant of 4WHS cannot close in EasyCrypt.
2. In EasyCrypt mode, lockstep execution already **assumes** the one-sided invariants on the old
   states, because they are base dependencies of every claim. EasyCrypt does not get the same
   assumption, so the two tools see different problems.

Vocabulary (`CONTEXT.md`): **Package invariant**, **Game invariant**, **side**, **Invariant**,
**State relation**, **`Domino_` operator**, **Saved joint tree**.

## 2. Inherited from earlier stories

- **Story 06:** `build_invariant_file` parses the equivalence's files with `SmtParser`. It
  translates each `define-fun` / `define-state-relation` into `op Domino_<mangled>`.
  `StateLookup` resolves dotted atoms (`left.<Inst>.<field>`).
- **Story 42 / ADR 0007:** each package with state has one record type, `<Pkg>_pkgstate`. All
  instances on both sides share it. Each side has a game record `<GameInst>_state`, with
  `{l_|r_}pkg_<Inst> : <Pkg>_pkgstate` fields, then parameter fields, then `{l_|r_}abort_flag`.
  `PackageStateMismatch` and `FieldCollision` are hard errors.
- **Story 47:** `inv = params_inv l r /\ l.abort = r.abort /\ (!l.abort => Domino_invariant l r)`.
- **Story 19:** the base case is closed by one line, `auto => />; smt(emptyE map_empty).`.
- **Story 53 (split by meaning uses EasyCrypt's names):** `relation_op_name` in `invariant.rs` is
  the one rule for `Domino_<mangled>`. `unfold_ops` in `tactics/mod.rs` uses it, but `inv` and
  `params_inv` are still hard-coded there.
- **Tactics driver:** `Prover` splits a leaf. An operator that starts with `Domino_` becomes
  `Part::Relation`. `pair_view` (`driver.rs`) gives a part its Domino view. The view selects the
  admit reason, and a part whose view is `Fails` is admitted **without an EasyCrypt attempt**
  (driver §3.6).
- **Lockstep execution:** `ClaimSet::NoDependencies` (`src/debug/lockstep_run.rs`) is the
  EasyCrypt-mode claim set: `equal-output` and `invariant`, with each state relation as a
  sub-verdict of `invariant` (`PairRecord::relations`).
- **ADR 0008:** a saved joint tree has a fingerprint with four parts (`code`, `constants`,
  `randomness`, `invariants`). A stale tree is still used, with a warning.

Facts found during the grilling:

- In SMT, `pkg.<name>` binds only the **state fields** of the package (`gen_varbinding`), never
  its parameters. `game.<Inst>.<name>` also binds only state fields.
- In Domino, a `define-fun` in a package or game invariant file is emitted one time for **each
  instance and side** that loads the file, so cvc5 stops with a duplicate definition when the
  package occurs two times. Two invariant forms for one package fail the same way. So the only
  content that works in Domino for all projects is exactly one invariant form.
- The existing base-case line closes the PRF invariant on the initial state (checked with a
  model of `PRF_pkgstate` in EasyCrypt r2026.09).
- Projects that use one-sided invariants: 4WHS (package `PRF`, composition `Hybrid2`) and yao
  (package `Keys`). In Simple4WHS, `Hybrid1 ~ Hybrid2` has both kinds on the right side, and
  `Real_Hybrid3 ~ Ideal_Hybrid3` has both kinds on both sides. In Full4WHS, the games `H6` and
  `H7` contain `PRF`.

## 3. Work to do

The work has two parts. Do Part 1 first. Part 2 needs the names and the operator map from
Part 1.

### Part 1 — Translation

#### 3.1 Which invariants

For each side, collect:

- the package invariant files of every package instance of that side's game instance
  (`inst.pkg.invariants`), in `ordered_pkgs_idx()` order;
- the game invariant files of that side's composition (`game_inst.game().invariants`).

Do this for both sides, also when both sides use the same composition.

#### 3.2 What a one-sided invariant file may contain

Parse each file with a new `SmtParser` implementation for one-sided files. Across **all** files of
one package template, there must be exactly one `define-package-invariant`. Across all files of
one composition, there must be exactly one `define-game-invariant`. Nothing else is permitted.
Each of these is a hard `InvariantError` that names the file and the form:

- a `define-fun`, `define-state-relation`, `define-lemma` or bare top-level s-expression;
- a second invariant form for the same package or composition;
- a form of the wrong kind (`define-game-invariant` in a package file, or the opposite);
- a package invariant for a package with no state fields (`StatelessPackageInvariant`): there is
  no `<Pkg>_pkgstate` for it.

Parse each package template's files one time, also when the package has several instances, and
also when the package is on both sides.

Also change `handle_define_game_invariant` and `handle_define_package_invariant` of the
**equivalence's** parser: they now give a hard error, not a skipped comment. Domino's SMT path
already rejects these forms there (`RewriteNeedsPackageContext`, `RewriteNeedsGameContext`).
Remove the two forms from the doc comment of `InvariantFile::skipped`.

#### 3.3 Operators

Package invariant: one operator for each package **template**, over its state record:

```
op PkgInv_<Pkg> (s : <Pkg>_pkgstate) : bool = <body>.
```

`pkg.<field>` in the body becomes ``s.`<Pkg>_<mangled field>``. Use the field names of
`pkg_state_field_name`.

Then one **wrapper** operator for each instance of the package, on each side. It has no body of
its own:

```
op PkgInv_<l|r>_<Inst> (l : <GameInst>_state) : bool = PkgInv_<Pkg> l.`l_pkg_<Inst>.
```

For example, `Real_Hybrid3 ~ Ideal_Hybrid3` gets `PkgInv_PRF` one time, `PkgInv_l_Prf` and
`PkgInv_r_Prf`. Each wrapper stands for exactly one Domino claim
(`package-invariant!<GameInst>-<Inst>!`). This lets the tactics driver give each conjunct the
verdict of its own claim by operator name only (§3.8).

Game invariant: one operator for each side whose composition has a game invariant, over that
side's game record:

```
op GameInv_<GameInst> (g : <GameInst>_state) : bool = <body>.
```

`game.<Inst>.<field>` becomes ``g.`{l_|r_}pkg_<Inst>.`<Pkg>_<mangled field>``, through the same
lookup that `build_side_record` fills for that side.

The body uses the existing expression translator (quantifiers, `let`, `ite`, maps, `Maybe`,
tuples, and binder escaping). An atom that is not a state field, a binder or a known function is
`InvariantError::Unrecognised`, as today.

Names: use the `PkgInv_` and `GameInv_` prefixes, not `Domino_`. Every mangled SMT name starts with
`Domino_`, so the new names cannot collide with one. A wrapper name could collide with a template
name (a package named `l_Prf`) or with another wrapper (instance `T_b` against package `T` and
instance `b`). Register all the new names in `OpRegistry`, so a collision is a hard error, as for
the `Domino_` names. Put the name helpers next to `pkg_state_type_name`.

Put the operators after the `Domino_` operators and before `params_inv`: the `PkgInv_<Pkg>`
templates, then the wrappers, then the `GameInv_` operators.

#### 3.4 `inv`

The guarded part gets the new conjuncts (ADR 0010):

```
op inv (l : L_state) (r : R_state) : bool =
     params_inv l r
  /\ l.`l_abort_flag = r.`r_abort_flag
  /\ (   !l.`l_abort_flag
      =>    Domino_invariant l r
         /\ PkgInv_l_<Inst> l /\ …       (* left instances, ordered_pkgs_idx order *)
         /\ GameInv_<L> l                 (* if the left composition has one *)
         /\ PkgInv_r_<Inst> r /\ …       (* right instances *)
         /\ GameInv_<R> r).
```

An equivalence without one-sided invariants gets the same `inv` as before, byte for byte.

#### 3.5 The new code goes into a submodule

`invariant.rs` is 3088 lines. Put the parser for one-sided files, the operator building and the
new error variants in a new submodule, `src/writers/easycrypt/invariant/side.rs`. `invariant.rs`
calls it from `build_invariant_file` and gives it the `StateLookup` and the record types.

#### 3.6 One owner for the operator names

Move `unfold_ops` from `tactics/mod.rs` into the invariant module, next to `relation_op_name`,
and extend it. It stays a pure function that reads no file (ADR 0006):

```rust
pub struct InvariantOp {
    /// The EasyCrypt operator, e.g. `PkgInv_r_Prf`.
    pub name: String,
    /// The one Domino claim it stands for: `package-invariant!Hybrid2-Prf!` for a wrapper,
    /// `game-invariant!Hybrid2!` for a `GameInv_` operator. `None` for `inv`, `params_inv`,
    /// the `Domino_` operators and the `PkgInv_<Pkg>` templates.
    pub claim: Option<String>,
}

pub fn invariant_ops(left: &GameInstance, right: &GameInstance, relations: &[String])
    -> Vec<InvariantOp>
// order (the order `rewrite /… in` unfolds them): inv, params_inv, Domino_<r>…,
// PkgInv_<l|r>_<Inst>… (wrappers), PkgInv_<Pkg>… (templates), GameInv_<GameInst>…
```

The translator uses the same name helpers (`relation_op_name`, and new `pkg_inv_op_name`,
`game_inv_op_name`) when it writes the operators.

Add two helpers to `emit.rs`, `package_invariant_claim_name(game_inst, pkg_inst)` and
`game_invariant_claim_name(game_inst)`. Use them in its three `format!` sites and in
`invariant_ops`, so that each claim name has one owner.

### Part 2 — Lockstep execution and tactics

#### 3.7 EasyCrypt-mode lockstep checks the one-sided invariants

In `ClaimSet::NoDependencies`, the `invariant` check also checks every claim from
`generate_game_or_package_invariant_claims` on the new state, without dependencies. Each claim is
a sub-verdict of `invariant`, by its claim name, in the same list as the relation sub-verdicts.
Apply the rule for aborting pairs that `invariant` has today: on a pair where a side aborts, a
failure counts as inconclusive.

The Domino listing (`domino debug`, all-claim runs) already checks these claims and does not
change.

> **Changed later by symbolic-execution story 21 §3.3 (owner decision, 2026-10-07).** After story
> 21, every part of `invariant`, these sub-verdicts included, is checked only on a pair where
> `invariant` is goal-fails or inconclusive. The `invariant` goal on the EasyCrypt listing then holds
> the whole guarded conjunction, so a verified `invariant` means that each part is verified, and
> `pair_view` gives the part that verdict. Implement §3.7 as written here. Story 21 changes it.

#### 3.8 The tactics driver

- `tactics/mod.rs`: build the unfold list from `invariant_ops(...)`. Remove its own
  `unfold_ops` and the hard-coded `inv` and `params_inv`. Move the test
  `unfold_ops_use_the_writers_op_names` with the function.
- `driver.rs`: add `Part::SideInvariant { op: String, claim: String }`. When a leaf part is an
  application of an operator whose `InvariantOp::claim` is `Some(claim)` (a wrapper or a
  `GameInv_` operator), the part becomes `Part::SideInvariant { op, claim }`, and the driver
  unfolds `op`. Its claim label is `invariant/<op>`. When the part is an application of a
  `PkgInv_<Pkg>` template (after a wrapper was unfolded), the driver unfolds it and keeps the
  part as it is.
- `pair_view` for `Part::SideInvariant { claim, .. }`: the view of the sub-verdict of `claim`
  only, with the rule for aborting pairs. If the sub-verdict is not there (a tree saved before
  this story), the view is `Inconclusive`.

The driver finds the claim by operator name only. It must not read the argument of the
application, and it must not know how the translator names record fields.

#### 3.9 The saved-tree fingerprint

Add a fifth part, `claims`, to `PARTS` in `src/debug/lockstep_fingerprint.rs`. It hashes the names
of the claims and sub-verdicts that EasyCrypt-mode lockstep execution checks for the oracle.
`describe_part("claims")` is `"the claims checked"`. A tree saved before this story has no
`claims` part, so `Fingerprint::changed` reports it as changed, and the tree is stale. ADR 0008
still applies: the tree is used, with a warning.

## 4. Acceptance criteria

- [ ] For `Simple4WHS`, `Eq_Hybrid1_Hybrid2_Invariants.ec` declares `PkgInv_PRF`, the wrapper
      `PkgInv_r_Prf` and `GameInv_Hybrid2`, each one time. `inv` has
      `PkgInv_r_Prf r /\ GameInv_Hybrid2 r` after `Domino_invariant l r`, inside the `!abort`
      guard.
- [ ] For `Real_Hybrid3 ~ Ideal_Hybrid3`, the body of the PRF invariant is in `PkgInv_PRF`
      only, one time. The wrappers `PkgInv_l_Prf` and `PkgInv_r_Prf` and the operators
      `GameInv_Real_Hybrid3` and `GameInv_Ideal_Hybrid3` are each declared one time.
- [ ] A name collision between a wrapper and another `PkgInv_` name is a hard error (unit
      test).
- [ ] For an equivalence without one-sided invariants (`Hybrid0 ~ Hybrid1`), the invariant file
      is byte-identical to the golden from before this story.
- [ ] The goldens for the one-sided equivalences are new or regenerated, and an EasyCrypt compile
      test passes for each.
- [ ] Translation of `example-projects/4WHS` (Full and Simple) compiles in dependency order with
      the real `easycrypt`, base cases included.
- [ ] A synthetic project under `testdata/easycrypt/story58/` has one theorem for each hard
      error of §3.2: a helper `define-fun`, two invariant forms, a wrong-kind form, a stateless
      package with an invariant, and `define-package-invariant` in an equivalence file. Each
      error names the file.
- [ ] `invariant_ops` gives the operators in the order of §3.6. The tactics module has no
      hard-coded operator names.
- [ ] `emit.rs` builds the one-sided claim names only through the two new helpers.
- [ ] The synthetic project under `testdata/easycrypt/story58/` also has one small theorem that
      translates and proves: a package with a package invariant and a composition with a game
      invariant, on both sides. EasyCrypt-mode lockstep execution on it records a sub-verdict for
      each `package-invariant!…!` and `game-invariant!…!` claim on every pair. (Overview §7: do
      not run lockstep execution on 4WHS or yao.)
- [ ] `domino easycrypt prove` on that theorem proves every oracle, or admits only parts whose
      Domino view is `fails`.
- [ ] A unit test of `pair_view`: on a pair where `package-invariant!Real_Hybrid3-Prf!` fails
      and `package-invariant!Ideal_Hybrid3-Prf!` is verified, the part for `PkgInv_l_Prf` is
      `fails` and the part for `PkgInv_r_Prf` is `verified`. A part whose sub-verdict is not
      there is `Inconclusive`.
- [ ] A tree saved before this story (a fixture without `claims`) is reported as stale, with
      "the claims checked", and it is still used.
- [ ] **Owner-run, not by the implementing session** (overview §7): a tactics run on
      `Simple4WHS` `Hybrid1 ~ Hybrid2` proves at least the oracles it proved before this story.
      Record the leaves that admit a `PkgInv_`/`GameInv_` part, their Domino views, and the
      lockstep time before and after.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/4WHS
$D easycrypt export --theorem Simple4WHS --force
grep -n '^op PkgInv_\|^op GameInv_' <out>/*/Eq_Hybrid1_Hybrid2_Invariants.ec
grep -A12 '^op inv' <out>/*/Eq_Hybrid1_Hybrid2_Invariants.ec

cd ../../testdata/easycrypt/story58
$D easycrypt export --theorem HelperFun --force; echo $?    # non-zero, names the file
$D easycrypt export --theorem OneSided --force
$D easycrypt prove --theorem OneSided                       # synthetic project only

# owner-run only (overview §7):
cd ../../../example-projects/4WHS
$D easycrypt prove --theorem Simple4WHS --proofstep <Hybrid1 ~ Hybrid2>
```

## 6. Rejected alternatives

- **Separate `hoare` lemmas joined with `conseq`** for each side and oracle. Rejected for now:
  much change amplification across the skeleton, the tactics driver, lockstep execution, the
  session record and the live page, for a small re-use gain. Recorded in ADR 0010 with the
  conditions for coming back to it.
- **No `!abort` guard on the new conjuncts.** Rejected: Domino proves them only under `no-abort`.
- **One operator for each side and instance** (a copy of the SMT shape). Rejected: the same body
  N times, change amplification. `<Pkg>_pkgstate` (ADR 0007) exists for this use.
- **Support helper `define-fun`s and several invariant forms.** Rejected: that is more than
  Domino supports (duplicate definitions in cvc5), so the two tools could later disagree.
- **Skip the forms in an equivalence's file with a comment, as before.** Rejected: Domino rejects
  them there, and a comment hides the mistake.
- **`Domino_` prefix for the new operators.** Rejected: the driver would read them as relations
  and silently use the `invariant` verdict, and a user relation could collide with them.
- **The tactics module derives the new names.** Rejected: every naming rule in two places.
- **The driver finds the operators in the goal.** Rejected: one more goal round-trip for each
  premise, and goal serialization is the main cost of proving.
- **No Domino verdict for the new parts.** Rejected: you could not tell a false invariant apart
  from a weak smt.
- **One part for each operator, with the worst verdict of its instances.** Rejected: when one
  package occurs two times in an equivalence, a failure of one instance's invariant gives the
  other instance's conjunct, on the same leaf, a `fails` view. The driver's `Fails` shortcut
  (story 53) then admits that conjunct with no EasyCrypt attempt.
- **`invariant_ops` gives the record field of each application,** and the driver reads the
  argument from the goal. Rejected: the driver would need new code to read terms and would
  depend on the shape of the argument. The wrappers give the same result by name only.
- **Refuse saved trees from before this story.** Rejected: against ADR 0008, and it costs the
  lockstep time that resume saves.
- **Two stories** (translation, then lockstep). Rejected: between the two stories the new parts
  would carry a wrong `inconclusive` label.

## 7. Notes / risks

- **Larger leaf goals.** Each leaf now also has the one-sided invariants of both sides. If the
  quick close or the fallbacks get slower on 4WHS, record it in the implementation report and
  stop. Do not change the fallback sequence without the owner.
- **Base case.** A project whose one-sided invariant is false on the initial state now fails to
  compile at the base case. Domino rejects it too.
- **Solver cost.** EasyCrypt-mode lockstep execution does one more check for each one-sided claim
  on each pair (about 2–3 more for `Hybrid1 ~ Hybrid2`). Record the lockstep time before and
  after on the synthetic project. The owner records it on 4WHS.
- **One more unfold step.** A package-invariant conjunct now unfolds in two steps (the wrapper,
  then the template). `rewrite /… in hpre` does both in one sentence, because the wrappers come
  before the templates in the unfold list.
- **yao.** `Keys` has a package invariant, but no yao theorem has an EasyCrypt test today. Do not
  add one in this story.

## 8. State handed to the next story

Record in `58-…-IMPLEMENTATION-REPORT.md`: the operator and claim-name helpers and where they
live, the shape of `invariant_ops`, the new `InvariantError` variants, the goldens added or
regenerated, the lockstep time before and after on the synthetic project, and the owner-run check
left unchecked.
