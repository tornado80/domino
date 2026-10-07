# Story 21 — Each check has its own verdict, and a failing invariant is broken down

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** EasyCrypt story 58 (`invariant_ops`, the one-sided sub-verdicts, `pair_view` for
`Part::SideInvariant`); stories 19 (all-claim runs), 20 (the sequential grid).
**Blocks:** symbolic-execution 22, 23; EasyCrypt 59.

---

## 1. Why this story exists

The owner said: *"In debugging mode of Domino code, I see `Domino_invariant` and
`Domino_relation-*`. These names are for EasyCrypt export and should not be mixed here. You can have
one invariant, one for each state relation, one for same-output and one for equal-aborts. It's very
good that you verify state relations separately; I want that in the sequential mode as well. Also, I
don't properly understand how claims are asserted in the sequential mode. Is each claim asserted
separately? I just get one inconclusive and don't get whether it is due to the invariant, a state
relation, equal-aborts, or same-output."*

Facts found during the grilling:

- **The sequential mode already checks each claim separately.** In an all-claim run,
  `check_claims` (`src/debug/claims.rs`) does one `push`, the claim's dependencies, its negated goal,
  `check-sat`, `pop` for each claim at each terminal pair. `trace.json` and `summary.txt` keep a
  verdict for each claim.
- **The sequential page hides it.** A pair shows one aggregate verdict (the worst). The **Model**
  section shows only the model of that one failure. The **Claim assertion** section joins every
  goal into one block with one `(check-sat)`, and "Copy runnable query" copies that block
  (`pairQueryText`, `src/debug/report.rs`). This is not what the solver got.
- **Only lockstep breaks down `invariant`.** `LockstepEngine::check_pair` (`src/debug/lockstep.rs`)
  checks each state relation when `invariant` is neither verified nor unreachable. The sequential
  mode does not.
- **The lockstep breakdown has a defect.** It checks each state relation *after* `check_claim` has
  popped the claim's dependencies. If `invariant` depends on a project lemma, a state-relation
  check can fail on a pair where the lemma is false.
- **The relation list holds `invariant` itself.** `state_relation_names()` returns every state
  relation, `invariant` too. So the lockstep page shows the check `invariant` and, under it,
  `Domino_invariant`: the same check two times.
- **`Domino_` comes from the page.** `src/debug/lockstep_viewer.html` writes `Domino_${name}` on
  both listings. On the Domino listing that is an EasyCrypt name.
- **The tactics run reads the debug check list.** `WalkedTree.relations`
  (`src/easycrypt/tactics/mod.rs`) is copied from `run.meta.goals.relations`, and the tactics run
  unfolds `Domino_<name>` for each entry. If this story removes `invariant` from the check list
  without care, the tactics run stops unfolding `Domino_invariant`.

Vocabulary (`CONTEXT.md`): **Check**, **State relation**, **Invariant**, **Dependency**,
**All-claim run**, **Listing**, **Package invariant**, **Game invariant**.

## 2. Inherited from earlier stories

- **Story 19 / ADR 0003:** an all-claim run checks the whole obligation set on one exploration.
  The claims are independent of the strategy and the listing. `check_claim` owns the dependency
  frame and the `Unreachable { DependencyFalse }` rule.
- **Story 20:** the sequential page uses the shared grid and listing code in `report.rs`.
- **EasyCrypt story 58:**
  - `invariant_ops(left, right, relations)` is the one owner of the operator names of the
    invariant file, and the tactics module builds its unfold list from it.
  - On the EasyCrypt listing (`ClaimSet::NoDependencies`), the `invariant` check gets each
    package and game invariant claim as a sub-verdict, in the same list as the state-relation
    sub-verdicts.
  - `pair_view` gives `Part::SideInvariant` the view of its own sub-verdict, and `Inconclusive`
    when there is none.

## 3. Work to do

### 3.1 The checks and their names

A **check** is one negated goal at one terminal pair with its own verdict: one claim, or one part
of a claim.

- Each claim of the run's claim set is a check, by its claim name.
- The `invariant` claim has **parts**:
  - **Domino listing:** each state relation **except `invariant`** (the `invariant` claim already
    is that check). Its name is `state-relation <name>`. The package and game invariants are not
    parts here: they are separate claims already.
  - **EasyCrypt listing:** the conjuncts of `inv` as `invariant_ops` lists them: each
    `Domino_<r>` except `Domino_invariant` (story 59 renames them to `StateRelation_<r>`), then the
    `PkgInv_<l|r>_<Inst>` and `GameInv_<GameInst>` operators of story 58. Each part is named by its
    EasyCrypt operator.

No page on the Domino listing shows an EasyCrypt operator name.

### 3.2 The claim checker owns the breakdown

`ClaimQuery` (`src/debug/claims.rs`) gets the parts:

```rust
pub struct ClaimQuery {
    pub name: String,
    pub dependencies: Vec<(String, SmtExpr)>,
    pub negated: SmtExpr,
    /// The named parts of the goal, each negated; empty for every claim but `invariant`.
    pub parts: Vec<(String, SmtExpr)>,
}
```

Each listing fills `parts` where it builds its claim queries. Nothing else knows the rule.

`check_claim` checks the parts itself, in a new small function `check_parts`:

- only when the claim's verdict is goal-fails or inconclusive;
- **inside the dependency frame** that `check_claim` already pushed: `push`, the negated part,
  `check-sat`, `pop` for each part;
- the model of a failing part goes to `models/<pair>.<claim>.<part>.smt2`.

`ClaimVerdict.relations` becomes `ClaimVerdict.parts: Vec<PartVerdict>` (`name`, `verdict`,
`model`). On a pair where the claim is verified or unreachable, `parts` is empty.

Delete the state-relation loop and `check_goal` in `LockstepEngine::check_pair`. Both strategies
then get the breakdown from `check_claims` / `check_claim`, also in a single-claim run
(`--claim invariant`). `--first-failure-per-claim`: when a claim is skipped on a pair, its parts
are skipped too.

### 3.3 The EasyCrypt listing: one rule for every part

Story 58 checks the one-sided sub-verdicts on **every** pair. This story uses one rule for every
part: a part is checked only where `invariant` is goal-fails or inconclusive. For that rule to be
sound, a verified `invariant` must mean "every part is verified". So:

- On the EasyCrypt listing, the negated goal of the `invariant` check is the negation of the
  **whole** guarded conjunction: the invariant relation on the new states **and** each package and
  game invariant claim on the new states. This is what `inv` says after story 58.
- `pair_view` (`src/easycrypt/tactics/driver.rs`): for a state-relation part or a
  `Part::SideInvariant`,
  - if `invariant` is verified or unreachable, the part has that view (sound, because the
    `invariant` goal holds every part);
  - else the part has the view of its own part verdict, with the rule for aborting pairs;
  - else, if there is no part verdict (a tree saved before this story), the view is
    `Inconclusive`. It is **never** the `invariant` verdict when `invariant` failed.

### 3.4 The tactics run takes its state relations from the translation

The `relations` that the tactics run gives to `invariant_ops` come from the exported invariant
file (`InvariantFile`'s state relations), not from `run.meta.goals.relations`. `SavedTree.relations`
stays, for older trees, and is filled from the same source. Add a test: after this story the unfold
list still contains `Domino_invariant`.

### 3.5 The sequential page

Use **one** Verdicts renderer for both pages. Put it in `report.rs` next to the shared grid code
(story 20), and let `lockstep_viewer.html` use it too.

- **Tree rows:** keep the aggregate badge. Add the checks that are not verified, for example
  `inconclusive [invariant → state-relation rel_ctr]`, as `summary.txt` already does.
- **Verdicts section (new):** one row for each check: name, badge, the reason for `unreachable`,
  and the model. The part rows are under `invariant`. Where `invariant` is verified, the part rows
  say "not checked: invariant verified".
- **Claim assertion:** one block for each check, in the order the solver got them: `push`, the
  dependencies, the negated goal, `check-sat`, `pop`, then the parts the same way. "Copy runnable
  query" copies exactly that sequence.
- **Model:** each failing check keeps its own model text in `trace.json`, so the page stays
  self-contained. Today only the standing failure keeps it.
- The names come from the run's metadata (`meta.listing` and the part names). The page has no
  prefix rule of its own.

Raise `TRACE_SCHEMA` (`driver.rs`) and `LOCKSTEP_TRACE_SCHEMA` (`lockstep_run.rs`).

### 3.6 Not in this story

- Debug indexes and `--out` (story 22).
- The core claim set (story 23).
- The `StateRelation_` / `Helper_` names (EasyCrypt story 59). Until 59, the EasyCrypt listing
  shows `Domino_<r>`.

## 4. Acceptance criteria

- [ ] `check_claim` checks the parts under the claim's dependencies. A unit test: `invariant`
      depends on a lemma that is false on the pair; with the lemma assumed, no part fails because of
      the lemma (the old lockstep loop failed this).
- [ ] `LockstepEngine::check_pair` has no state-relation loop and no `check_goal`.
- [ ] A sequential all-claim run on a project whose `invariant` is inconclusive on some pair shows,
      for that pair, a verdict for each state relation except `invariant`.
- [ ] No page on the Domino listing contains `Domino_` (`grep -c Domino_` on the generated
      viewers of a test run is 0). The checks are named `state-relation <name>`.
- [ ] Neither page lists `invariant` as a part of `invariant`.
- [ ] The sequential page has the Verdicts section, one assertion block for each check, and a
      model for each failing check. "Copy runnable query" gives a query that cvc5 runs to the
      same answers.
- [ ] The Verdicts section is one piece of shared code, used by both pages.
- [ ] The tactics run still unfolds `Domino_invariant` (test).
- [ ] `pair_view` unit tests: a part on a pair with `invariant` verified is verified; a part with
      its own `fails` verdict is `fails`; a part with no verdict on a pair where `invariant`
      failed is `Inconclusive`.
- [ ] On the EasyCrypt listing, the `invariant` goal contains the package and game invariant
      claims of story 58, and their sub-verdicts appear only on pairs where `invariant` is not
      verified.
- [ ] Screenshots of both pages at 1600×1000 and 800×1000 in the implementation report.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```sh
source ~/.cache/domino/cvc5-lib-env.sh
cargo build -p domino --features cvc5-lib
D=$PWD/target/debug/domino
cd example-projects/hello-world-oracle-rename-new
$D debug --proof Proof --proofstep 0 --oracle ChangeNameUsefulOracle
$D debug --proof Proof --proofstep 0 --oracle ChangeNameUsefulOracle --lockstep
grep -c Domino_ _build/debug/Proof/*/ChangeNameUsefulOracle/!all-claims!/*_viewer.html   # 0
```

Use a project with an inconclusive or failing `invariant` and at least two state relations for the
page checks. If no example project has one, add a small one under `testdata/debug/story21/`.

## 6. Rejected alternatives

- **The bare relation name** for a state-relation check. Rejected: it can look the same as a
  declared claim with that name.
- **Keep `Domino_<name>` on both listings.** Rejected: it breaks the glossary; `Domino_` names an
  EasyCrypt operator.
- **Check every state relation on every pair.** Rejected: one more query for each relation at
  each reachable pair, and a failing helper relation that the invariant does not use is only noise.
- **A flag for "check relations always".** Rejected: no user need.
- **Each strategy keeps its own breakdown loop.** Rejected: the rule in two places, both with the
  dependency defect.
- **Flatten the parts into the claim list with a guard "only if `invariant` failed".** Rejected:
  the order of the list would carry a meaning, and a filter on the list breaks it silently.
- **A check selector as the main view** of the sequential page. Possible later, on top of this.
- **The engine keeps `invariant` in its relation list and the page hides it.** Rejected: one
  solver query for nothing on each failing pair, and the tactics run keeps reading the debug check
  list.
- **Story 58's rule** (one-sided sub-verdicts on every pair, state relations only on failure).
  Rejected: two rules for one list of parts; a part would have to say which rule it follows.

## 7. Notes / risks

- On the EasyCrypt listing, the `invariant` goal becomes larger (story 58's conjuncts). If the
  lockstep time on the story-58 synthetic project grows by more than 20 %, record it in the
  report.
- A declared claim and a state relation with the same name are two separate checks: the claim
  uses its own dependencies, the part uses the invariant's.

## 8. State handed to the next story

Record in `21-…-IMPLEMENTATION-REPORT.md`: the shape of `ClaimQuery.parts` and `PartVerdict`, the
new schema numbers, where the shared Verdicts renderer lives, and the screenshots.
