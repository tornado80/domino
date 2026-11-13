# The EasyCrypt proving algorithm

This document describes what `domino easycrypt prove` does: how it proves each lemma, every
fallback sequence it can enter, and every kind of `admit` it can leave in a proof. It describes
the code in `src/easycrypt/tactics/` and uses the vocabulary of `CONTEXT.md`.

Translation (`domino easycrypt export`) proves nothing. It writes the lemma files, with a
placeholder proof where a proof job will work. Everything below happens after translation.

## 1. The shape of a run

### 1.1 Which lemmas exist

| Lemma | File | Judgement | Tree walked | Proved by |
|---|---|---|---|---|
| Oracle lemma | `Eq_<L>_<R>_<O>.ec` | `equiv[…]`: equal results and `inv` | Joint tree (lockstep execution) | Proof job |
| Side-invariant lemma, game invariants | `SideInv_<C>_<O>.ec` | `hoare[…]` | Side tree (one-sided execution) | Side-invariant job |
| Side-invariant lemma, no game invariants | `SideInv_<C>_<O>.ec` | `hoare[…]` | None | Translation writes the proof; the job checks it |
| Package-invariant lemma | `PkgInv_<V>_<O>.ec` | `hoare[…]`, any imports | Package tree (one-sided execution) | Package-invariant job |
| Frame lemma | `Frame_<V>_<O>.ec` | `hoare[…]` | None | Translation writes the proof; the job checks it |
| Start lemma | `PkgInv_<V>_init.ec`, `SideInvInit_<C>.ec` | `hoare[init : true ==> …]` | None | Job tries two proofs |
| Equivalence glue | `Eq_<L>_<R>.ec` | Joins the lemmas with `conseq` | None | Translation; no job sends it |
| Reduction oracle lemma | `Red_<L>_<R>_<O>.ec` (or `_<O>_L`/`_<O>_R`) | `equiv[…]`: equal results and `inv_<L>_<R>` | None: the blind walk (7.4) from `proc; inline *.`, no lockstep execution, no solver. The reduction walk (§10) replaces it with story 106 | Reduction proof job (`--gamehop` on a reduction hop) |
| Reduction run lemma, proposition lemmas | `Red_<L>_<R>.ec`, `Prop_<name>.ec` | `run_<L>_<R>`, bound lemmas | None | Translation; no `admit` |

An oracle lemma assumes the side invariants of both sides. The glue joins it with the
side-invariant lemmas: `by conseq Eq_X_<O> SideInv_<L>_<O> SideInv_<R>_<O> => /#.` The glue's
induction start is `auto => />; smt(emptyE map_empty).`

### 1.2 Which jobs run

| Options | Jobs |
|---|---|
| `--package P` | The package-invariant job of each variant of `P` |
| `--game C` | The side-invariant job of `C`, if the package lemma files of its packages are on disk |
| `--gamehop N` | The proof job of that equivalence, if the side-invariant files of its compositions are on disk |
| None of these | Every equivalence. A second thread runs the package and side-invariant jobs |

On that second thread, each side-invariant job runs after the package jobs of its composition.
Package jobs that no side job needed run last. "On disk" only asks that the files exist: a file
with admits counts. A missing file gives a warning, and the dependent job does not start.

### 1.3 What each job does with its records

| Records | Without `--force` | With `--force` |
|---|---|---|
| None | Prove | Prove |
| All done | Skip | From scratch |
| Some done | Resume | From scratch |

With `--oracle O` and `--force`, only `O` is proved again. An oracle counts as done when it ended
without an `interrupted` admit, so **admits with any other reason are not retried** without
`--force`.

A skipped package or side job still checks its fixed lemmas when one of their files does not yet
end with the marker `(* EasyCrypt accepted this file. *)`.

### 1.4 One oracle

Up to `--jobs N` workers take oracles in order. Each worker does the following.

1. It takes the oracle's lock. If another job holds it, the oracle is skipped with a message.
2. It re-reads the oracle's record under the lock, in case another job has proved it.
3. It starts a fresh EasyCrypt and sends the lemma file up to `proof.`
4. It runs lockstep or one-sided execution and saves the tree. If the record says `interrupted`
   and the oracle can be resumed, it uses the saved tree instead (section 8).
5. It walks the tree with the prover. After each accepted sentence (the default
   `--write-granularity tactic`) it seals a copy and rewrites the lemma file, its report and its
   record.

Nothing compiles the written file during a run (ADR 0005). Every sentence in it was accepted by
the live session.

### 1.5 Limits and timeouts

| Limit | Default | Scope |
|---|---|---|
| `--ec-timeout` | 60 s | Each sentence |
| Quick close timeout | `min(2 s, --ec-timeout)` | The program-goal quick close only (section 3) |
| Interrupt after a timeout | Resend every 5 s for 30 s | No answer in that time means EasyCrypt is unresponsive |
| `--leaf-budget` | Off | Time to take one leaf apart, from the formula on |
| `--smt-retry-timeout` | Off | The `smt` timeout of one retry. `--ec-timeout` must be at least this plus 10 s |
| Blind walk budget | 64 | Depth of one blind walk path |
| Formula opening | 64 steps | One `open_part` loop |
| Key pairs of a case split | 1 to 6 | More than 6, or none: no split |
| Key pairs of a named split | At most 2 | One-program judgements only |

A sentence that times out comes back `interrupted`. The prover treats that like a refusal: the
attempt is undone and the next fallback runs.

## 2. Rules of the walk

- **Goal contract.** Every routine that handles the front goal leaves that goal closed and every
  other goal as it was. Subgoals are handled front to back, one bullet each.
- **Attempts are undoable.** Each attempt takes a snapshot of the session state, the script and
  the statistics. A rollback restores all of them, including any case admits made inside.
- **The script holds accepted sentences only.** Refused and undone sentences appear only in the
  transcript.
- **Tactics take positions from EasyCrypt** (ADR 0002). The tree supplies decisions only. Counts
  for `sp` and names of sampled variables come from the goal JSON, and subgoals are told apart by
  kind.
- **The tree is not trusted to match.** Each structural step checks the shape that came back: the
  number of goals and their kinds.

## 3. The algorithm

```text
oracle:
    send "proc; inline."
        refused → admit program-mismatch (N0, claim "proc; inline.")
    align the goal with Domino's listing (equivalences only)
    prelude (section 4)
        then prove_node(root)

prove_node(n):
    if resuming and n is a closed node: keep it, done (section 8)

    if every terminal below n fails in Domino: admit domino-fails, done
    if package lemma: send the open calls at the head of the program
    if n is not a terminal pair and n is not an ancestor of the resumed node:
        quick close: "auto => /#." under the short timeout. Closed: done

    match kind of n:
        terminal pair → leaf (section 6)
        stuck         → admit stuck, children are not walked
        unreachable   → "exfalso; smt()."; else admit domino-verified-ec-failed
        otherwise     → structural step (section 5)
                        step did not apply → undo, blind walk (section 7)

child of a node:
    explored      → prove_node(child)
    pruned        → "exfalso; smt()."; else "auto => /#."; else admit
    not explored  → admit domino-inconclusive
```

"Fails in Domino" at a node means this for every terminal below it:

- For an oracle lemma, both `equal-output` and `invariant` fail.
- For a `hoare` lemma, the terminal has claims and every claim fails.

This check comes before everything else at the node, so it takes precedence over `stuck`.

The quick close is not sent on terminal pairs. On a package lemma the open calls are sent first:
each is `sp k.` when needed, then `seq 1 : (#pre); 1: by call (_: true); auto.`

## 4. The prelude

**Oracle lemma.** After `proc; inline.` the prover sends `sp k l.` and `if.` on the router's guard.
It expects a formula and two program goals.

| Bullet | What happens |
|---|---|
| Condition | Side goal, claim `router-condition`, admit reason `router` |
| Guarded body | `prove_node(root)`. With an alignment mismatch, the blind walk instead |
| Both aborted | Quick close, then side goal, claim `both-aborted`, admit reason `router` |

If the prelude does not have that shape, it is undone back to just after `proc; inline.` and the
blind walk runs from there.

**Side-invariant lemma.** The prover sends `sp`, then `if.`, and expects one extra program goal.
The first arm is `prove_node(root)`. The second is quick close, then side goal, claim
`already-aborted`, admit reason `router`. A wrong shape goes to the blind walk.

**Package-invariant lemma.** There is no router: `prove_node(root)` runs directly after
`proc; inline.`

## 5. Structural steps

Every kind except `determined` starts with `sp k l.` (`sp k.` in a `hoare`), counted from the goal
JSON. `determined` skips it, because each `sp` adds existentials that the side goal would have to
reason about.

| Node kind | Sentences | Then |
|---|---|---|
| Determined | For each side that moved alone: `rcondt{i} ^if; 1: auto => /#.` or `rcondf` | The one child |
| Synchronized | `if.` | Condition as side goal, claim `branch-condition`, then both children |
| Split, both sides | `if{1}.`, then in each arm `if{2}.` | Four children. An arm that refuses `if{2}.` is admitted, claim `split` |
| Split, one side | `if{s}.` | Two children |
| Sampling, synchronized | `seq 1 1 : (#pre /\ x{1} = y{2}); 1: <close>.` | The one child |
| Sampling, independent | `seq 1 0 : (#pre); 1: <close>.` or `seq 0 1` | The one child |
| Split in a `hoare` | `if.` | Two children |
| Sampling in a `hoare` | `seq 1 : (#pre); 1: <close>.` | The one child |

`<close>` is tried as `auto => />`, then `auto => /#`, then `auto`.

If a determined node's combined sentence is refused, the prover sends `rcondt{i} ^if.` alone and
treats the extra goal as a side goal, claim `side-goal`. If the combined sentence is accepted but
leaves the goal count changed, the step fails.

A step that fails (refused tactic, wrong number or kind of goals, missing child) returns "did not
apply". The node is undone and goes to the blind walk.

## 6. Leaves

A leaf goes through four stages.

### 6.1 Decide the exit path

For each `if` left in the programs, side 1 first, at most as many times as there are top-level
`if`s:

```text
rcondf{i} ^if; 1: by auto.    or    rcondt{i} ^if; 1: by auto.
```

Domino's prediction goes first. On the router's tail `if (ec_result = None)`, when that side's
terminal is an abort, `rcondt` goes first. Everywhere else `rcondf` goes first. If neither is
accepted, the stage stops and `auto`'s `wp` takes that `if` into the formula.

### 6.2 Reduce to a formula

- `auto => &1 &2 hpre.` for an oracle lemma.
- `auto => &hr hpre /=.` for a `hoare` lemma.

If this fails or leaves a program goal, the **whole leaf is admitted** with the reason from
section 9.3. If it closes the goal, the leaf is done. Otherwise the invariant is unfolded in
`hpre`: `rewrite /inv /… in hpre.` with all operators, and if that is refused, with only the head
operator. Unfolding is best effort, and a failure here does not stop the leaf.

### 6.3 Open the formula into leaf parts

This loop runs at most 64 steps on each goal.

| Goal shape | Sentence | Effect |
|---|---|---|
| Budget spent | None | Admit the part, note `(leaf time budget spent)` |
| `forall` | `move => <names> /=.` | Binders recorded for the key case split |
| `A => B` | `move => hpre<n> /=.` | Premise recorded and invariant unfolded in it |
| `inv …` | `rewrite /inv /=.` | The goal is now the `invariant` part |
| A listed operator | `rewrite /<op> /=.` | The goal becomes that claim's part, if the operator stands for a claim |
| Anything else | `do split.` | Each goal is a bullet, opened again. One goal or a refusal makes a leaf part |

If the part's claim fails in Domino, it is admitted at once as `domino-fails`, with no fallback
tried. A step EasyCrypt refuses ends the loop, and the goal becomes a leaf part.

### 6.4 Close each leaf part

The part fallback sequence is in section 7.2.

## 7. Every fallback sequence

### 7.1 Side goals

Side goals are branch conditions, the side goals of `rcondt`, and router goals. The order is:

| # | Sentence | Notes |
|---|---|---|
| Quick close | `auto => /#.` | Under the **full** sentence timeout |
| Reduce | `move => &m.` or `auto.` | Up to 4 times, to bring the goal to a plain formula. Not a closing attempt |
| 1. Crush | `move=> /> <binders> *; smt().` | Needs `forall …, A => B` |
| 2. Unfolded | `move => <binders> hpre.`, unfold in `hpre`, `smt().` | Needs a premise |
| 3. Hints | `smt(<hints>).` | On the goal as it stands |
| 4. Pruned crush | `move=> /> <binders>.`, then `move=> x0 h0 _ h1; move: x0 h0 h1; smt().` | Side-invariant premises become `_`. The rest go back into the goal |
| 5. Invariant selection | Opens the side invariant and keeps conjuncts that share a table with the conclusion | Runs on the goal fallback 4 opened |
| Admit | `router` for the prelude, otherwise `domino-verified-ec-failed` | |

The `<hints>` are `get_setE mem_set remE mem_rem emptyE`, then the project's `[easycrypt]
smt_hints`.

A fallback that needs a premise sends nothing on a goal without one. Fallback 5 applies only when
the conclusion reads a memory that a side-invariant premise reads, the abort premise of that
memory is present, and some conjunct's footprint meets the conclusion's tables. Package-invariant
jobs have no side invariants to drop, so fallback 4 drops nothing and fallback 5 never applies.

The side goal sequence has no timeout retry and no leaf budget.

### 7.2 Leaf parts

| # | Sentence |
|---|---|
| 1 | `smt().` |
| 2 | `smt(<hints>).` |
| 3 | `move: <premises> => />; smt(<hints>).` |
| Retry of 3 | `move: <premises> => />; smt timeout=<t> wantedlemmas=(<hints>).` |
| 4 | Key case split, section 7.3 |
| Admit | Reason from section 9.3, with the last `smt` outcome |

Fallback 3 is skipped when there are no premises to move, but every leaf has at least `hpre`, so
in practice it always runs. The retry runs only with `--smt-retry-timeout`, only after fallback 3
failed with `smt: timeout`, and only while the leaf budget lasts.

The leaf budget is checked in the opening loop, before the retry, before a named split and before
each case. It is not checked between fallbacks 1 to 3.

### 7.3 The key case split

It finds pairs `(index, key)`: a read `m.[b]` or a membership test `b \in m` on an updated map,
where `b` is a binder the leaf introduced or a printable term over one, with each atom key written
into the map. It runs only with 1 to 6 pairs.

1. **Merge.** For two keys of one index, it sends
   `have hk : k = k' by move: <premises> => />.` An accepted `have` stays in the context and drops
   the second pair.
2. **Named split**, `hoare` lemmas only, at most 2 pairs, budget not spent:
   `case (i1 = k1) => hc; case (i2 = k2) => hc1; smt(<hints>).` It is never retried.
3. **Cases.** One `case` per pair, each arm a bullet. A binder index uses `case (b = k) => [->>|?].`
   and the equal arm drops the other pairs of that binder. A term index uses
   `case (t = k) => [hc|hc].`
4. **Each case** is closed with `move: <premises> => />; smt(<hints>).`, then the retry. If that
   fails, or the budget is spent, the case alone is admitted with a note `(case i = k, j <> l)`.

The split is kept when at least one case closed. If none closed, or EasyCrypt refused a `case`,
everything is undone, merges and case admits included, and the part is admitted whole.

### 7.4 The blind walk

The blind walk (`prove_blind`) is used when the tree cannot be followed. It reads only EasyCrypt's
program heads. On each goal it tries, in order:

1. Budget used up, or the front goal is no program goal: admit `program-mismatch`.
2. Quick close, under the short timeout.
3. `sp`. Refused: admit `program-mismatch`.
4. On a one-program judgement: an empty program goes to the leaf procedure, anything else is
   admitted `program-mismatch`. There is no trial procedure for one program.
5. Both programs empty: the leaf procedure, with no pair known.
6. For a side at an `if`, side 1 first: `rcondt{i} ^if; 1: auto => /#.`, then `rcondf`.
7. Both at `if`: `if.`, condition as side goal, then both arms.
8. For a side at an `if`: `if{1}.`, then `if{2}.`, each with both arms.
9. Samplings: `seq 1 1 : (#pre /\ x{1} = y{2}); 1: auto => /#.`, or `seq 1 0`, or `seq 0 1`.
10. Otherwise: admit `program-mismatch`.

### 7.5 All the other fallback points

| Where | Sequence |
|---|---|
| Node step does not apply | Undo, blind walk |
| Router prelude has the wrong shape | Undo to after `proc; inline.`, blind walk |
| Alignment mismatch | Condition closes normally, blind walk on the guarded body |
| Determined node | Combined `rcond`, then plain `rcond` and a side goal, then blind walk |
| Sampling | `auto => />`, `auto => /#`, `auto`, then blind walk |
| Exit `if` | Predicted decision, other decision, leave it to `auto` |
| Unfolding a premise | All operators, head operator, nothing |
| Unreachable node | Quick close, `exfalso; smt().`, admit |
| Pruned combination | `exfalso; smt().`, `auto => /#.`, admit |
| Start lemma | `+ proc; auto => /#.`, then `+ proc; inline; auto => />; smt(<hints>).`, each in a fresh EasyCrypt, then the admitted proof |
| Frame lemma, or a side-invariant lemma with no game invariants | As translation wrote it, then `admit.` |
| Resume, `replay` | Replay the node's script. A refusal or an open goal undoes it, and the node is proved live |
| Resume cannot start | Proved from scratch with lockstep execution (section 8) |
| Unknown admit in a closed node | The node is proved again |
| EasyCrypt leaves an interrupt unanswered | Seal the oracle, go on with a fresh EasyCrypt. The third such event in a job ends the job |

## 8. Resuming and stopping

**Seal.** A seal copies the script and closes each open goal of the oracle with `admit.`, reason
`interrupted`, claim `open-goal`. It sends nothing to EasyCrypt. It is what each write puts on
disk while an oracle runs, and what remains after a Ctrl-C, an unanswered interrupt, or a kill.

**Resume modes** apply to an oracle whose record says `interrupted`.

| Mode | Closed nodes | Lockstep |
|---|---|---|
| `trust` (default) | Goal closed with `admit.` in the live session. The recorded script goes into the file, unchecked | Saved tree |
| `replay` | Recorded script is sent again | Saved tree |
| `restart` | Everything is proved again | Run again |

The in-flight node is proved from its start. Its ancestors skip the quick close, because the
earlier job already got past it.

An oracle starts from scratch, with a warning, when its record is older than version 3, its saved
tree is missing or unreadable, the tree is another oracle's, or the tree's id is not the one its
closed nodes were proved on. A tree whose fingerprint no longer matches is **still used**, with a
warning.

**Conditions that end the run with an error** rather than an admit:

- The lemma cannot be opened up to `proof.`
- EasyCrypt closes, or gives an answer that cannot be read.
- EasyCrypt refuses `admit.`, which means the walk has lost track of its goals.
- A proof file cannot be written.

## 9. Every kind of admit

### 9.1 Labelled admits in a walked proof

Each one has a comment such as:

```text
admit. (* domino: J7 StateRelation_rel; domino-verified-ec-failed; smt: timeout *)
```

The fields are the id, the claim, the reason, then `Domino: <view>` for the four reasons that do
not state a view, then the `smt` outcome when a part fallback ran. The ids are `J<n>` (joint
path), `S<n>` (stuck point), `N<n>` (node), or `router`.

| Reason | Meaning |
|---|---|
| `stuck` | Lockstep could not give EasyCrypt a step for a sampling |
| `domino-fails` | Domino refutes the claim, so EasyCrypt was not asked, or could not prove it |
| `domino-inconclusive` | Domino could not decide, and EasyCrypt did not close it |
| `domino-verified-ec-failed` | Domino decided it, and EasyCrypt did not close it |
| `program-mismatch` | EasyCrypt's program did not match, and the blind walk found nothing |
| `seq-post` | A synchronized sampling had assignments before it after `sp` |
| `router` | A goal of the router prelude |
| `interrupted` | A goal still open when the oracle was sealed |

### 9.2 Every place each reason is emitted

| Reason | Site | Id | Claim | Domino view |
|---|---|---|---|---|
| `stuck` | Stuck node, after the checks of section 3. Covers its whole subtree | `S<n>` or `N<n>` | `stuck/partner-not-at-head`, `stuck/pairing-sat-not-valid`, `stuck/pairing-unknown`, `stuck/no-partner-reachable`, or `stuck` | Worst below |
| `domino-fails` | Every terminal below the node fails | First pair | `equal-output+invariant`, `side-invariant`, `package-invariant` | Fails |
| `domino-fails` | A part's claim fails while opening | Pair | The part | Fails |
| `domino-fails` | Section 9.3, after fallbacks | Pair | The part or leaf | Fails |
| `domino-inconclusive` | Section 9.3, after fallbacks | Pair, or `N<n>` | The part or leaf | Inconclusive |
| `domino-inconclusive` | A child not explored | `N<parent>` | `not-explored` | Inconclusive |
| `domino-verified-ec-failed` | Section 9.3, after fallbacks | Pair | The part or leaf | Verified |
| `domino-verified-ec-failed` | Side goal outside the prelude | A pair below | `side-goal`, `branch-condition` | Verified, fixed |
| `domino-verified-ec-failed` | Unreachable node | `N<n>` | `unreachable` | Verified, fixed |
| `domino-verified-ec-failed` | Pruned combination | `N<parent>` | `pruned-combination` | Verified, fixed |
| `program-mismatch` | `proc; inline.` refused | `N0` | `proc; inline.` | n/a |
| `program-mismatch` | Blind walk ran out of options | `N<n>` | `program` | Inconclusive |
| `seq-post` | Synchronized sampling after `sp` | A pair below | `sampling` | Verified, fixed |
| `router` | Prelude side goal | `router` | `router-condition`, `both-aborted`, `already-aborted` | n/a |
| `interrupted` | The seal | `N<n>` or `router` | `open-goal` | n/a |

"Fixed" means the code writes `Verified` without reading a verdict for that exact formula. It
means Domino decided that branch or combination under its assumptions, not that the solver
checked the formula EasyCrypt showed.

Two cases are defensive. `not-explored` needs a tree from a stopped or path-limited run, and a
`prove` run sets no path limit and does not walk a stopped tree. `seq-post` needs EasyCrypt to
leave an assignment at the head right after `sp`.

### 9.3 How the reason of an EasyCrypt failure is chosen

A leaf or part that EasyCrypt could not close takes its reason from Domino's view of it:

| View | Reason |
|---|---|
| Fails | `domino-fails` |
| Verified | `domino-verified-ec-failed` |
| Inconclusive, or not applicable | `domino-inconclusive` |

The view comes from one of three sources.

- **With a known pair, on an oracle lemma**, `Part::EqualOutput` and `Part::Invariant` read their
  own verdict. A state relation or side invariant reads the verdict of `invariant` if that is
  verified or unreachable, otherwise its own part verdict, or inconclusive if it has none. A whole
  leaf is the worse of `equal-output` and `invariant`.
- **With a known pair, on a `hoare` lemma**, a side-invariant part reads its own claim, or is
  inconclusive without one. Any other part is the worst of all claims.
- **With no known pair**, as in a blind-walk leaf, a leaf that does not reduce, or an arm that
  refuses `if{2}.`, it is the worst view over every pair below the node. It is inconclusive when
  there are none.

An `unreachable` verdict counts as verified. There are two notes that can follow the claim, and
neither is a reason of its own: `(leaf time budget spent)` and `(case …)`.

### 9.4 Admits without a label

| Admit | When | Report says |
|---|---|---|
| `+ proc; inline. admit.` from translation | The lemma was not reached: stopped before it, job ended early, lock held, or not selected by `--oracle` | The oracle is absent or pending |
| `+ proc; inline. admit.` from translation | Lockstep or one-sided execution failed | `no tactics (…)`. It is not counted in the oracle's admits |
| `admit.` as the whole proof | EasyCrypt refused a frame lemma or a side-invariant lemma as translation wrote it | `admitted (the proof translation wrote was refused: …)` |
| Admitted start lemma | Both start proofs refused | `admitted (claims …; Domino: the start check …; last refusal: …)` |

The start lemma placeholders are in `PkgInv_<V>_init.ec` and `SideInvInit_<C>.ec`. The bullet of
game invariants in `SideInv_<C>_<O>.ec` starts as the same placeholder.

Export reports `admit_count == oracle_count` for an equivalence, one placeholder for each oracle.

### 9.5 Admits that never reach the proof file

These are sent to the live EasyCrypt only:

- A closed node under `--resume trust`. The file gets the node's recorded script.
- The oracle's goal when lockstep or one-sided execution failed.
- `domino easycrypt check-alignment`, which admits each goal after comparing it. This is a separate
  command, not part of `prove`.

### 9.6 What is not an admit but is still a gap

- **Open hops.** A conjecture, or an equivalence with no translated file, adds the adversary's own
  advantage as a term of the proposition lemma.
- **Hybrid hops.** A proposition whose path has one gets no lemma file.
- **Project lemmas** are never translated. The EasyCrypt listing checks only `equal-output` and
  `invariant`, with no project lemmas.
- **The `admit` modifier on a claim in a Domino theorem** belongs to Domino's own checks. It is
  separate from EasyCrypt admits.
- **Propositions are only as strong as their parts.** A proposition file has no `admit`, but the
  oracle files it depends on can have them.
- **The glue is not checked by a proof job.** A problem in `Eq_<L>_<R>.ec` appears only when you
  compile it.

## 10. The reduction walk

**Status:** designed, not built. Epic `docs/stories/easycrypt/epic-the-reduction-walk.md`
(stories 104–107), ADR 0024. Until story 106 is done, a reduction's oracle lemma is proved by the
blind walk (§7.4). Story 106 removes this status line and updates §1.1, §1.5, §9.1 and §9.2.

The reduction walk proves a reduction's oracle lemma
`equiv[Game_<L>.<O> ~ Red_<L>_<R>(<A>.Game_<A>).<O> : ={arg} /\ inv ==> ={res} /\ inv]`. It uses
no joint tree and no solver. It depends on one fact: **both sides run the same code**, except that
the right side has, around each call that the reduction router forwards to the assumption game:

- the **assumption guard** `if (!<A>.Game_<C>.abort_flag) { … }`;
- copies of the arguments and the results (assignments);
- the assumption game's **tail branch** `if (<r> = None) { <A>.Game_<C>.abort_flag <- true; }`.

The invariant `game_abort = red_abort /\ (assm_abort => red_abort) /\ (equal states)` makes the first
assumption guard of an oracle true. A later guard of the same oracle is true because the reduction
code makes the next forwarded call only on the path where the earlier results were values.

The walk reads the shape of each program head from EasyCrypt's goal JSON (ADR 0002) and sends the
one step that the shape calls for. It never searches. A shape that it does not expect is a
**mismatch**: that goal is admitted and the walk goes on with the other open goals.

### 10.1 The algorithm

```text
oracle:
    send "proc; inline *."
        refused → admit program-mismatch (N0, claim "proc; inline *.")
    A := the theory of the reduction's assumption composition
    walk("R", arm_start = true)

walk(path, arm_start):
    if arm_start:
        quick close "auto => /#." under the short timeout. Closed: done
    sp_front                                       -- "sp k l." with the counts of the goal
    (l, r) := the first statements of the left and the right program
    match classify(l, r, A):                       -- §10.2, first matching rule wins

        Leaf →                                     -- both programs empty
            quick close "auto => /#." (unless arm_start already tried it). Closed: done
            leaf procedure with no pair (§6); a part that fails → admit reduction-ec-failed

        AssumptionGuard →
            step("rcondt{2} ^if.", claim "assumption-guard")
            walk(path, false)

        TailBranch →
            for (d, close) in [(rcondf, />), (rcondf, /#), (rcondt, />), (rcondt, /#)]:
                accepted "d{2} ^if; 1: auto => close." → walk(path, false), done
            step("rcondt{2} ^if.", claim "tail-branch")   -- full side-goal sequence, last try
                refused → admit reduction-mismatch (path, "undecided-tail-branch"), done
            walk(path, false)

        ExitGuards →                               -- both heads are exit guards
            for side in [1, 2]:
                for d in exit_decisions(cond of side), for close in [/>, /#]:
                    accepted "d{side} ^if; 1: auto => close." → next side
                not decided → undo both sides, go to Branches
            walk(path, false)

        Branches →                                 -- both heads are if
            step("if.", claim "if-conditions")     -- leaves the then arm and the else arm
            + walk(path + ".t", true)
            + walk(path + ".e", true)

        Samplings(x, y) →
            x{1} or y{2} in #pre (§10.3) → admit seq-post (path, "sampling: x{1} in #pre"), done
            step("seq 1 1 : (#pre /\ x{1} = y{2}).", claim "seq-coupling")
            walk(path, false)

        Mismatch(m) →
            admit reduction-mismatch (path, claim of m), done

step(tactic, claim):                               -- the shape is right: only its side goal is open
    send tactic
        refused → admit reduction-mismatch (path, claim), stop this goal
    side goal (the first new goal):
        "auto => />."                    closed: done
        close_side_goal: quick close, then the fallback sequence of §7.1
        nothing closed → admit reduction-ec-failed (path, claim)
    the program goal continues
```

The walk ends: each step removes at least one statement or splits a goal into two smaller ones,
and a loop is a mismatch. So it has no step budget.

### 10.2 The shapes

The walk classifies the first statement of each side after `sp`. The first rule that matches wins.

| Order | Left head | Right head | Shape |
|---|---|---|---|
| 1 | none | none | `Leaf` |
| 2 | any | assumption guard of `<A>` | `AssumptionGuard` |
| 3 | any | tail branch of `<A>` | `TailBranch` |
| 4, 5 | `while` | any (or the other way) | mismatch `loop` |
| 6 | exit guard | exit guard | `ExitGuards` |
| 7 | `if` | `if` | `Branches` |
| 8 | `rnd` x | `rnd` y | `Samplings(x, y)` |
| 9 | `if` | not `if` | mismatch `left-only-if` |
| 10 | not `if` | `if` | mismatch `right-only-if` |
| 11 | `rnd` | not `rnd` (or the other way) | mismatch `one-sided-sampling` |
| 12 | anything else | | mismatch `heads <left kind>/<right kind>` |

- **Assumption guard:** an `if` whose condition is `!<A>.Game_<C>.abort_flag`.
- **Tail branch of `<A>`:** an `if` whose condition is `<r> = None…`, whose *then* block is only
  `<A>.Game_<C>.abort_flag <- true`, and whose *else* block is empty. The reduction router's own tail
  branch sets `Red_<L>_<R>.abort_flag`, so it is not one; it is an exit guard on both sides.
- **Exit guard:** an `if` whose condition reads only translation locals (`ec_…`), abort flags,
  `None`, `true` and `false`. A package variable makes it a real decision, for example
  `key0 <> None` in the MAC package.

EasyCrypt gives a condition as printed text only (`cond.pp`), so the rules read that text.

### 10.3 A sampled variable in `#pre`

EasyCrypt renames an inlined local only when its name clashes. A variable that the code samples into
again (an argument, an assigned local, or a state field) keeps its name. Then
`seq 1 1 : (#pre /\ x{1} = y{2})` asks for a `#pre` that the sampling made false. Before it sends the
`seq`, the walk checks `#pre` for `x` in memory `&1` and `y` in memory `&2`: the variable itself, or
for a state field `M.x`, `glob M`. If it finds one, it admits `seq-post` and sends no `seq`. The
equivalence path (§5, synchronized sampling) runs the same check.

### 10.4 Admits

| Reason | When | Id | Claim | Domino view |
|---|---|---|---|---|
| `reduction-mismatch` | A shape of §10.2 that the walk does not expect; a structural tactic that EasyCrypt refuses; a tail branch that no direction decides | Arm path, `R`, `R.t`, `R.t.e` | `left-only-if`, `right-only-if`, `one-sided-sampling`, `loop`, `heads <k>/<k>`, `undecided-tail-branch`, or the step's claim | n/a |
| `reduction-ec-failed` | A side goal of a correct step, or a leaf part, that nothing closed | Arm path | `assumption-guard`, `tail-branch`, `if-conditions`, `seq-coupling`, `leaf`, or the leaf part | n/a |
| `seq-post` | §10.3 | Arm path | `sampling: <x>{<side>} in #pre` | n/a |

A `reduction-mismatch` tells you that the code does not have the shape of a reduction: look at the
translation or at the packages. A `reduction-ec-failed` tells you that the shape is right and the
proof needs work: try the goal with `easycrypt llm -upto`.

Example comment: `admit. (* domino: R.t.e left-only-if; reduction-mismatch *)`.

### 10.5 What the walk writes

For `Red_H7_1_H7_0_Send2`, the start of the proof is expected to look like this. A step and its side
goal are two sentences; each side goal is a bullet. The closer in a bullet is the first one that
EasyCrypt accepts. The closers below are expected, not measured (story 107 measures them).

```text
proc; inline *.
sp 1 1.
if.                                      (router guards: exit guards, not decided → Branches)
+ auto => />.                            (if-conditions)
+ sp 3 3.                                (then arm: neither game aborted)
  …
  seq 1 1 : (#pre /\ ni1{1} = ni1{2}).   (the nonce)
  + auto => />.                          (seq-coupling)
  + …
    rcondt{2} ^if.                       (assumption guard around Init)
    + auto => /#.                        (assumption-guard: needs the invariant)
    + …
+ auto => /#.                            (else arm: both games aborted, quick close)
```
