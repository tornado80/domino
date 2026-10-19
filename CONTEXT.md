# Context

The shared vocabulary of this repository. Glossary only — no implementation details, no plans.
When a term here conflicts with how a document or a piece of code uses a word, this file wins.

## Domino core

**Package** — a reusable unit of stateful code: parameters, state fields, imported oracle
signatures and oracle definitions. A package is a *template*; it is never used directly.

**Package parameter** — a value a package is instantiated with. Three kinds: booleans
(see *idealization bit*), integers, and functions.

**Package instance** — a package with all of its parameters bound, living inside one composition
under an instance name. By the time a proof runs, an instance's code has been rewritten so that
every parameter and type is substituted: an instance is *monomorphic*.

**Package state** — the state fields of a package instance, and nothing else: an instance's
parameters are bound once and are not part of its state. Two instances have *equal state* when
their state fields are equal; their parameters are not compared.

**Composition** (also **game**) — a set of package instances plus the call graph wiring them
together, and the list of oracles it exports to the adversary. The call graph is **acyclic**, and an
oracle cannot call another oracle of its own package, so a call can never re-enter the package it
came from. Package instances do **not** share state: an oracle can only write its own instance's
state fields. (The SMT encoding collects all of a game's state into one datatype; that is an
encoding convenience, not shared ownership.)

**Game instance** — a composition with its game constants bound, named in a theorem. Several game
instances can share one composition and differ only in the constants they bind.

**Theorem constant** — a value declared at theorem level and passed down into game instances and
from there into package instances. Boolean, integer or function.

**Oracle** — a procedure a package defines. An **exported oracle** is one the composition offers
to the adversary.

**Continuation** — the statements that follow a given statement in the same block, together with
everything that follows the blocks enclosing it. What a mid-body abort or return skips.

**Abort** — an oracle ending without a value: an explicit `abort`, an `assert` whose condition is
false, or unwrapping a `None`. An abort is not an error; it is a run of the game in which the
adversary loses its ability to query further. Abort **cascades**: a caller whose callee aborted
aborts too, and once a game has aborted no later query does anything.

**Table write** — an assignment that sets one entry of a table to a `Maybe` value: `Some v` stores
`v`, and `None` removes the entry. When the value is not known to be `Some` or `None`, the choice
between storing and removing is a real decision of the oracle.
_Distinguish_: an **exit guard**, which decides nothing.

**Idealization bit** — a boolean parameter that selects between a real and an idealized behaviour
of a package. Related instances usually differ only in these bits.

**Equivalence** — a proof step claiming two game instances are perfectly indistinguishable. Its
obligations are discharged per exported oracle.

**Claim** — one obligation of an equivalence for one oracle: `invariant`, `same-output` or
`equal-aborts`, each with its dependencies.

**Dependency** — a fact a claim is proved *under*: it is assumed, together with the shared
assumptions, before the claim's negated goal is checked. A dependency is a built-in fact
(`no-abort`, `left-no-abort`, `right-no-abort`, `equal-aborts`), another claim, or a project lemma.

**Claim kind** — what a claim or dependency name stands for: a built-in fact, a state relation, a
project lemma, or a package or game invariant. The kind comes from what the name is declared as —
built in, or a definition in the project's SMT-LIB files — and never from how the name is spelled.
A name that is declared as none of these is an error, not a guess.
_Avoid_: claim type guessed from a name prefix (`relation…`, `invariant…`).

**Project lemma** — a lemma hand-written in the project's SMT-LIB file and named in a proofstep's
`lemmas` block, declared with `define-lemma`. It is never translated to EasyCrypt.
_Distinguish_: the built-in facts above, which are a claim kind of their own, not lemmas.

**State relation** — a predicate over the left and right game states, hand-written in SMT-LIB, that
an equivalence maintains. One set of state relations per equivalence.

**Invariant** — the state relation named `invariant`: the one, and only, relation assumed to hold
on the states before every oracle call. Every other state relation is a claim to prove or a helper
the invariant calls; it is assumed only as far as the invariant includes it. Every equivalence has
exactly one. _Distinguish_: **state relation** (any of them).

**Randomness mapping** — a per-oracle predicate, hand-written in SMT-LIB or chosen by name, that
says which left sampling draws the same value as which right sampling. It may depend on the state
and the oracle's arguments, so whether two particular samplings are paired is a question for the
solver, not something read off the mapping's text.

**Package invariant** — a named predicate over the state of one package, hand-written in SMT-LIB
and declared by the package template. A package may declare several; each is a claim of its own,
known by its name and its package. It applies to every instance of the package, in every game
instance that contains one. Domino assumes it before every oracle call and proves that every oracle
call that does not abort keeps it.

**Game invariant** — a named predicate over the state of one game instance, hand-written in SMT-LIB
and declared by its composition. A composition may declare several; each is a claim of its own. It
applies to every game instance of that composition. Domino assumes
and proves it the same way as a package invariant.
_Distinguish_: **state relation** and **invariant**. Those relate the two sides of an equivalence. A
package invariant or a game invariant is about **one side** only.

## Debugging

**Strategy** — how the debugger walks two oracles: *sequential exploration* or *lockstep
execution*. Independent of the **listing** it walks them on.

**Listing** — the code the debugger executes and labels: the Domino code, or the EasyCrypt code the
export produces. `domino debug` walks the Domino listing; the EasyCrypt listing is reached through
`domino easycrypt export`.

**Trivial branch** — a branch whose condition is `true` or `false` once the constants known to the
listing are put in: the game instance's constants for a lockstep run or `domino inline`, only
literals where parameters are free. It decides nothing on any path.

**Folded listing** — a listing shown with its trivial branches removed: a branch that is always
`false` disappears, and one that is always `true` is replaced by its body. It is another view of the
same code, not other code: the debugger always executes the full listing, and every line of the
folded listing points back to the line of the full listing it comes from.
_Distinguish_: an **exit guard**, which is not trivial and is never folded away.

**Early return** — a `return` in an inlined oracle that can run before the oracle's last statement.
A listing shows it as a jump to a label right after the inlined body, so that the code it skips does
not read as if it runs.

**Sequential exploration** — the strategy that takes every path of the left oracle, then, under
each, every path of the right oracle.

**Lockstep execution** — the strategy in which both oracles advance together, each over its
straight-line code up to its next *decision point*, and the two decision points are then resolved
jointly. It is what an EasyCrypt pRHL proof does, which is why it exists.
_Avoid_: synchronized execution (the word *synchronized* is reserved for the outcomes below).

**One-sided execution** — the debugger's walk of one oracle on its own, with its parameters left
free. Of a composition's oracle it builds a **side tree** and checks the composition's game
invariants on each path. Of a package's oracle it builds a **package tree** and checks the
package's invariants on each path; every call the package makes to its imports is an *open call*.
It is not a strategy, because a strategy walks two oracles; it is what a hoare proof of a
side-invariant lemma or a package-invariant lemma follows, the way an equivalence's proof follows
the joint tree.

**Open call** — a call from a package to one of its imports when nothing is known about who
provides it: it may abort, or return any value of its type, and it cannot touch the calling
package's state. Each call site has its own unknown outcome, independent of every other call
site, so two calls of the same import may return different values. The solver check of a package
invariant, the package tree and the package-invariant lemma all see an import this way.
_Avoid_: virtual package (an earlier model of the same freedom as a stateful stand-in package).

**All-claim run** — a debugger run that names no claim and therefore checks the oracle's whole
obligation set — its proof tree plus the generated package and game invariant claims — on one
shared exploration.
_Avoid_: claim-free run, full-obligation run.

**Core claim set** — the claims a debugger run checks when project lemmas are left out:
`equal-aborts`, `same-output`, `invariant`, and the package and game invariant claims, each under
its built-in dependencies only. It is close to what an EasyCrypt proof can use, since EasyCrypt has
no project lemmas. _Distinguish_: the **obligation set** (every claim, every dependency) and the
EasyCrypt listing's two checks, `equal-output` and `invariant`, with no dependencies at all.

**Check** — one question the debugger asks the solver at one terminal pair, with its own verdict:
the negated goal of one claim, or of one state relation other than the invariant. Every claim of
the obligation set is a check; so is every state relation except `invariant`, because the
`invariant` claim already is that check. A state relation is checked only at a pair where the
`invariant` check is neither verified nor unreachable, and on the invariant's own dependencies: it
says *which part* of a failing invariant fails. On the Domino listing a state relation's check is
called `state-relation <name>`; the EasyCrypt operator names (`StateRelation_<name>`) belong to
the EasyCrypt listing only.
_Avoid_: query (a check may take several solver queries), EasyCrypt operator names on the Domino
listing.

**Debug index** — a page that lists every debugger run on disk below one level: a proofstep, a
theorem, or the project. It shows what is on disk, not what the last run did, so a narrower rerun
updates its rows and never removes the others. An index exists only at a level the user has run
the debugger at. _Avoid_: sweep index, global index.

**Result record** — the small file (`<strategy>_result.json`) that one debugger run writes next to
its viewer: what a row of a debug index needs, and nothing more. A run artifact. A debug index
reads only result records. _Avoid_: run summary (that is `summary.txt`), trace.

**Unreachable** — a verdict meaning a claim was not refuted because the situation it was checked in
cannot arise *under the assumptions in force*. Either the path pair itself is infeasible, or the
pair happens but this one claim's dependency is false on it. It is never a synonym for *verified*:
telling the two apart is what stops an all-green run from being mistaken for a proof.

**Decision point** — where one side of a lockstep execution cannot continue as straight-line
code: a branch, a sampling, or the end of the oracle.

**Waiting side** — a side of lockstep execution that has reached the end of its oracle while the
other side still has decision points to resolve. It stands at its return until both sides end.

**Synchronized branch** — both sides at a branch whose conditions are equivalent under the path
condition and the assumptions, so both take *then* or both take *else*. A branch that is not
synchronized is **split**: every combination of the two sides' outcomes is considered, and the
infeasible ones are pruned. A branch on one side only is always split.

**Synchronized sampling** — both sides at a sampling that the randomness mapping, under the path
condition, forces to draw equal values. A sampling the mapping relates to nothing on the other side
is an **independent sampling** and is consumed on its side alone.

**Stuck point** — a place on a joint path where lockstep execution cannot hand EasyCrypt a proof
step: a paired sampling reached on one side before its partner, or a sampling whose pairing the
solver cannot decide under the path condition. The proof admits it; the execution carries on past
it with Domino's randomness semantics, so the paths below still get verdicts.

**Joint path** — one path of a lockstep execution: the sequence of joint decisions from the start
of both oracles to a pair of terminals.

**Exit guard** — a branch that exists in the EasyCrypt code only because EasyCrypt allows one
exit point, and whose only job is to skip code after something earlier already returned or
aborted. Three kinds: the **done-flag guard**, the **call-result guard** on an inlined call's
result, and the router's **abort-flag guard**. It decides nothing Domino would call a decision, but
an EasyCrypt proof has to step over it like any other branch.
_Avoid_: plumbing branch, plumbing node.

**Exit path** — the exit guards and the router's tail branch that are still in a leaf's EasyCrypt
programs after lockstep execution has stopped. Each of them has only one way it can go, so a proof
decides each one before it reasons about the leaf's postcondition.

**Decision skeleton** — a program with its straight-line code erased: the tree of its branches,
samplings and ends. Two programs that differ only in assignments have the same skeleton.

**Alignment** — matching the decision skeleton EasyCrypt shows for an oracle with the one lockstep
execution walks, so that each EasyCrypt proof step can be tied to a joint decision. Where the two
disagree there is a **mismatch**.

**Equal-output** — the claim, checked in EasyCrypt mode, that both oracles produce the same result
where an abort counts as a result: *same-output* and *equal-aborts* together, with *no-abort* not
assumed. It is EasyCrypt's `={res}` on an optional result, and is never declared in a project.

## EasyCrypt export

**Package variant** — one EasyCrypt module generated for a package, specialised to a distinct
assignment of the parameters that are baked into its code: the integers used as *Bits* widths and
the function parameters. Two package instances that agree on those share one variant. Boolean and
value-integer parameters do not distinguish variants (they are initialization arguments), and
neither does *how an instance is wired* — a package's variant is a fact about the package, never
about the composition it appears in.

**Import interface** — the module type a package declares for the oracles it expects, named by the
package's *own* import names. It lives with the package, so a package never refers to the interface
of whatever happens to serve it.

**Import adapter** — a module belonging to one composition that satisfies one package instance's
import interface by forwarding each expected oracle to the instance that provides it. It exists
because a package may import from several instances at once, and because a composition may rename
an oracle on the way in. It holds no state and is generated only when a single instance cannot
serve the interface as it stands.

**Instance clone** — an EasyCrypt theory clone of a package variant, one per package instance, so
that each instance has its own memory. Instances of the same variant differ only by their clone.

**Router** — the EasyCrypt module generated for a composition. It owns the *abort flag*, exposes the
composition's exported oracles, and forwards each to the package instance that defines it. Packages
themselves carry no abort flag.

**Abort flag** — the router's single piece of state, recording that the game has aborted. It is the
EasyCrypt counterpart of Domino's abort cascade: while it is set, every oracle returns `None`.

**Done flag** — a *per-oracle local*, distinct from the router's abort flag, recording that this
oracle has already aborted or returned. EasyCrypt allows only one exit point, so an oracle's
continuation cannot be skipped by returning early; it is skipped by being guarded on this flag
instead. An oracle whose continuation is never at risk carries no done flag.

**Experiment** — the EasyCrypt module that initializes a router with a game instance's constants and
runs the adversary against it. One per composition; the constants are its `run` arguments.

**Game interface** — the EasyCrypt module type listing the oracles a router exposes to the
adversary. Compositions exporting the same signatures share one.

**Game-state record** — a record type for one game instance: one field per package instance with
state, holding that package's state record (`<Pkg>_pkgstate`, shared by every instance of the
package), then one field per package parameter that becomes a module variable, then its abort flag
(ADR 0007). It exists solely so that invariant operators take a single argument per side; no
router or package ever uses it.

**`StateRelation_` operator** — an EasyCrypt operator translated from a hand-written SMT-LIB state
relation, named after its SMT original; the invariant becomes `StateRelation_invariant`. Only these
are read as state-relation parts of a leaf. _Avoid_: `Domino_` operator (the old name, which also
covered helpers).

**`Helper_` operator** — an EasyCrypt operator translated from a hand-written SMT-LIB helper
function: a function of the invariant file that is not a state relation. Package and game
invariants become `PkgInv_` and `GameInv_` operators, neither `StateRelation_` nor `Helper_`.

**Translation** — producing the export tree from a Domino theorem: the package variants, games,
types, invariants and one proof skeleton per equivalence. Translation proves nothing and talks to
no EasyCrypt. It is what the `export` subcommand does: "export" names the command, never the
concept. _Avoid_: export (as a noun for the concept), proof translation.

**Stage** — one command-level step of an EasyCrypt command: translation, lockstep execution,
proving, report. A stage is not an export **phase**, which is a step *inside* translation.
_Avoid_: phase (for a stage).

**Proof job** — proving one equivalence (optionally only some of its oracles) against the files
translation left on disk. A proof job trusts that a file with the expected name is what translation
would have written, and never rewrites a file that belongs to translation or to another oracle,
which is what lets several proof jobs of one theorem run at once. Two proof jobs never work on the
same oracle at the same time: the oracle is the unit of parallelism, inside one proof job as well as
between proof jobs.

**Oracle lemma** — the proof that one oracle of an equivalence keeps equal outputs and the
invariant, as a lemma of its own in a file of its own. It assumes the side invariants of both sides
but does not prove them. The equivalence's own proof only joins its oracle lemmas with the
side-invariant lemmas of its two compositions; it proves no oracle itself.

**Side-invariant lemma** — the proof that one oracle of a composition keeps all of that
composition's package invariants and its game invariants, for every value of the composition's
parameters, as a lemma of its own in a file of its own. It belongs to the composition, not to an
equivalence, so every equivalence that uses the composition uses the same lemma. Its package
invariants come from the package-invariant and frame lemmas of the composition's instances; only
its game invariants are proved by walking the composition's oracle. A **side-invariant job** proves
them for one composition; a proof job never does, and will not start an equivalence whose
compositions have no side-invariant lemmas yet.

**Package-invariant lemma** — the proof that one oracle of a package keeps that package's
invariants, for every environment the package can be placed in: any module that provides its
imports and cannot write its state. Nothing is known about what the imports do. It belongs to the
package (one per package variant), never to a composition, so a package used in many compositions
is proved once. A **package-invariant job** proves the package-invariant, frame and start lemmas of
one package; a side-invariant job never does, and will not start a composition whose packages have
no such lemmas yet.

**Frame lemma** — the proof that one oracle of a package keeps any property of its environment's
state that the environment's own oracles keep. It says nothing about the package's invariants and
follows from the shape of the code alone. It is what carries a called package's invariant through
the code of the package that calls it.
_Distinguish_: **package-invariant lemma** (about the package's own state).

**Session record** — what a proof job leaves about how far proving one oracle lemma got: the
oracle's status and the tactics accepted at each joint node. The records of an equivalence's oracles
together decide whether the next proof job on that equivalence starts fresh, **resumes** (proves
only the oracles not yet done), or skips the equivalence as complete. An oracle is done when it
ended without an `interrupted` admit; admits with any other reason count as done. Unlike a run artifact it is worth
protecting, because losing it loses the ability to resume.

**Saved joint tree** — the joint tree lockstep execution built for one oracle, kept beside the
session record together with a **fingerprint** of everything lockstep execution read to build it.
It is what lets a later proof job resume that oracle without running lockstep execution again, so
the debugger never has to be deterministic. A fingerprint that no longer matches the project means
the tree is *stale*: it is still used, with a warning, because the EasyCrypt files on disk are as
old as it is.

**Closed node** — a joint node whose goal an earlier proof job finished, its whole subtree
included, without an `interrupted` admit. Admits with any other reason do not reopen it.
_Distinguish_: the **in-flight node** is the innermost node the earlier job was in when it
stopped; its **ancestors** are neither closed nor in flight.

**Resume mode** — how a proof job picks up an oracle that an earlier job left `interrupted`.
**restart** proves it again from scratch, lockstep execution included. **trust** and **replay**
walk the saved joint tree again: each closed node is skipped (under **trust** its goal is closed
with `admit` in the live session; under **replay** its recorded script is sent to EasyCrypt
again) and its recorded script goes into the file. The in-flight node is proved from its start.
Oracles already done are never re-proved, whatever the mode.

**Tactics run** — the proving pass of one proof job against a live EasyCrypt. Its defining
property: the proof file on disk always holds what has been proved so far, so stopping it early
costs no proved oracle. _Avoid_: proof translation.

**Leaf** — a joint node with no further branching: both programs have run to their end and only
the postcondition is left to prove.

**Leaf part** — one goal that is left when a leaf is taken apart: its exit path decided, its
programs run to a formula, and that formula opened (binders and premises introduced, conjunctions
split) until nothing more opens. How many parts a leaf has is known only after this. A part belongs
to no claim of its own, except when opening it unfolded one of the invariant's operators that stands
for a claim (a state relation, a package or a game invariant): then it belongs to the last such
claim. An admitted part is named by its leaf, and its reason is Domino's verdict on its claim, or
on the leaf as a whole (the worse of equal-output and invariant) when it has none.
_Avoid_: conjunct (a part can hold several conjuncts), subgoal.

**Leaf budget** — an optional limit, set only by the user, on the time a tactics run may spend
taking one leaf apart; when it runs out, the leaf's remaining parts are admitted. Without one, a
leaf takes as long as its sentences do, each still bounded by the per-sentence timeout.

**Quick close** — the one cheap closing attempt every program goal of a tactics run gets first,
before any structural tactic: `auto => /#` under a short timeout.
_Avoid_: rung 0.

**Fallback sequence** — the fixed, ordered list of closing tactics a tactics run tries on a side
goal or a leaf part, cheapest first, ending in an admit. Its members are **fallbacks**, numbered
from one.
_Avoid_: ladder, rung.

**Seal** — to close every goal an oracle still has open with `admit`, so the oracle's proof is
complete as written even though the walk had not finished it. Sealing is what makes a stopped
tactics run leave a usable file. It works on a copy of the script and sends nothing to
EasyCrypt; its admits carry the reason `interrupted`.

**Partial proof** — a proof file holding proved bullets alongside the admits of a seal. It is a
proof EasyCrypt accepts, not a draft.

**Interrupt** — Domino telling EasyCrypt to abandon the sentence it is running, because the
sentence ran past its time or the run was asked to stop. An interrupt is **honored** when that
sentence ends `interrupted`; it is **swallowed** when EasyCrypt carries on with the sentence as if
nothing had arrived; it is **unanswered** when no answer to the sentence comes back in time at all.
An interrupt that lands after the sentence has finished, or between two sentences, changes nothing
and is not answered: every sentence has exactly one answer.

**Respawn** — replacing, in the middle of a proof job, an EasyCrypt that left an interrupt
unanswered with a fresh one opened at the same proof. The oracle in flight is sealed; oracles
already finished are admitted in the fresh EasyCrypt, not proved again; the job carries on with the
next oracle. _Avoid_: restart (a resume mode, which re-proves an oracle in a *later* proof job).

**Ended early** — a proof job that stopped before its last oracle for a reason other than a
Ctrl-C: its respawns ran out, or a respawn failed. It leaves its file and record as a Ctrl-C would
(the oracle in flight sealed, the rest `pending`), but the cause is shown as its own, and the run
goes on with the next proof job. _Avoid_: interrupted (that is a Ctrl-C).

**Front goal** — the first open goal: the one the next tactic works on. EasyCrypt's answer to a
sentence always gives the **goal kind** of every open goal: *program* (a judgement over two
programs) or *formula* (anything else). The number of open goals is the length of that list. Of the
front goal it gives what the sentence asked for: nothing, its **head** (the conclusion to a fixed
depth and the names and types of the hypotheses), or the whole goal. A sentence that fails changes
no goal, so its answer gives no front goal at all. _Avoid_: first goal, focused goal.

**Sentence role** — why a tactics run sent a sentence: a *quick close*; *structure* (moving through
the program: straight-line code, branches, samplings); a *side-goal fallback*; *exit path*
(deciding a leaf's exit path); *reduce* (turning a leaf's program goal into a formula); *split*
(opening a leaf into its parts); a *part fallback* (closing one leaf part); an *admit*; an *undo*;
a *resume* (sending again what an earlier run proved, to bring a closed node back). Time is
reported by role.
_Avoid_: step (the report uses "proofstep" for a hop of the theorem), rung.

**Run artifact** — a file a tactics run writes *about itself* rather than as translation output:
the live page, the EasyCrypt transcript, the per-equivalence report, the alignment report, the
debug output of lockstep execution. Regenerated every run and never hand-edited, so unlike
translation output it may be overwritten without asking.

**EasyCrypt transcript** — the record of one tactics run's exchange with EasyCrypt: every sentence
sent, in order, with EasyCrypt's answer and how long it took. Undone attempts and the `undo`
sentences themselves are part of it. By default each answer is **capped**: its front goal's conclusion and hypotheses are each cut at a fixed length (`--ec-transcript full` keeps the answer verbatim); records are only ever appended, never
compacted, because the page reads them back by byte offset. Each record says why its sentence was
sent (its oracle, joint node and **Sentence role**). Event records (an interrupt, a respawn, Domino's
own time between two sentences) hold the time outside sentences, so the records of one oracle add
up to its EasyCrypt time. _Distinguish_: the **solver transcript** is the raw incremental
exchange with cvc5, a debugging aid for the debugger itself.
