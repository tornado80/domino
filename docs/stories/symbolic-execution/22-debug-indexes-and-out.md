# Story 22 — Debug indexes at each level, and `--out` for every run

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 21 (the check names, which the failures list uses); 19 (the sweep, `SweepEntry`,
the layout).
**Blocks:** nothing.
**Decision record:** `docs/adr/0011-a-debug-index-renders-the-records-on-disk.md`.

---

## 1. Why this story exists

The owner said: *"the domino debug index html rewrites upon each proofstep. I think there is no
need for a global index html if the user has not called debug on a project. Instead let's have an
index html for each proofstep and theorem."* And: *"`--out` can not be used when one wants to prove
a theorem or proofstep and it only works for an oracle. I think it should work in all cases."*

Today (`crates/domino/src/main.rs`, end of `debug`):

- Each run that covers more than one oracle writes `_build/debug/index.html` and
  `_build/debug/summary.txt` from **this run's entries only** (`sweep::write_index`). A run of one
  proofstep deletes every other row of the project index.
- `--out` names the exact directory of one oracle run. If the run covers more than one oracle,
  the command stops with "`--out` names one output directory, but this run covers N oracles".

Vocabulary (`CONTEXT.md`): **Debug index**, **Check**, **All-claim run**, **Strategy**,
**Listing**.

## 2. Inherited from earlier stories

- **Story 19 / `src/debug/layout.rs`:** a run of the Domino listing writes to
  `<root>/<theorem>/<left>-<right>/<oracle>/<claim>/`, with `!all-claims!` for an all-claim run.
  The root is `_build/debug` (`DOMINO_DEBUG_DIR`). Both strategies write into the same directory,
  and each one names its files after itself (`sequential_viewer.html`, `lockstep_trace.json`, …).
- **`src/debug/sweep.rs`:** `plan` turns the filters into targets. `SweepEntry` (from
  `from_sequential` / `from_lockstep`) holds what a row needs. `failure_table` and `write_index`
  render it.
- The default directory of one run is built in **two** places: `driver.rs` (sequential, around
  `claim_label`) and `lockstep_run.rs` (`out.unwrap_or_else(...)`).
- **Story 21:** the names of the checks (`state-relation <name>` and the claim names), and
  a verdict for each check in `trace.json`.

## 3. Work to do

### 3.1 One function owns the run directory

Add one function to `src/debug/layout.rs`:

```rust
/// The directory of one Domino-listing run: `<root>/<theorem>/<left>-<right>/<oracle>/<claim>/`.
pub fn run_dir(root: &Path, target: &Target, claim_label: &str) -> PathBuf
```

The sequential driver and the lockstep driver both use it. Remove the two copies of the path rule.
The EasyCrypt listing (`_build/easycrypt/<T>/!debug!/…`) does not change.

### 3.2 `--out` is the debug root

`--out <dir>` replaces `_build/debug` for every run, of every level. Below `<dir>`, the layout is
the usual layout. A run of one oracle then writes to `<dir>/<T>/<L>-<R>/<O>/<claim>/`, and no
longer to `<dir>` itself.

- Remove the error `--out names one output directory, but this run covers N oracles` and its
  check (`main.rs`, `plan.targets.len() > 1 && d.out.is_some()`).
- Change the help text of `--out` (`crates/domino/src/cli.rs`): "Root of the debug output.
  Defaults to `_build/debug`. Each run writes to `<root>/<theorem>/<left>-<right>/<oracle>/<claim>/`
  (`!all-claims!` for an all-claim run). Indexes are written at the level the run selects."
- Change every story, README section and skill text that shows `--out` as the directory of one
  run. Use `grep -rn -- "--out" docs Readme.md` to find them. Old implementation reports stay as
  they are.

### 3.3 The result record

Each oracle run writes a **result record** next to its viewer: `<strategy>_result.json`. It holds
what a row of an index needs, and nothing more:

```json
{
  "schema": 1,
  "theorem": "T", "proofstep": 3, "left": "L", "right": "R", "oracle": "O",
  "claim": "!all-claims!",
  "strategy": "sequential",
  "listing": "domino",
  "viewer": "sequential_viewer.html",
  "unit": "pairs", "units": 42,
  "checks": [ { "check": "invariant", "verified": 40, "unreachable": 1,
                "goal_fails": 0, "inconclusive": 1 }, … ],
  "failures": [ { "check": "state-relation rel_ctr", "pair": "#3.1",
                  "verdict": "inconclusive" }, … ],
  "ok": false,
  "stop_reason": "completed",
  "elapsed_ms": 1234,
  "finished_at": "2026-10-07T12:00:00Z"
}
```

`SweepEntry` becomes the in-memory form of this record (add `claim` and `finished_at`). The
record is written with the other run artifacts, also after an interrupt (then `stop_reason` says
so). It is a **run artifact** (`CONTEXT.md`): regenerated on each run and never edited by hand.

Runs from before this story have no record. They are not listed. A rerun lists them.

### 3.4 Indexes render the records on disk (ADR 0011)

Replace `write_index(root, entries)` with:

```rust
/// Rewrite the index of `level` and each index above it that already exists, all under `root`,
/// from the result records on disk. Returns the paths written.
pub fn refresh_indexes(root: &Path, level: &Level) -> std::io::Result<Vec<PathBuf>>

pub enum Level {
    Project,
    Theorem { theorem: String },
    Proofstep { theorem: String, left: String, right: String },
}
```

- The **selected level** comes from the filters, the same way `plan` reads them: no `--proof`
  is `Project`; `--proof` without `--proofstep` is `Theorem`; `--proofstep` is `Proofstep`.
  `--oracle` and `--claim` do not change the level; they only select fewer runs.
- A run of exactly one oracle (all three filters) writes **no** index, as today. It still updates
  each index above it that already exists.
- `refresh_indexes` writes the index of `level`. Then it goes up the tree and rewrites each
  index (`index.html` and `summary.txt`) that already exists. It never creates an index above the
  selected level. Thus there is no project index until a run on the whole project.
- An index reads every `*_result.json` below its directory. It never reads `trace.json`.
- An index writes `index.html` and `summary.txt` in its own directory:
  `<root>/index.html`, `<root>/<T>/index.html`, `<root>/<T>/<L>-<R>/index.html`.

The CLI passes only `root` and `level`. It no longer collects entries to give to the index.

### 3.5 What an index shows

One renderer for the three levels; the level is a parameter. Use the existing look of the index
page (`sweep.rs`), with its light and dark colours.

**The table: one row for each child.**

| Level | One row for each | Columns |
|---|---|---|
| Project | theorem | theorem, number of runs, runs not ok, oldest run, link to its index |
| Theorem | equivalence proofstep | proofstep, `L == R`, number of runs, runs not ok, oldest run, link to its index |
| Proofstep | run | oracle, claim label, strategy, result (`ok` / `FAILS` / `stopped early (…)`), checks not verified, time, finished at, link to the viewer |

A child with no index of its own (for example, a proofstep that was only run oracle by oracle)
still has a row. Its link goes to the child's directory index if there is one, or else the row has
no link and says "no index; run `domino debug --proof T --proofstep N`".

The "oldest run" column shows the `finished_at` of the oldest record below the row. Thus a row that
holds an old run is visible as old.

**The failures list, under the table.** Each run below the index with a goal-fails or
inconclusive check: the target, the strategy, the check names with their verdicts (story 21's
names, for example `invariant: inconclusive → state-relation rel_ctr: inconclusive`), and a direct
link to the viewer of the run. At most 50 rows, then "… and N more", as `failure_table` does
today.

`summary.txt` has the same content as text.

### 3.6 stdout

Keep the one line for each oracle and the failure table. At the end, print each index that was
written:

```
index    _build/debug/T/L-R/index.html
index    _build/debug/T/index.html      (updated)
```

### 3.7 Not in this story

- Indexes for `domino easycrypt debug` (the EasyCrypt listing). It keeps its own output.
- Deleting old runs. To remove them, delete the directory.

## 4. Acceptance criteria

- [ ] `layout::run_dir` is the only place that builds the path of a Domino-listing run. Both
      drivers use it.
- [ ] `domino debug --proof T --proofstep N --oracle O --out X` writes to `X/T/L-R/O/!all-claims!/`.
- [ ] `domino debug --proof T --out X` runs (no error) and writes `X/T/index.html` and one
      `X/T/<L>-<R>/index.html` for each equivalence proofstep.
- [ ] A run of a proofstep writes `<root>/T/L-R/index.html`, and **no** `<root>/index.html`
      when there was none before.
- [ ] Run `--proof T`, then `--proof T --proofstep 0`: the index of `T` still has every
      proofstep, and its row for step 0 shows the new `finished_at`.
- [ ] A sequential run and then a lockstep run of the same proofstep: the proofstep index shows
      both runs, each with its strategy.
- [ ] A run with `--claim invariant` and an all-claim run of the same oracle: both rows show.
- [ ] Each run directory has its `<strategy>_result.json`, also after Ctrl-C.
- [ ] The failures list links straight to the viewer of each failing run, and names the checks
      with story 21's names.
- [ ] Unit tests for `refresh_indexes` on a temporary directory with hand-written records:
      levels, "update only if it exists", ordering, the oldest-run column, and a child with no
      index.
- [ ] The `--out` help text and the documentation say "root of the debug output".
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```sh
source ~/.cache/domino/cvc5-lib-env.sh
cargo build -p domino --features cvc5-lib
D=$PWD/target/debug/domino
cd example-projects/hello-world-oracle-rename-new
rm -rf _build/debug
$D debug --proof Proof --proofstep 0 ; ls _build/debug _build/debug/Proof      # no _build/debug/index.html
$D debug --proof Proof ; ls _build/debug/Proof/index.html
$D debug --proof Proof --proofstep 0 --lockstep ; grep -c lockstep _build/debug/Proof/*/index.html
$D debug --proof Proof --out /tmp/dbg ; find /tmp/dbg -name index.html
```

Open each `index.html` in a browser and click from the theorem index to a failing run.

## 6. Rejected alternatives

- **Write each index from this run's entries only** (today's shape, at three levels). Rejected:
  a narrower rerun leaves stale rows above it with no warning, a filtered run (`--oracle`,
  `--claim`) writes an index with missing rows over a full one, and a lockstep run replaces the
  sequential index of the same step.
- **`--out` replaces the directory of the selected level** (a proofstep run writes `<out>/<O>/…`).
  Rejected by the owner: the meaning of `--out` then depends on the level.
- **A second flag, `--out-root`, for sweeps.** Rejected: two flags with almost the same meaning.
- **A flat index at each level** (every run below it). Rejected: it does not scale; `llvm-cov`
  moved from one flat index to one index for each directory for this reason.
- **Drill-down without the failures list.** Rejected: too many clicks to find a failure.
- **Indexes for the EasyCrypt listing in this story.** Rejected: different paths, different
  `--out` rules (ADR 0004) and the live page links; it doubles the story.

## 7. Notes / risks

- Two equivalence proofsteps of one theorem with the same `L` and `R` share one directory. This is
  not new. Do not change it here.
- An index reads one small record for each run. On a large project this is some hundred files. If
  `refresh_indexes` takes more than one second on 4WHS, record it in the report.

## 8. State handed to the next story

Record in `22-…-IMPLEMENTATION-REPORT.md`: the record schema, where `refresh_indexes` lives, the
documents changed for `--out`, and a screenshot of each index level.
