# Story 94 — The joint-tree viewer header counts claims; the details are in the Run summary

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 24 (the joint-tree viewer), symbolic-execution 25 (one-sided runs use the same page).
**Blocks:** 95 (it renames the words in the header that this story writes).
**ADR:** none. The rejected alternatives are in §4.
**Decisions:** owner's grilling session of 2026-10-26, Questions 1 to 4.

A **debugger page** story: Rust and the page template. Test-first.

---

## 1. Why this story exists

The header of the joint-tree viewer (`src/debug/lockstep_viewer.html`, `#h-summary`) adds up to four
chips for each claim: `verified`, `unreachable`, `goal fails`, `inconclusive`. An all-claim run with
12 claims shows about 30 chips. The header then fills the top of the page, and the tree, the detail
cell and the listings get less space. The one-sided runs (`domino debug --game`, `--package`,
`domino easycrypt debug --side-inv`, `--pkg-inv`) use the same template, so they have the same
problem.

The top-right cell (`#cell-detail`) shows only "Select a node or a joint path in the tree." until the
user clicks something. It has space for the details that the header must lose.

## 2. What the user sees after this story

```
Full4WHS · proofstep 3 · H1_1 == H2_0
oracle Send · 12 claims · lockstep on the domino listing     [RUNNING]  40 joint paths · 212 nodes · 2 stuck points · [12 claims: 10 verified · 1 inconclusive · 1 GOAL FAILS ▸]  [PARTIAL …]
```

When no node is selected, the top-right cell shows the **Run summary**. The claims line in the
header is a button: it clears the selection and shows the Run summary again.

(Story 95 changes "proofstep" in the title to "game hop".)

## 3. What to build

### 3.1 The status of a claim (Rust)

`VerdictCounts` (`src/debug/lockstep_run.rs:245`) gets one method, `status()`. It gives the worst
verdict of the claim over the joint paths so far:

| Counts | `status()` |
|---|---|
| `goal_fails > 0` | `goal-fails` |
| else `inconclusive > 0` | `inconclusive` |
| else `verified + unreachable > 0` | `verified` |
| else (no joint path has a verdict for the claim yet) | `none-yet` |

An unreachable verdict is "not refuted", so it counts as `verified`. A claim that is unreachable on
every joint path is `verified` too; the Claims table (§3.3) shows its counts.

Each entry of `summary.claims` in `trace.json` gets the field `"status"`, serialised from
`status()`. `LOCKSTEP_TRACE_SCHEMA` goes from 14 to 15. The lockstep run and the one-sided runs
(`src/debug/side_run.rs`) use the same `LockstepSummary`, so both get the field.

The page does not calculate a status. It counts the `status` values only.

### 3.2 The header (page)

The header has two rows:

1. **Title** — as now.
2. **Sub-line and summary**, on one wrapping row:
   - The sub-line: `oracle O · <claims> · lockstep on the <listing> listing`. `<claims>` is the list
     of claim names when the run checks 1 or 2 claims (all EasyCrypt runs, or `--claim X`), and
     `N claims` when it checks more. An all-claim run keeps its words ("all claims of the core claim
     set").
   - `RUNNING — this page refreshes every 2 s` (amber, on a live page only).
   - `N joint paths · N nodes · N stuck points` (stuck points red when more than 0).
   - **The claims button**: `N claims: a verified · b inconclusive · c GOAL FAILS ▸`. A group with 0
     claims is not shown; `none-yet` shows as `d pending` on a live page. The colour is the colour
     of the worst group: red for a goal failure, amber for inconclusive, green otherwise.
   - `PARTIAL — exploration stopped early (…)` (red, as now).

The four option chips (`timeout`, `max-paths`, `smt`, `transcript`) and `N children pruned` move to
the Run summary (§3.3).

### 3.3 The Run summary (page)

A new function `renderSummary()`, next to `renderDetail()`, fills the top-right cell. It shows in
these cases:

- when the page opens and the URL hash has no `n=`;
- when the user clicks the claims button. The click clears the selection (`selection = null`, the
  `.sel` classes removed) and removes `n` and `c` from the hash, so a refresh keeps the summary.

It uses the `sec` sections that the cell already uses:

1. **Claims** (open). One row for each checked claim, in the order of `summary.claims`:
   status badge · verified · unreachable (pair / dependency) · GOAL FAILS · inconclusive. These are
   the columns of the stdout report (`render_summary`). The admitted claims come last, with
   "admitted — not checked".
2. **State relations failing** (open; only when `summary.relation_failures` is not empty). One row
   for each relation, with its number of joint paths.
3. **Run** (closed). The option chips, `N children pruned`, the node kinds (`summary.node_kinds`),
   the stop reason, and the number of stuck points.

The help text "Select a node or a joint path in the tree." goes to the top of the Run summary as one
short line.

### 3.4 The same line on stdout and in `summary.txt` (Rust)

`render_summary` (stdout) and `one_line_summary` (`summary.txt`, `src/debug/lockstep_report.rs`)
print the same short line, from `status()`:

```
claims        12 (10 verified, 1 inconclusive, 1 GOAL FAILS)
```

The per-claim table on stdout does not change.

## 4. Rejected alternatives

- **Count checks** (claims × joint paths added together). The numbers are large, and they do not
  show which claim fails.
- **Count joint paths by their worst claim.** This repeats the tree, where each joint path has its own
  badges.
- **A summary block pinned to the top of the detail cell for each selection.** It moves the space
  problem down one cell, and every render must know about it (change amplification).
- **A pop-over panel from the header.** It hides the tree while it is open.
- **Keep the option chips in the header.** They do not change during a run and are seldom read.
- **The page calculates the status.** The rule is then in a template string that no test covers, and
  stdout would need a second copy.
- **A separate group for a claim that is unreachable on every path ("vacuous").** The Claims table
  shows its counts; the header stays short.

## 5. Tests first

- [ ] `status()`: one test for each row of the table in §3.1, and one where `goal_fails` and
      `inconclusive` are both more than 0 (gives `goal-fails`).
- [ ] `trace.json` of a lockstep run has `summary.claims[i].status`, and `schema` is 15.
- [ ] `trace.json` of a one-sided run (`domino debug --game C`) has the same field.
- [ ] `render_summary` and `summary.txt` have the `claims` line with the counts of a run with one
      goal failure and one inconclusive claim.
- [ ] The page template has the claims button, the function `renderSummary`, and no `h-opts` row in
      the header (string checks in `lockstep_viewer.rs`, as the existing tests do).
- [ ] The page is still a pure function of its inputs (the existing test).

## 6. Acceptance criteria

- [ ] All tests of §5 green; `cargo clippy` clean.
- [ ] The owner's check, in a browser: an all-claim `domino debug --lockstep` run on a project with
      more than 5 claims, and one `domino easycrypt debug` run. The header has two rows; the page
      opens on the Run summary; a click on a node shows the node; a click on the claims button shows
      the Run summary again; a refresh keeps each of these.
- [ ] A live page (`RUNNING`) shows the claims that have no verdict yet as `pending`.
- [ ] Complexity: `status()` and the summary-line function within budget (`crap_scope` on
      `src/debug/lockstep_run.rs` and `src/debug/lockstep_report.rs`).

## 7. Not in this story

- The sequential viewer (`domino debug` without `--lockstep`, `src/debug/report.rs`). It already
  shows one set of four totals, not one set for each claim.
- The word "proofstep" in the title. Story 95 changes it.
