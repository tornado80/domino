# Story 94 — Implementation report: the viewer header counts claims

Rust and the page template. No ADR. The title keeps the word "proofstep" (story 95 changes it).

## What changed

### The status of a claim (`src/debug/lockstep_run.rs`)

- New `VerdictCounts::status() -> ClaimStatus`. It gives the worst verdict so far:
  `goal-fails`, then `inconclusive`, then `verified` (verified or unreachable), else `none-yet`.
- New public enum `ClaimStatus` (kebab-case in JSON).
- `ClaimCounts` serialises through a private `ClaimCountsJson` (`serde(from, into)`). The JSON
  has the field `status`, calculated from the counts. Deserialisation ignores it, so the counts
  are the only source. The lockstep run, the one-sided runs and the stuck-point rollups all get
  the field, because they all use `ClaimCounts`.
- `LOCKSTEP_TRACE_SCHEMA` is 15.

### The `claims` line (`src/debug/lockstep_report.rs`)

- New public `claims_line(&LockstepSummary)`: `12 (10 verified, 1 inconclusive, 1 GOAL FAILS)`.
  A status with 0 claims is not shown; `none-yet` is `pending`.
- `render_summary` (stdout) prints it as `claims        …` after `elapsed`. `render_tree`
  (`summary.txt`) prints it after the `summary:` line. The per-claim table does not change.
- To keep `render_summary` in the complexity budget, two blocks moved to new private functions:
  `write_verdicts` (the verdict table) and `write_failing` (the failing joint paths). The output
  does not change.

### The page (`src/debug/lockstep_viewer.html`)

- The header has two rows: the title (`#h-title` has `flex-basis: 100%`), then the sub-line and
  the chips on one wrapping row. The `h-opts` row is removed.
- The sub-line: the claim names for 1 or 2 checked claims, `N claims` for more; an all-claim
  Domino run keeps its words. "lockstep execution on" is now "lockstep on", as in §2.
- The chips: `RUNNING …` (live only), `N joint paths · N nodes`, `N stuck points` (red when more
  than 0), the claims button `#h-claims`, `PARTIAL …`. The button counts the `status` values only.
  Its colour is the colour of the worst group.
- New `renderSummary()` (next to `renderDetail()`): the help line, then the sections Claims (open),
  State relations failing (open, only when not empty) and Run (closed: option chips, children
  pruned, node kinds, stop reason, stuck points). New helpers `table`, `claimsTable`, `runBlock`.
- New `showSummary()`: the click handler of the claims button. It removes the `.sel` classes, sets
  `selection = null`, removes `n` and `c` from the hash and calls `renderSummary()`. `restore()`
  calls it when the hash has no valid `n`, so the page opens on the Run summary and a refresh keeps
  it. The `hashchange` handler also restores when `n` is removed from the hash.

## Tests

`cargo test --workspace --features cvc5-lib`: all green after the fix below (the lib: 1033 pass,
7 ignored, before the fix 1 failed). `cargo clippy --workspace --all-targets --features cvc5-lib`:
no warnings. New or changed tests:

- `a_claim_status_is_its_worst_verdict_so_far`, `a_goal_failure_outranks_an_inconclusive_verdict`,
  `a_claim_unreachable_on_every_path_is_verified`: each row of the §3.1 table.
- `the_trace_gives_each_claim_its_status`: the JSON field, and a round trip.
- `the_claims_line_counts_claims_by_status`: the groups and `pending`.
- `the_summary_and_the_tree_text_count_the_claims_by_status`: stdout and `summary.txt` with one
  goal failure and one inconclusive claim.
- `the_acceptance_cases_complete_and_write_their_artifacts`: `schema` is 15 and each
  `summary.claims[i]` has `status`.
- `a_side_run_checks_the_composition_claims_and_fails_only_the_breaking_path`: the one-sided
  `trace.json` has `status` `goal-fails`. Deviation: this is the `--side-inv` run of
  `side_run.rs`, not a `domino debug --game` run. Both use the same `LockstepSummary`.
- `the_header_has_a_claims_button_and_the_detail_cell_a_run_summary`: string checks on the
  template.

Manual check: a headless Chrome `--dump-dom` of an all-claim `domino debug --lockstep` run on
`example-projects/4WHS` (13 claims). The header has the title row and one row
`oracle Send4 · all claims · lockstep on the domino listing | 10 joint paths · 43 nodes |
0 stuck points | 13 claims: 13 verified ▸`. The detail cell opens on the Run summary.

## Complexity (cyclomatic, `crap_symbol`)

`VerdictCounts::status` 4, `claims_line` 1, `render_summary` 10 (it was 23 before the
extraction), `write_verdicts` 6, `write_failing` 9. The JavaScript functions are not measured.

## A fix outside the story

`writers::easycrypt::export::tests::the_name_rule_rejects_an_oracle_called_invariants_and_names_both_files`
failed on macOS. Its helper `hello_world_with_oracle` read each file of
`example-projects/hello-world` as UTF-8. A `.DS_Store` file (git ignores it) is not UTF-8. The
helper now copies a file that is not text without a change.

## Not done

- The owner's check in a browser (clicks, refresh, an `easycrypt debug` run, a live page).
