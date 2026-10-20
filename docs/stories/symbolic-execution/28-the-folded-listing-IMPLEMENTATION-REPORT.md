# Story 28 — Implementation report: the folded listing

## What changed

- **`src/debug/fold.rs`** (new): `FoldedListing { text, labels }` and `FoldedListing::of(&InlinedOracle)`.
  The fold reads the full listing's text and the line ranges that the IR records for each branch
  (`then_lines`, `else_lines`, `frame_lines`). It is the same for the Domino listing and the
  EasyCrypt listing. `known_value` substitutes each constant that resolves to a literal
  (`resolve_const`) and then uses story 27's `condition_value`. A side tree's free parameters
  resolve to theorem constants, so there only literal conditions fold.
  - A trivial `true` branch keeps its `then` body; a trivial `false` branch keeps its `else` body
    or nothing. The body moves left to the branch's indentation.
  - A branch with an exit guard, and an `assert`, never fold.
  - Code after a statement that always exits (with trivial conditions at their value) is left
    out, as the read-only view of story 26 does. Without this, the ideal code of `Prf.Eval` after
    the folded `if (… or not b)` stays in the listing.
  - `line_of(label)`: the folded line of a label, or the first folded line after it.
- **`domino inline --fold-trivial-branches`**: `render::ListingView { Full, Folded }`. The folded
  lines keep their full-listing numbers, and one header line says so. Without the option the
  output is as in story 27 (the snapshot test is unchanged).
- **Pages**: `LockstepMeta` and `DebugRun` carry `left_folded` and `right_folded`.
  `LOCKSTEP_TRACE_SCHEMA` 13 → 14, `TRACE_SCHEMA` 10 → 11. The paths keep full-listing labels.
- **Viewer** (`LISTING_JS`, both pages): a listing has a full view and a folded view. Each folded
  row shows its label as its line number, so the path tree and the detail pane need no change.
  A folded row paints the labels it covers (its own, and those the fold leaves out just before
  it): the decision of a folded branch shows on the first line after it. The checkbox
  "hide trivial branches" is on each listing; the two stay in step. The default is the full
  listing. The choice is in `localStorage` (`domino.hide-trivial-branches`), in `try`/`catch`.

## Rejected shapes

- Re-render the AST with a fold flag in `ir.rs` and in `lower.rs`: two renderers to change, a flag
  parameter, and labels that must be mapped back.
- Folded lines numbered 1..n with a separate map: the tree and the detail pane say `L<n>` in
  full labels, and would need the map too.

## Tests

- `fold.rs`: Hybrid2 `Send2` (`bprf: false`): no `Prf.PRF[` line in the folded Domino listing, and
  each folded line is the full line at its label; the same on the EasyCrypt listing; KEM-DEM
  `PKENC`: every done-flag guard is in the folded listing; a side tree of `Hybrid2` with free
  parameters folds only what literals decide.
- `render.rs`: `--fold-trivial-branches` prints the folded listing with its labels.
- `lockstep_run.rs`: the trace carries both folded listings, and each label is a full line. The
  "no network" test now checks that each `localStorage` use is inside `try`.
- Browser (headless Chrome over CDP, `28-screenshots/`): on the Domino and EasyCrypt pages of
  Simple4WHS proofstep 1 `Send2`, the checkbox switches both listings; every painted line of the
  full view that the folded view shows is painted there too; the choice survives a reload; with
  `localStorage` blocked the page works and the choice is not kept.

## Open

- Complexity: `sdlc` is not on `PATH`; the gate is UNMEASURED.
