# Story 20 — The sequential report uses the debug viewer's grid

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Depends on:** EasyCrypt story 48 (the grid, the persistent listings and their shared code in
`src/debug/report.rs`); stories 07 (the viewer), 16 (executed-line painting).
**Blocks:** nothing.

This is a **viewer-only** story. Exploration, verdicts and `trace.json` do not change.

---

## 1. Why this story exists

The owner asked for the joint-tree viewer's new layout (EasyCrypt story 48) "for debugging in Domino
mode (both normal and lockstep)". `domino debug --lockstep` already gets it from story 48, because
it renders the same page. The **sequential** report (`domino debug` without `--lockstep`, the page
built by `src/debug/report.rs`) is the "normal" mode, and it has every problem story 48 fixed:

- `renderDetail` runs `detail.innerHTML = ""` on every selection and rebuilds both listings.
- The listings are `<details>` sections, **collapsed by default**, at the bottom of the detail pane,
  one under the other. They are never side by side, and a scroll is lost on the next click.
- An opened listing centres its terminal (`pre._termRow`), but only once, when the section opens.

## 2. Inherited from earlier stories

- EasyCrypt story 48 leaves `GRID_CSS` and `LISTING_JS` (or whatever it names them) in
  `report.rs`: the 2×2 grid, the splitters with their hash keys, the narrow-window stack, listings
  built once and repainted from a spec, and "bring a listing to a target line".
- The sequential page's tree pane holds the filter box, the verdict toggles and the left paths,
  each with its right paths and right-branch prunes under it. Top-level left-branch prunes are
  synthetic rows (`prunedRow`) whose "terminal" is the cut fork line.
- `listingBlock(text, path, terminal)` paints a path's executed lines and its terminal. That
  painting logic stays and becomes the spec handed to the shared repaint.

## 3. Work to do

### 3.1 The grid

The same four cells as story 48 §3.1:

- **Top left:** what `#left` holds today (filter, toggles, collapse/expand, path tree).
- **Top right:** the detail pane minus the two listing sections: path tables, effect, claim
  assertion, model, SMT asserted.
- **Bottom left / bottom right:** the left and right listings, always visible, each with a title bar
  (side, game, "N lines · M executed") and the legend.

Splitters, hash keys, the narrow-window stack and the one-line header are story 48's, through the
shared code. There is no private copy.

### 3.2 What a selection paints and where it scrolls

| What is selected | Left listing | Right listing |
|---|---|---|
| a left path | painted with that path; centred on its terminal | cleared of colour, scroll unchanged; title bar reads "no right path selected" |
| a right path (a left × right pair) | painted with the left path; centred on its terminal | painted with the right path; centred on its terminal |
| a right-branch prune | painted with the left path; centred on its terminal | painted with the prune's prefix; centred on the cut line |
| a top-level left-branch prune | painted with the prune's prefix; centred on the cut line | cleared, scroll unchanged |

The listings are never rebuilt (story 48 §3.2), and a hand scroll lasts until the next selection.

### 3.3 Keyboard navigation

Story 48 §3.4's keys apply to the path tree: ↑/↓ over visible rows, → opens or goes to the first
right path, ← closes or goes to the parent left path. Rows hidden by the filter box or a verdict
toggle are skipped.

### 3.4 Not in this story

- Anything EasyCrypt-specific: this page only ever shows the Domino listing.
- A live progress page for `domino debug`: Domino mode reports progress on the terminal, and the
  owner decided no HTML progress page is wanted.

## 4. Acceptance criteria

- [ ] The sequential page is the 2×2 grid, built from the shared code in `report.rs` (no second copy
      of the grid CSS or listing JS).
- [ ] Both listings are always visible and created once per page load; selecting rows never
      replaces a listing's rows.
- [ ] Each row of the §3.2 table paints and scrolls as stated.
- [ ] Splitter positions and listing offsets survive a reload through the hash.
- [ ] Keyboard navigation as §3.3.
- [ ] `trace.json` is byte-identical before and after; the page is byte-identical across two runs.

## 5. How to verify

```sh
D=target/debug/domino
cd example-projects/hello-world-oracle-rename-new
$D debug --proof Proof --proofstep 0 --oracle ChangeNameUsefulOracle
```

Pick a claim run with at least two left paths and a right-branch prune; kem-dem `PKENC` has both.
Headless Chrome, screenshots at 1600×1000 and 800×1000:

1. Select a left path: the left listing is centred on its terminal; the right listing is uncoloured
   and says "no right path selected".
2. Scroll the left listing by hand, then select a right path under that left path: the left listing
   re-centres on the left terminal, the right listing on the right terminal, and a row element
   tagged before the selection is still in the DOM.
3. Select a right-branch prune: the right listing is centred on the cut line.
4. Drag the row splitter, reload: same position.

Attach the screenshots to the implementation report.
