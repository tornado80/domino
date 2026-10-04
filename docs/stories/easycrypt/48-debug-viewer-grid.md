# Story 48 — The joint-tree viewer is a 2×2 grid, and a click brings both listings to the node

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 24 (the joint-tree viewer), symbolic-execution 16 (executed-line painting).
**Blocks:** symbolic-execution 20 (the sequential report adopts this layout), 49 (paints inside the
listings this story makes persistent), 50 (renames a toggle this story moves).

This is a **viewer-only** story. Translation, the IR, lockstep execution and `trace.json` do not
change.

---

## 1. Why this story exists

The owner, on the joint-tree page (`lockstep_viewer.html`), which serves both
`domino debug --lockstep` (Domino listing) and `domino easycrypt debug` (EasyCrypt
listing):

> *"In the debug UI, it is quite hard to navigate when you click on a node, scroll on the oracle
> listing resets. Also, one cannot see the left and right oracle listings side by side. My
> suggestion is that the lockstep debugging mode … has 2 * 2 grid style instead of a left and right
> pane. Then the nodes tree is in the first row at top left. Then the left and right listings are in
> the second row and other information such as joint path are in first row at top right. Most
> importantly, I want that when I click on a node, both left and right listing scroll to the head of
> both branches in the left and right listing."*

What the page does today (`src/debug/lockstep_viewer.html`):

- Two columns: `#left` (stuck panel, toggles, tree) and `#detail`.
- Every selection calls `renderDetail`, which runs `detail.innerHTML = ""` and rebuilds everything,
  **both listings included**, as `<details>` sections stacked one under the other at the bottom of
  the detail pane. A listing the reader had scrolled is thrown away on the next click.
- `listingBlock` sets `pre._focus` to the **first** coloured row (usually an executed line near the
  top of the procedure), not to the node's head, and only that row is scrolled into view.
- Left and right listings are never visible at the same time unless the window is very tall.

## 2. Inherited from earlier stories

- `src/debug/lockstep_viewer.rs` fills the template: `__VIEWER_CSS__` and `__EFFECT_JS__` come from
  `src/debug/report.rs` (`VIEWER_CSS`, `EFFECT_JS`), shared with the sequential report.
- Each node has `left`/`right` with `consumed` (line ranges), `head` (`label`, `kind`) and
  `plumbing`. An explored child edge carries per-side `label`/`decision`; a pruned or unexplored
  child is a **cut**. A terminal pair has `pair`, whose sides carry `terminal` (`label`,
  `is_abort`) and `lines`.
- `listingSpec` and `executed` compute what to paint for a path; this story keeps that logic and
  changes only *where* it is applied.
- The URL hash already carries the selection and the tree/detail scroll offsets (`ts`, `ds`), so a
  live page (`<meta http-equiv="refresh">`) keeps its place across reloads.
- Story 24's verification used headless Chrome (`--dump-dom`, screenshots); this story's
  verification does the same.

## 3. Work to do

### 3.1 The grid

```
┌───────────────────────────────── header (one line) ─────────────────────────────────┐
├───────────────────────────────┬──────────────────────────────────────────────────────┤
│ tree pane                     │ detail pane                                          │
│  stuck points (collapsible)   │  heading, verdicts, joint path, solver answers,      │
│  toggles, collapse/expand     │  effect, claim assertion                             │
│  joint tree                   │  (everything it shows today except the listings)     │
├───────────────────────────────┼──────────────────────────────────────────────────────┤
│ left listing                  │ right listing                                        │
│  title bar: side, game,       │  title bar: side, game,                              │
│  oracle, "N lines · M exec."  │  oracle, "N lines · M exec."                         │
│  legend                       │  legend                                              │
│  listing (own scroll)         │  listing (own scroll)                                │
└───────────────────────────────┴──────────────────────────────────────────────────────┘
```

- The page fills the viewport. Each of the four cells scrolls on its own, and the page itself
  never scrolls.
- The header shrinks to one line: title, then the option and summary chips, wrapping only when it
  must.
- **Splitters.** One vertical splitter between the columns, shared by both rows so the two listings
  stay aligned, and one horizontal splitter between the rows. Both can be dragged, and both work
  from the keyboard (focusable; ←/→ or ↑/↓ move them 2 %). Their positions ride in the hash (`gc`,
  `gr`, as fractions), next to `ts`/`ds`. Defaults: columns 50/50, rows 45/55.
- **Narrow windows.** Below 900 px the grid becomes one column in the order tree, detail, left
  listing, right listing. Each cell gets a sensible max height and scrolls on its own, and the
  splitters are hidden.

### 3.2 Listings are built once

- Build both listings once, at page load, from `T.left_listing` / `T.right_listing`, into their
  grid cells.
- A selection **repaints**. It clears and resets each row's class (`exec`, `head`, `ret`, `abort`,
  `cut`) and decision tag (`dtag`) from `listingSpec`, and updates each title bar's "M executed".
  It never removes or rebuilds a row.
- The detail pane may still be rebuilt per selection, as today; only the listings move out of it.
- A listing's scroll offset is the reader's own except for the one scroll a selection makes
  (§3.3). Both offsets ride in the hash (`ls`, `rs`) like `ts`/`ds`, so a live reload does not
  throw the reader back to the top.

### 3.3 A selection brings both listings to the node

Each selection has, on each side, a **target line**:

| What is selected | Target line on each side |
|---|---|
| an inner joint node | that side's `head.label`: the decision point it stands at |
| a terminal pair (joint path) | that side's `pair.<side>.terminal.label` |
| a pruned or unexplored combination | that side's cut label; a side not in the cut keeps its head |
| a stuck-point entry in the stuck panel | the stuck node's heads (the stuck sampling on the stuck side) |

A side that does not move at the selected node is **still** brought to its target, so both
listings always show where each side stands. Scroll each listing so its target line is centred.
Use `behavior: "smooth"`, or `"auto"` under `prefers-reduced-motion`. Give the target row a brief
outline pulse so the eye finds it.

Story 49 changes *which* line is the terminal and adds the waiting side; it does so by changing the
target lines, not this mechanism.

### 3.4 Keyboard navigation in the tree

With focus in the tree:

- **↑ / ↓** select the previous or next *visible* row, exactly as a click would: detail pane and
  both listings follow.
- **→** opens a closed node; on an open node it selects the first child.
- **←** closes an open node; on a closed node or a leaf it selects the parent.
- **Enter / Space** keep their current meaning.

Rows hidden by a toggle (today: "hide plumbing nodes") are skipped.

### 3.5 Shared parts, ready for the sequential report

Put the grid CSS, the splitter code and the persistent-listing code (build once, repaint from a
spec, bring to a target line) in `src/debug/report.rs`, next to `VIEWER_CSS` and `EFFECT_JS`. For
example `GRID_CSS` and `LISTING_JS`, spliced in by placeholders as those two are. The joint-tree
viewer is their first user and the sequential report (symbolic-execution story 20) the second.
Neither page keeps a private copy.

### 3.6 Not in this story

- The sequential report (`report.rs` page): symbolic-execution story 20.
- What is painted in the EasyCrypt listing (single-exit bookkeeping lines, return on
  `return ec_result;`, waiting side, callee annotations): story 49.
- Renaming "plumbing" to "exit guard": story 50.

## 4. Acceptance criteria

- [ ] The page is a 2×2 grid as in §3.1, on both listings (Domino and EasyCrypt). The page body
      does not scroll, and each cell does.
- [ ] Both splitters drag and respond to the keyboard; their positions survive a reload through the
      hash.
- [ ] Below 900 px the cells stack in the order tree, detail, left, right.
- [ ] The listings are created once per page load. Selecting nodes never replaces a listing's
      rows; checked by tagging a row element before a selection and finding the same element after
      it.
- [ ] After a selection, each listing's target line (§3.3 table) is centred in its cell, for each
      row of the table.
- [ ] A listing scrolled by hand keeps its offset until the next selection; the next selection
      re-centres it on the new target.
- [ ] `ls`/`rs` ride in the hash; a live page keeps both listings' offsets across its reload.
- [ ] ↑/↓/←/→ behave as §3.4, and listings follow keyboard selection exactly as clicks.
- [ ] The grid CSS and listing JS live once in `report.rs` and are spliced into the viewer.
- [ ] `trace.json` is byte-identical before and after this story on the verification runs; the
      viewer's page is byte-identical across two runs of an unchanged project.

## 5. How to verify

```sh
D=target/debug/domino
cd example-projects/hello-world-oracle-rename-new
$D easycrypt debug --theorem Proof --proofstep 0 --oracle ChangeNameUsefulOracle
$D debug --proof Proof --proofstep 0 --oracle ChangeNameUsefulOracle --lockstep
```

Headless Chrome (`--dump-dom` plus screenshots at 1600×1000 and at 800×1000) on the EasyCrypt
page of `ChangeNameUsefulOracle`, whose listing is quoted below in the summary's numbering
(left: `medium_composition`, right: `small_composition`):

1. Load with `#n=1`. Left listing centred on **L24** (`if (!(ec_r1 = None))`), right listing
   centred on its head at node 1 (**R10** today; story 49 moves it to **R15**).
2. Scroll the left listing to the top by hand, then press ↓. Node 2 is selected, the left listing
   is centred on **L30** (`rand_2 <$ dbits_n`), and the row element tagged before the key press is
   still in the DOM.
3. Select the terminal pair J1: the left listing is centred on its terminal, the right on its
   terminal.
4. Drag the column splitter to 30/70, reload: it is still 30/70.
5. At 800 px wide: one column, in the order tree, detail, left, right.

Repeat 1–3 on kem-dem `PKENC` (the largest listing story 24 used) and attach the screenshots to the
implementation report.
