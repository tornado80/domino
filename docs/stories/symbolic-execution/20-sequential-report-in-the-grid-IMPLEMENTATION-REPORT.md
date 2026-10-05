# Story 20 `sequential-report-in-the-grid` — implementation report

## What changed

- **`src/debug/report.rs`**
  - `render_html` splices `GRID_CSS` and `LISTING_JS` (story 48) into the sequential page. The
    page has no private copy of the grid CSS or the listing code.
  - The page is the 2×2 grid: `#cell-tree` (filter, verdict toggles, collapse/expand, path
    tree), `#cell-detail` (path tables, effect, claim assertion, model, SMT asserted),
    `#cell-left` and `#cell-right` (the listings), and the two splitters.
  - `listingBlock` is removed. The two listings are built once at load (`listings.left`,
    `listings.right`). `pathSpec(path)` turns a path, a right-branch prune or a top-level
    left-branch prune into the spec of `paintListing`: executed lines, decisions, and the
    terminal (or the cut line of a prune).
  - `showListings(lp, rp)` runs on each selection. It paints the left listing with `lp` and
    brings it to `lp.terminal.label`. With `rp`, it paints the right listing with `rp` and brings
    it to `rp.terminal.label`. Without `rp`, it paints the right listing with `CLEAR_SPEC`, does
    not scroll it, and its title bar reads "no right path selected". A top-level left-branch
    prune is passed as `lp`, so its cut line is the left target.
  - `renderDetail` no longer adds listing sections. `sec` no longer centres a listing.
  - Keyboard in the tree: `.lp-head` and `.rp` rows are focusable. ↑/↓ go to the previous/next
    visible row, → opens a left path or goes to its first visible right row, ← closes a left
    path or goes from a right row to its left path. A key press focuses and clicks the row.
    Rows hidden by the filter, a verdict toggle or a collapsed parent are skipped.
    `setCollapsed` is the one place that collapses a node and sets its twist.
  - The hash carries `p` (the selected row's path id), `gc`/`gr` (splitters, defaults
    0.42/0.45) and `ls`/`rs` (listing offsets). A load selects `p` (which centres the
    listings) and then applies `ls`/`rs`.
  - `VIEWER_CSS`: the `#left` and `#detail` rules are removed; `#cell-detail h2` /
    `#cell-detail .path-sub` and the `cut` legend swatch move here. The legend has "branch cut".
- **`src/debug/lockstep_viewer.html`**: the two rules that are now in `VIEWER_CSS`
  (`.legend-item.cut` swatch, `#cell-detail .path-sub`) are removed.
- Two new tests: `the_sequential_page_is_the_grid_from_the_shared_code` and
  `the_sequential_page_keeps_no_private_listing_code`.
- **`docs/stories/symbolic-execution/20-screenshots/`**: screenshots and the synthetic trace.

## Design decisions

- The selection goes in the hash as the path id (`p=1.1`), not as tree indices. Path ids are
  stable and unique for left paths, right paths and both kinds of prune.
- The detail cell is still rebuilt on each selection. The story requires persistence only for
  the listings.
- The default column fraction is 0.42, the old width of `#left`.

## Rejected shapes

- A `side` parameter on a shared "show one listing" function with a flag for "clear": the right
  listing has two cases (path or clear). `showListings` handles them with one early return.
- Keeping `listingBlock` and adding the grid cells around it: this rebuilds the rows on each
  selection, which the acceptance criteria forbid.

## Verification

- Tests were written first (red: no `__GRID_CSS__`/`__LISTING_JS__`, `listingBlock` present).
- Baseline before the change: `cargo test` 620 passed, 0 failed, 5 ignored.
- After: `cargo test` 622 passed, 0 failed, 5 ignored. `cargo clippy --all-targets`: 0 warnings.
- Headless Chrome (`--force-prefers-reduced-motion`), page rendered from a synthetic trace with a
  probe script appended:
  - Left path #1: left centred on L120; right listing has 0 coloured rows, its offset stays 40,
    title "no right path selected".
  - Left scroll set to 0 by hand, then right path #1.1: left re-centred on L120, right on R132.
    A row tagged before the selection is the same element after it.
  - Right-branch prune #1.p1: right centred on the cut line R90.
  - Top-level left-branch prune #p1: left centred on the cut line L45; right cleared, offset
    unchanged.
  - Keys from #1: → 1.1, ↓ 1.2, ↓ 1.p1, ← 1, ← (collapses 1), ↓ 2, ↑ 1. With 1 collapsed, →
    opens it and stays on 1.
  - Five ↑ presses on the row splitter give `gr=0.35`. A load with `#p=1.1&gr=0.35&ls=300&rs=150`
    gives row fraction 35 % and listing offsets 300 and 150. A hand scroll writes `ls` into the
    hash.
  - The page body does not scroll. At 1600 px the cells are a 2×2 grid; at 800 px they stack.

## Deviations and notes

- `domino debug` needs the `cvc5-lib` feature, which does not build on this machine (no
  `cmake`). There is no sequential `trace.json` in `_build`. So the page was rendered from a
  synthetic trace (`20-screenshots/synthetic-trace.json`): the real kem-dem `PKENC` EasyCrypt
  listings from the lockstep trace, with hand-made paths (two left paths, three right paths, a
  right-branch prune, a top-level left-branch prune). The render used a temporary test that
  called `render_html`; it is not committed.
- "`trace.json` byte-identical" is checked only by construction: no Rust code that writes the
  trace changed. Page determinism is covered by `html_is_byte_identical_across_runs`.
- Drag was not checked in a browser, only the keyboard path of the splitter. Both call `move`.
- Smooth scrolling was not checked (headless virtual time does not advance it).

## Open items

- Re-run §5 with `cvc5-lib` on a machine with `cmake`, on a real sequential run, with smooth
  scrolling and a mouse drag.
