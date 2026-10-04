# Story 48 `debug-viewer-grid` — implementation report

## What changed

- **`src/debug/report.rs`**: two new shared constants, next to `VIEWER_CSS` and `EFFECT_JS`.
  - `GRID_CSS` (spliced at `__GRID_CSS__`): the one-line header, the 2×2 grid `main.grid` with the
    cells `#cell-tree`, `#cell-detail`, `#cell-left`, `#cell-right`, the column splitter (shared
    by both rows) and the row splitter, the listing cell layout (title bar, legend, own scroll),
    the target-row outline pulse, and the one-column layout below 900 px (order tree, detail,
    left, right; splitters hidden; each cell has a max height and scrolls).
  - `LISTING_JS` (spliced at `__LISTING_JS__`): `makeListing` builds a listing once into its
    cell; `paintListing` resets each row's class (`exec`, `head`, `ret`, `abort`, `cut`) and
    `dtag` from a spec and updates "N lines · M executed"; `bringListingTo` centres a line
    (`smooth`, or `auto` under `prefers-reduced-motion`) and pulses its row; `initGrid` and
    `bindSplitter` make the splitters drag and move 2 % per arrow key.
- **`src/debug/lockstep_viewer.html`**
  - The page is the 2×2 grid. The tree cell holds the stuck panel, the toggles and the tree. The
    detail cell holds everything it held before except the listings.
  - `listingBlock` is removed. Both listings are built once at load (`listings.left`,
    `listings.right`). `showListings` repaints them from `listingSpec` on each selection and
    brings each one to its target line (`targetLine`: cut label, else the terminal of the joint
    path, else the head; a side that is not in the cut keeps its head). A stuck-point entry
    selects the stuck node, so its heads are the targets.
  - Keyboard in the tree: ↑/↓ select the previous/next visible row, → opens a node or selects its
    first child, ← closes a node or selects the parent. A key press focuses and clicks the row,
    so the detail pane and the listings follow exactly as for a click. Rows hidden by "hide
    plumbing nodes" are not visible, so they are skipped.
  - The hash carries `gc`/`gr` (splitter fractions, defaults 0.5/0.45) and `ls`/`rs` (listing
    scroll offsets) next to `ts`/`ds`. A restore selects the node (which centres the listings)
    and then applies `ls`/`rs` when the hash has them, so a live reload keeps the reader's place.
- **`src/debug/lockstep_viewer.rs`**: `render_html` splices `GRID_CSS` and `LISTING_JS`. Two new
  tests: `the_grid_and_the_persistent_listings_are_spliced_from_report` and
  `the_viewer_keeps_no_private_copy_of_the_listing_code`.
- **`docs/stories/easycrypt/48-screenshots/`**: screenshots at 1600×1000 and 800×1000 of
  `ChangeNameUsefulOracle` (EasyCrypt) and kem-dem `PKENC`, with `#n=1`.

## Design decisions

- `paintClass` keeps the old precedence: cut over terminal over head over executed.
- Every selection brings the listings to their targets, also on a restore. Only an `ls`/`rs` in
  the hash overrides it. So `#n=1` centres the listings on load, and a live reload keeps the
  reader's own offsets.
- The splitters write fractions with two decimals and clamp them to 0.1–0.9.
- `LISTING_JS` takes the legend element from its caller. The joint-tree legend has "decision
  point here" and "cut", which the sequential legend does not have.

## Rejected shapes

- A `bring` (or `keepScroll`) flag on `showListings`: a restore would then not centre the
  listings at all. Instead, every selection brings, and the hash offsets are applied after it.
- Rebuilding the rows per selection and restoring the scroll offset afterwards: this still
  replaces the row elements (the acceptance test tags a row) and flickers on large listings.

## Verification

- Tests were written first (red: `GRID_CSS`/`LISTING_JS` did not exist), then green.
- Baseline before the change: `cargo test` 602 passed, 0 failed, 5 ignored.
- After: `cargo test` 604 passed, 0 failed, 5 ignored. `cargo clippy --all-targets`: 0 warnings.
- Headless Chrome, with a probe script appended to a copy of the page:
  - ChangeName, `#n=1`: left centred on L24, right shows R10 (head row painted; R10 is too near
    the top to be exactly centred, the centre row is R11). ↓ after a manual scroll to the top:
    node 2, left centred on L30; the row tagged before the key press is the same element after.
    J1: left shows L35 (centre row L34, the scroll is at its end), right R10.
  - PKENC: J1 centres L120 and R132 exactly. The tagged row survives ↓.
  - The page body does not scroll. At 1600 px the cells are a 2×2 grid; at 800 px they stack
    in the order tree, detail, left, right.
  - Ten ← presses on the column splitter give `gc=0.3`. A load with `#gc=0.3&ls=300&rs=150`
    gives a tree column of 477 of 1600 px and listing offsets 300 and 150.

## Deviations and notes

- The verification commands (`domino easycrypt debug`, `domino debug --lockstep`) need the
  `cvc5-lib` feature, which does not build on this machine (no `cmake`). The pages were rendered
  instead from the `trace.json` files already in `_build`, by the same placeholder splice. The
  ChangeName trace is from an older format (no `claims`/`goals`), so the scratch copy had those
  fields added as empty. Because no new run was made, the "`trace.json` byte-identical" criterion
  is checked only by construction: this story does not touch any Rust code that writes the
  trace. Page determinism is covered by `rendering_is_a_pure_function_of_its_inputs`.
- Headless Chrome does not advance a smooth scroll in virtual time, so the probes ran with
  `--force-prefers-reduced-motion` (the `auto` path). The smooth path uses the same target.
- Neither verification trace has a pruned/unexplored child or a stuck point, so those rows of the
  §3.3 table were not checked in a browser.
- Drag was not checked in a browser (only the keyboard path and the restore). Both paths call the
  same `move`.
- The Domino-listing page was not checked in a browser; it is the same template.

## Open items

- Re-run §5 with `cvc5-lib` on a machine with `cmake`, with smooth scrolling, on the Domino
  listing, and on a trace with a stuck point and a pruned child.
- Symbolic-execution story 20 is the second user of `GRID_CSS` and `LISTING_JS`.
