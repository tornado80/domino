# Story 49 `easycrypt-listing-painting` — implementation report

## What changed

- **`src/debug/ir.rs`**: `Listing` has two new fields, `lines: Vec<LineInfo>` and
  `frames: Vec<FrameSpan>`. The Domino inliner leaves them empty.
  - `LineRole` (serialised kebab-case): `entry-init`, `router-guard`, `frame-init`, `guard-head`,
    `else-open`, `done-set`, `router-tail`, `router-abort`, `return`.
  - `LineInfo { line, role, frame?, end? }`. `frame` is the open line of the frame of a
    `frame-init` line. `end` is the last line of the block that a `guard-head`, `else-open` or
    `router-tail` line opens.
  - `FrameSpan { open, close, pkg_inst, oracle, result_temp, result_local }`. `result_temp` is
    `None` for a discarded result.
- **`src/writers/easycrypt/lower.rs`**: the lowering records the roles while it lays the listing
  out (`Lowerer::mark`, `mark_in`, `emit_plain_role`). `EcFrame` knows its open line. Each
  inlined call pushes a `FrameSpan`; the table is sorted by open line at the end. The listing
  text and the IR do not change.
- **`src/debug/lockstep_run.rs`**: `LockstepMeta` has `left_lines`, `right_lines`,
  `left_frames`, `right_frames`. `LOCKSTEP_TRACE_SCHEMA` is 11.
- **`src/debug/report.rs`**
  - `LISTING_JS`: a spec has two more fields, `waits: Set` and `tags: Map`. `paintClass` has
    the new class `wait` (after terminal, before head). A row's `dtag` shows the decision and
    the tag, joined by " · ". The new `annotateFrames` runs once per listing at build time:
    hovers on every occurrence of `ec_rN` and `ec_result_N`, end-of-line tags (`.atag`) on
    their `var` lines, on the frame-closing line, on the open line and on the call-result
    guard, and a gutter bracket per frame (`.gut .br`, nested brackets 6 px apart).
  - `GRID_CSS`: styles for `wait`, `.atag`, `.nm`, `.gut`, and the tag-only legend item.
- **`src/debug/lockstep_viewer.html`**
  - `executed` adds `entry-init` and `router-guard` on every path, `frame-init` of each frame
    whose open line is executed, and, for a finished or waiting side, the tail
    (`tailLines`).
  - `tailLines` walks forward from the terminal. It records frame-closing lines and the roles
    `guard-head`, `done-set`, `router-tail`, `router-abort`, `return`. At a `guard-head` or an
    `else-open` it jumps to the block end. At `router-tail` it jumps only when the side did not
    abort. A guard's `end` is its then-close line, so the walk enters the else of a false guard
    (kem-dem: `} else { ec_done <- true; }`).
  - `lineTags`: "result set" / "aborts here" on the IR terminal of an EasyCrypt side,
    "callee returns" / "callee aborts" on each frame-closing line on the path, "waits here" on
    the line a waiting side stands at.
  - `finish`, `waiting`, `endLine`: a side is waiting when its head is a `return`/`abort` and
    the node is not a terminal pair. Its target line, its terminal colour and its waiting
    style go on `return ec_result;` on the EasyCrypt listing and on the head on the Domino
    listing (the Domino listing has no `return` role).
  - Tree row: `headsEl` shows "R waiting at return" in a neutral `.kind` chip. Joint-path
    table: "waiting" and the source of that line.
  - Legend: "waits here" and the tag-only "result set / aborts here (tag)".
- **`docs/stories/easycrypt/49-screenshots/`**: five screenshots (see Verification).

## Design decisions

- The tail is computed in the page, from the roles and frames, as the story asks. Rust gives the
  structure (`end`) and does not compute a tail per terminal.
- Two roles are not in the story's table:
  - `else-open` on `} else {`. Without it the walk cannot leave a then body without entering
    the else body. The viewer never paints it.
  - `done-set` on every `ec_done <- true`. EasyCrypt runs it after `ec_result <- Some e` and in
    the else of a false call-result guard after a callee abort. The walk paints it only there.
- The `router-abort` and `guard-head` lines are IR-labelled too. They keep their `SiteInfo`; the
  role is extra information.
- "callee aborts" when the side aborted and the terminal is in `(open, close]`; else "callee
  returns" when the close line is executed. A prefix inside a callee gets no tag.
- The "result set" tag is put only where the terminal is not the `return` line itself, so the
  Domino listing keeps its old paint.
- Static annotations (`.atag`) are built once and are separate from the per-selection `.dtag`,
  so a repaint does not remove them.

## Rejected shapes

- A precomputed tail per IR terminal in `trace.json` (`left_tails`). It is simpler for the page
  and testable in Rust, but the story limits the trace to four new fields, and the tail follows
  from the structure the page has already.
- Finding blocks in the page by brace or indent counting on the listing text. It depends on the
  renderer's layout. The `end` field states the structure.
- A `waiting` flag on `listingSpec`. The spec gets a `waits` set, like `heads` and `cuts`.

## Verification

- Tests first: the four role/frame tests did not compile before `LineRole`/`FrameSpan` existed.
- Baseline before the change: `cargo test` 604 passed, 0 failed, 5 ignored.
- After: `cargo test` 609 passed, 0 failed, 5 ignored. `cargo clippy --all-targets`: 0 warnings.
- New tests (`src/writers/easycrypt/lower/tests.rs`):
  - `two_inlined_calls_have_their_roles_and_frames` (ChangeName left: exact roles and frames);
  - `an_oracle_without_calls_has_router_roles_only` (ChangeName right);
  - `nested_calls_and_aborts_have_their_roles_and_frames` (kem-dem `PKENC`: nested frames, the
    mid-body abort `ec_done <- true` in a guard's else, a fall-through abort at each frame
    close and at the router);
  - `every_role_names_the_line_it_is_on` (all four story-08 cases);
  - `roles_and_frames_serialise_for_the_viewer`.
- Export tree: `domino easycrypt export --force` with the binary before and after, on
  hello-world-oracle-rename-new and kem-dem-cca-ssp, into separate directories: `diff -r` is
  empty (26 files).
- Headless Chrome, with a probe that dumps each row's class and tag:
  - ChangeName (EasyCrypt), J1: left L14–16, L19, L28, L38 executed, L42 **return**, L39 not
    painted, L35 "result set", L23 and L32 "callee returns". Right R5–R7, R11 executed, R12 not,
    R15 **return**, R10 "result set".
  - ChangeName nodes 1–3: tree "R waiting at return", table "waiting / return ec_result;",
    R15 `wait` with "waits here", no right row `head`.
  - Domino-listing variant (same trace, `*_lines`/`*_frames` empty): node 1 right R10 is `wait`
    with "waits here", J1 unchanged (L35 and R10 **return**).
  - Hover on `ec_r1`: "ec_r1: result of rand.UsefulOracle (call at L17)". The left bracket for
    `rand.UsefulOracle` covers L17–L23 (and L26–L32 for the second call).
  - Callee abort (synthetic, see Deviations), kem-dem `PKENC` J1 ending at L77: L77 "aborts here
    · callee aborts", L78 guard head executed, L79–L80 not, L82 `ec_done <- true` executed,
    L118 guard head executed, L119–L120 not, L124 and L125 executed, L128 **abort**.
  - Screenshots: `changename-ec-J1.png`, `changename-ec-node1.png`, `changename-ec-node3.png`,
    `changename-domino-node1.png`, `pkenc-callee-abort-J1.png`.

## Deviations and notes

- `cvc5-lib` does not build on this machine (no `cmake`), so §5's `domino easycrypt debug` and
  `domino debug --lockstep` were not run. As in story 48, the pages were rendered from the
  `trace.json` files in `_build`. The four new fields were added from the lowering of this
  commit (the listings in the old traces are byte-equal to the new lowering, checked). The old
  ChangeName trace (schema 9) also got empty `claims`/`goals`.
- No Domino-listing lockstep trace exists in `_build`. The Domino display was checked on the
  ChangeName trace with the role and frame tables emptied, which is what the Domino listing
  sends.
- No trace in the repository has a path that aborts in an inlined callee: in kem-dem `PKENC`
  every callee returns. The abort case was checked on a copy of the kem-dem trace with J1 moved
  to node 8 and its left terminal set to the fall-through abort at L77. The story asked for a
  real path.
- The trace-schema test in `lockstep_run.rs` (now 11, and checks the four fields) is under
  `cvc5-lib` and did not run here.
- The story's role table has seven roles; two more (`else-open`, `done-set`) were needed. See
  Design decisions.

## Open items

- Re-run §5 with `cvc5-lib`: both pages, the Domino listing, and an oracle that really aborts in
  an inlined callee (a small test project would do; none exists yet).
- The gutter bracket is 2 px wide and close to the line numbers; the owner may want it more
  visible.
- Story 50 renames "plumbing" in the UI.
