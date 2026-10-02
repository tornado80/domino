# Story 19 follow-up — implementation report: renamed oracles and game sources in the HTML viewer

**Status:** done (requested in conversation). Branch `amir/html-viewer`, commit `3a8ac40b`.

## 1. The problem

A composition can expose an oracle under a different name than the package gives it:

```
compose {
    adversary: { AnotherUsefulOracle: UsefulOracle of rand, },
    fwd:       { O: UsefulOracle of rand, },
}
```

`New: Old of inst` exports `inst.Old` as `New`, or wires the caller's import `New` to
`inst.Old`. In the model the new name is the `alias` of an `Export` or `Edge`, and `sig.name`
is the package's name.

The viewer lost the old name everywhere:

- **Diagram.** The arrow showed only `New` (`Export::name()` / `Edge::name()`).
- **Listings.** Row `AnotherUsefulOracle` was headed by `UsefulOracle() -> …`, the package's
  signature. A renamed call read `// inlined rand.UsefulOracle`, and the `O` the caller invokes
  appeared nowhere.

Labels had a second, older problem: they were centred on their arrow, and the solver layout
reserves no room for label width. A label wider than its arrow ran under the boxes, which are
drawn after the labels. On an export arrow it ran past the SVG's left edge and was clipped. In
`hello-world-oracle-rename`, `small_composition` showed `notherUsefulOra`. Renaming makes labels
longer, so this had to be fixed too.

Separately, the side pane could show a package's source but not the game's.

## 2. What the page shows now

### Diagram labels

A renamed oracle reads `New:Old`, with `:Old` in a new `--ren` colour (orange). The hover title
is `New: Old of inst (the package calls it Old)`. The header legend gains `New:Old renamed
oracle`. Where a stack of labels goes depends on whether its widest full label fits the arrow
(`Arrow::fit`):

| Case | Placement |
|---|---|
| Fits (`Centred`) | centred on the arrow, as before |
| Export arrow, too wide (`AtHead`) | right-aligned 6px before the arrowhead, running left into the adversary side |
| Package-to-package arrow, too wide (`Short`) | centred, with each renamed label shortened to `New` in the renamed colour; the hover keeps the full form |

`AtHead` is safe with the solver layout. The SMT encoding (`graph.rs`) forbids any package box
within half a unit (25px) of an arrow's height between its two columns, and the labels sit
4–18px above the arrow. The fallback layout gives no such guarantee (§4), so there only
exports into the first package column are `AtHead`.

Label widths now count toward the SVG bounds, at an estimated 6.2px per character (10px
monospace), so no label is clipped at the diagram's edge.

### Listings

```
// AnotherUsefulOracle: UsefulOracle of fwd
AnotherUsefulOracle() -> (Integer, Bits(n)) {
    // inlined O: UsefulOracle of rand
        rand.ctr <- (rand.ctr + 1);
        …
```

The signature line carries the exported name, so it matches the row. A renamed export is
preceded by the composition's line. A renamed call is inlined as `// inlined Import: Old of
inst`. Calls without a rename keep `// inlined inst.Oracle`, and goto labels
(`end_inst_Oracle`) are unchanged.

### Game source in the side pane

The game name in a column header (`game MediumComposition`, dotted underline) opens the side
pane. The pane shows:

- the game's source, highlighted, with `instance`, `compose`, `adversary` and `of` added to the
  keywords
- its file name
- the game instance's constants as `name: Type = value`, with the proof path's assignments
  substituted and the hybrid loop variable named as declared

The instance name is not clickable.

## 3. Changes

| File | Change |
|---|---|
| `src/package.rs` | `Composition` gains `file_name` and `file_contents`, as `Package` has. |
| `src/parser/composition.rs` | `into_game` fills them from the parse context. |
| `src/theorem.rs` | Game instantiation copies them. |
| `src/debug/view.rs` | Entry signature uses the export name, preceded by `// New: Old of inst` when renamed. A renamed edge is inlined as `// inlined Import: Old of inst`. Module doc updated. |
| `src/writers/html.rs` | `OracleLabel` (name and optional `(old, inst)`) replaces `String` labels. `Arrow` with `fit` / `label_span` replaces the `(x0, x1, y, labels)` tuple. `LabelFit` decides placement. The bounds include label widths. `.gamelink` header, `game_params_text`, hidden `pre.gamesrc` sources, and the pane's `openSource` shared by `openPkg` / `openGame`. `--ren` colour and legend entry. |

Test: `renamed_oracles_read_as_in_the_composition` is a snapshot of `AnotherUsefulOracle` in
`big_composition` of `hello-world-oracle-rename`. It covers a renamed export (`… of fwd`) that
inlines a renamed edge (`O: … of rand`).

## 4. The solver-free layout, for reference

`--no-solver`, or a failed solver layout, uses `fallback_geometry`. It is simple and, as its doc
says, only a fallback:

1. **Columns by call depth.** Each package starts at depth 1 (the adversary is column 0). A
   Bellman-Ford-style relaxation, `depth[to] = max(depth[to], depth[from] + 1)` over all edges,
   repeats `n` times. That gives each package the length of the longest call chain from the
   adversary. A cap at `n + 1` stops a cyclic composition from growing forever. A package's x is
   `depth × 3.5`.
2. **Stacking within a column.** Packages fill slots in declaration order. Slot `k` has its top
   at `−1.6k` and a height of 1, so every box is the same size.
3. **Arrows.** There is one horizontal arrow per (caller, callee) pair, plus one per exported
   package from x = 0. It is drawn at the *callee's* mid-height and starts at the caller's right
   edge, or at 0 for an export.

Nothing keeps arrows clear of boxes. An arrow skipping a column passes behind whatever sits at
that height. An arrow may start beside, not on, its caller when the callee's mid-height is
outside the caller's box. Two arrows into packages at the same slot share a height, so their
labels collide. In `hello-world-oracle-rename`, `UsefulOracle` (into `fwd`) and
`AnotherUsefulOracle` (into `rand`, behind `fwd`) overlap in both the old and new pages.

The solver layout (`GraphLayout`, shared with the LaTeX export) encodes in QF_LIA:

- integer columns and box bottoms and tops
- each arrow's height inside both endpoints' boxes
- callers left of callees
- no two boxes overlapping in a column
- no box within one half-unit of an arrow's height between that arrow's columns

It then binary-searches the smallest width, and then the smallest height at that width. The
result is cached in `_build/graph`.

## 5. Verification

- **Page comparison.** `domino html --no-solver` was run with the binary from `6746b2e9` and
  with `3a8ac40b`, on every example project outside `archive/`. Every page changes in its header
  (game links, legend), styles and script. Listings and diagram labels were compared per cell:

  | Page | Listings changed | Renamed headers | Renamed calls | Renamed labels (short) | `AtHead` stacks |
  |---|---|---|---|---|---|
  | hello-world-oracle-rename `Proof` | 20/28 | 12 | 12 | 11 (5) | 4 |
  | hello-world-oracle-rename-new `Proof` | 24/28 | 20 | 12 | 15 (5) | 6 |
  | yao `Yao` | 8/20 | 0 | 8 | 4 (4) | 0 |
  | yao `Yao3Layer` | 8/24 | 0 | 24 | 12 (0) | 0 |
  | yao `HybridSecurity` | 4/88 | 0 | 4 | 2 (2) | 0 |

  Counts cover both the full and the lossy listing. Every changed listing line is one of the
  rename forms above; no other line differs. Label text differs only on renamed labels. The 13
  other pages have identical listings and labels.
- **Rendering.** Headless-Chrome screenshots of `hello-world-oracle-rename` (solver and
  fallback layouts) and yao `Yao3Layer` (solver). Before, the export labels in `small_composition`
  were clipped and the `O` edges hidden under boxes. After, every label is readable: `GBL3:GBL` in
  yao fits between packages, and `O` shortens to the new name. The game pane opens with
  `MediumComposition.comp.ssp`.
- **Pre-existing failures.** `ae`, `ae-mini`, `nprf` and `rosenpass-basic` fail with the same
  parse or type error on both binaries.
- **Workspace checks.** `cargo test --workspace`: 163 passed, 4 ignored. `cargo clippy
  --workspace --all-targets`: no warnings in the changed files. `cargo fmt` is clean.

## 6. Known limitations

1. **Label width is estimated.** 6.2px per character assumes the 10px monospace font. A
   proportional fallback font could still overflow slightly.
2. **`Short` hides the old name until hover.** Between two packages there are 75px, which is too
   little for most `New:Old` pairs. The listing's `// inlined New: Old of inst` line and the game
   pane carry the full form.
3. **The fallback layout still overlaps** (§4). This change only avoids making it worse.
4. **The game pane shows the source as written.** Renamed lines are not highlighted in it.
