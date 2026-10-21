# Story 33 — `domino debug --package P`: the package tree on the Domino listing

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 32, 29.
**Blocks:** nothing.
**ADR:** 0021; 0017 (imports are open calls); 0016.
**Decisions:** grilling of 2026-10-21/22, Questions 4–9, 14, 15.

A **debugger** story, Rust only. Test-first.

---

## 1. Why this story exists

When `domino prove --package P` fails, the owner gets one verdict for each oracle. The package tree
of story 29 shows the failing path, but only on the **EasyCrypt listing**
(`domino easycrypt debug --pkg-inv P --theorem T`). After this story:

```
domino debug --package P [--oracle O] [--claim <name>]
```

runs one-sided execution of each oracle of P on the **Domino listing**, with P's parameters free and
each import call an open call, with no theorem.

The new part is the open call on the Domino listing. Today only the EasyCrypt lowering makes
`InlStmt::OpenCall` (`src/writers/easycrypt/lower.rs:1227`). The Domino inliner gives
`InlineError::UnresolvedEdge` for an `invoke` with no edge.

### What an open call is (for the reader of this story)

A package can import an oracle. In a composition, the import is wired to a real package, and the
inliner puts that code in place of the call. When a package is checked alone, nothing says which
package provides the import. The invariant must hold for every provider (ADR 0016), so the call can
return any value of its type or abort, but it cannot write the calling package's state. That call is
an **open call** (`CONTEXT.md`).

Vocabulary (`CONTEXT.md`): **Open call**, **Package tree**, **One-sided execution**.

## 2. Inherited

- Story 29: `src/debug/pkg_run.rs` (`run_pkg_command`, `pkg_oracles`, `pkg_debug_dir`), the
  package tree on the EasyCrypt listing, the claims `package-invariant!<name>!<P>!` under
  `no-abort`.
- Story 75 of the EasyCrypt epic: `PackageInvariantContext`, `open_game_theorem` (the package alone,
  parameters free), `Error::OpenCallInLoop`.
- Story 32: the listing kind from the command, the `--game` flag set, `!game!` layout and
  `Level::Game`.
- `src/debug/ir.rs:179`: `InlStmt::OpenCall { label, bind, ty }`. "It is not a decision point."

## 3. Work to do

### 3.1 Open calls in the Domino inliner

- For an `invoke` with **no edge**, the Domino inliner makes `InlStmt::OpenCall`, as the EasyCrypt
  lowering does. It finds the import in the caller's import interface; an `invoke` of a name that the
  caller does not import is still `UnresolvedEdge`. No caller passes a flag that says "treat calls as
  open": the inliner decides from the missing edge (as story 29 decided).
- `bind` gets a **fresh value of the import's return type**. There is no `Maybe` wrapper and no
  call-result guard on the Domino listing: the listing shows only the code that the package has.
- The listing line is the call as written, `y <- invoke Get(x)`, with a mark "open call". The
  executor does not change: an open call stays a statement that is not a decision point.
- The abort outcome of an open call is **not a path**. An abort ends the oracle, and every check is
  under `no-abort`, so an abort has nothing to check. The viewer (at each open call) and
  `summary.txt` (one line) say: "an open call can also abort; an abort ends the oracle and has
  nothing to check".
- In a composition every `invoke` has an edge, so two-sided runs and `debug --game` get no open
  calls.

### 3.2 The CLI and the run

- `Debug` gets `--package <P>`, with the same accepted and refused flags as `--game` (story 32), and
  it conflicts with `--game`. Help text: "One-sided execution of each oracle of this package on the
  Domino listing, with its parameters free and each import call an open call. Needs no theorem. The
  start check is `domino prove --package P --invariant-start`."
- The listing is the package template with free parameters (`open_game_theorem`), not a package
  variant: variants exist only in the EasyCrypt export.
- The base frame and the claims come from `PackageInvariantContext`, as in `pkg_run.rs`. `--claim
  <name>` is the exact declared name; an unknown name lists the package's invariants.
- Errors: no package named P (list the packages, as `UnknownPackage`), P has no invariant
  (`NoInvariant`), P has no oracle O, an open call in a loop (`OpenCallInLoop`).

### 3.3 Output and index

- The run directory is `<root>/!package!/<P>/<O>/<claim-dir>/`, the same artifacts as story 32.
- A new index level `Level::Package { package }`, directory `<root>/!package!/<P>/`, parent
  `Level::Project`. The project index lists one row `package  <P>` for each package with a run on
  disk, after the `game` rows.
- The viewer's one-column mode says "package invariants of `<P>`".

## 4. Rejected alternatives

- **The abort of an open call as a path** (Question 9, B): the executor must learn a mode for the
  Domino listing only, and each open call adds an end with nothing to check.
- **The EasyCrypt shape on the Domino listing** (Question 9, C): a `Maybe` result and a synthetic
  guard `if r == None { abort }` are lines that the package does not have.
- **The package tree only on the EasyCrypt listing:** the owner must then read EasyCrypt code to
  debug a Domino package invariant.
- **A caller flag "treat calls as open":** the inliner can see the missing edge itself (story 29).
- **`_build/debug/PkgInv_<P>/`** (Question 8): a theorem can have that name, and the glossary keeps
  EasyCrypt names off the Domino listing.

## 5. Tests first

- [ ] Red: `testdata/debug/se29`, `debug --package Ctr --oracle Bad`: the call `y <- invoke Get(x)`
      is an open call; the tree splits on `x < 0`; the terminal with `x < 0` fails `nonneg`, the
      other verifies.
- [ ] `--oracle Step`: one path, it verifies (`ctr <- 1` after the call). There is no abort path.
- [ ] `--oracle Ping`: the bare call `invoke Put(ctr)` is an open call with no bind; it verifies.
- [ ] Agreement: for each oracle of `Ctr`, the claims that fail are the same as in
      `easycrypt debug --pkg-inv Ctr` and in `prove --package Ctr`.
- [ ] The Domino listing of `Bad` shows the call as written, with the open-call mark, and has no
      call-result guard. `summary.txt` has the abort line.
- [ ] An `invoke` of a name that the package does not import is still `UnresolvedEdge`.
- [ ] A two-sided `domino debug` run and `debug --game` on a composition with wired imports have no
      open calls (an existing test, or a new one on `test-projects/test-side-invariant-from-package-lemmas`).
- [ ] The directory is `_build/debug/!package!/Ctr/Bad/!all-claims!/`; the project index lists
      `package  Ctr`.
- [ ] `--claim nope` lists `nonneg`; `--package X` where X has no invariant gives `NoInvariant`.
- [ ] clap refuses `--package` with `--game` and with each flag of the refused list of story 32.

## 6. Acceptance criteria

- [ ] All tests of §5 green.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget (`ir.rs` in particular).
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 7. How to verify

```bash
cd testdata/debug/se29
$D debug --package Ctr && open _build/debug/!package!/Ctr/Bad/!all-claims!/index.html
$D prove --package Ctr          # Bad fails, as in the tree
```
