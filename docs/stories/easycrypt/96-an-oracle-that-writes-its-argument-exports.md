# Story 96 — An oracle that writes its argument exports to EasyCrypt

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** nothing.
**Blocks:** nothing.
**ADR:** none. The change is easy to undo, and it does what the debugger listing does already. The
rejected alternatives are in §5.
**Decisions:** owner's grilling session of 2026-10-29, Questions 1 to 3. The term
**Oracle argument** is in `CONTEXT.md`.

A **writer** story: `src/writers/easycrypt/package.rs`, a new fixture and its tests. Test-first.

---

## 1. Why this story exists

An oracle body can write to its own argument. The Domino front end accepts this, and the SMT
prover and the debugger handle it. The first real case is `MAC.Init` in the Full4WHS model
(`ec4whs`, commit `bc97150`):

```
oracle Init(handle: (Integer, Integer, Integer, Bits(n), Bits(n)),
            key: Bits(n),
            hon: Bool) {
    if (Keys[handle] == None) {
        if hon {
            key <-$ Bits(n);
        }
        Honesty[handle] <- Some(hon);
        Keys[handle] <- Some(key);
    }
}
```

The EasyCrypt export of this oracle declares `key` two times:

```
proc d_Init(handle : (int * int * int * bits_n * bits_n), key : bits_n, hon : bool) : unit option = {
  …
  var key : bits_n;
```

`build_proc` (`src/writers/easycrypt/package.rs:760`) declares the oracle arguments as proc
parameters. Then `collect_locals` and `record_local` (`package.rs:665`, `package.rs:729`) declare a
`var` for each name that the body assigns. They do not skip a name that is a parameter. EasyCrypt
rejects the file:

```
In external theory Pkg_MAC [Pkg_MAC.ec: line 20 (8-11)]:
duplicated local/parameters name: `key'
```

Each job that requires a composition with this package stops before it proves anything. In
Full4WHS these are game hop 11 (`H6_1_1 == H7_0`), game hop 13 (`H7_1_1_0 == H7_1_1_1`) and
`--game H7`.

## 2. The facts this story uses

- **EasyCrypt accepts a write to a proc parameter.** This compiles (tested on 2026-10-29):

  ```
  module M = {
    proc f(k : bool, hon : bool) : bool = {
      if (hon) { k <$ {0,1}; }
      return k;
    }
  }.
  ```

  Only the second declaration is wrong. The write itself is correct EasyCrypt.
- **EasyCrypt passes arguments by value**, as Domino does. A write to a parameter changes only the
  copy of that call. The caller (the composition's proc, the router) does not see it.
- **The debugger listing does this already.** `LocalNames::resolve` (`lower.rs:404-450`) claims
  the name of each argument of a frame before the body. A later write in the same frame resolves
  to the same name, and `declare` is false for the listing proc's own parameters. The listing
  therefore writes to the argument and has no second `var` line.

## 3. What to build

In `src/writers/easycrypt/package.rs`:

- `record_local` does not declare a name that is a parameter of the proc. Match on the
  **EasyCrypt** name, as `seen` does already: `build_proc` mangles the arguments, and
  `record_local` mangles the local through the same `PackageScope`, so the two spellings are equal.
  One way: `build_proc` puts the mangled argument names into `seen` before it calls
  `collect_locals`. Then `record_local` skips them as it skips a local that it has seen.
- The body is not changed. A write to the argument stays a write to the parameter.

The forms of write to cover:

| Domino | EasyCrypt |
|---|---|
| `x <- e` | `x <- e;` |
| `x <-$ T` | `x <$ d…;` |
| `(x, y) <- e` (a tuple pattern that contains the argument) | `(x, y) <- e;`, and `var` only for `y` |
| `T[i] <- e` where `T` is an argument | no change: `Pattern::Table` declares nothing |

`lower.rs`, `check-alignment`, the tactics and the side-invariant writers do not change.

## 4. Tests first

A new fixture `testdata/easycrypt/story96/`: one theorem with one equivalence (two compositions
that use the same package are sufficient). The package has one oracle that:

- samples into its argument when a boolean argument is true (the shape of `MAC.Init`),
- assigns its argument (`x <- …`),
- assigns a tuple pattern that contains its argument and a new local.

- [x] Unit test in `package.rs`: the rendered proc of that oracle has no `var` line for an
      argument, and has exactly one `var` line for the new local of the tuple.
- [x] Unit test: the body still writes to the argument (`x <$`, `x <-`, `(x, y) <-`).
- [x] Compile test in `export.rs`: `story96_full_tree_compiles_in_dependency_order`, with
      `assert_tree_compiles` (it skips without `easycrypt`).
- [x] The existing full-tree compile tests stay green: an oracle that does not write its argument
      gives the same text as before.

## 5. Rejected alternatives

- **A fresh local, with a copy of the argument at proc entry** (`var key_0; key_0 <- key;`, and
  each later use of `key` becomes `key_0`). This was the first proposal. EasyCrypt does not need
  it: it accepts a write to a parameter (§2). The module and the debugger listing would then be
  different, so `lower.rs`, `check-alignment` and the lockstep walk must change in the same way
  (change amplification). Each affected oracle also gets one more statement to prove. Compilers
  add such a copy only when the target forbids a write to a parameter (Ada `in` parameters,
  GNAT "assignment to "in" mode parameter not allowed"), or needs its address (Clang's allocas
  for arguments, LLVM bug 20419). EasyCrypt has neither limit.
- **A hygienic rename** (Erdweg et al., *Capture-Avoiding and Hygienic Program
  Transformations*, ECOOP 2014). This is the correct tool when two *different* variables clash.
  Here the argument and the assigned name are *one* variable, and a rename hides that.
- **Sync `example-projects/4WHS` with the owner's `ec4whs/4WHS`, so that
  `full_4whs_full_tree_compiles_in_dependency_order` finds the bug.** The domino test suite would
  then depend on a research model that changes often, and the sync brings unrelated model changes
  (PRF, `KX_noprfmackey`, the games H2–H7) into this story. The test would also not name the rule.
- **Acceptance needs `Init` to close with 0 admits.** That is proof strength, not the name bug.

## 6. Acceptance criteria

- [x] All tests of §4 green, the whole test suite green, `cargo clippy` clean.
- [ ] Complexity: `collect_locals`, `record_local` and `build_proc` stay within budget
      (`crap_scope` on `src/writers/easycrypt/package.rs`).
- [ ] The owner's check, by hand (about 1 hour of machine time, not in CI):
      `domino easycrypt export --project ec4whs/4WHS --theorem Full4WHS --out <scratch>`, then
      `domino easycrypt prove --theorem Full4WHS --out <scratch> --jobs 12` with `--gamehop 11`,
      `--gamehop 13` and `--game H7`, one after the other. Pass: each job gets past
      `require Comp_H7` and proves its oracles. The jobs report their admits. Admits do not fail
      this story.

## 7. Follow-up (not in this story)

- `example-projects/4WHS` is older than `ec4whs/4WHS` (`MAC`, `ReductionMac`, `PRF`,
  `KX_noprfkey`, `ProtNoKeyOnlyKid`, the games H2–H7, `invariant-H1_1-H2_0.smt2`, and
  `KX_noprfmackey` and `invariant-H0-H1_0.smt2` are missing). A sync is a separate task.
