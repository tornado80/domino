# Story 112: implementation report. A sampling into a name that holds a value goes through a temporary

A writer story on branch `amir/easycrypt-export`. Commits: `7a52247a` (the implementation, the
fixture, the tests and the docs), `80a89e19` (the review fix), and this report.

## Result

Some sampling targets already hold a value: an oracle argument, a state field, or a local that an
earlier statement of the oracle writes (on any branch). A sampling into one of them is now exported
through a temporary:

```
ec_s1 <$ dbits_n;
key <- ec_s1;
```

Every other sampling is still `x <$ d;`. This is the form that closed N51 of hop 11 `Send2` by hand
on 2026-10-30. The prover is unchanged. Story 104's `sampled_var_in_pre` check stays as a safety
net.

## What was built

- **`SampleTemps::written`** (`package.rs`). This is a private `HashSet<String>` of the names the
  translated statements have written, as `OracleNaming::target` spells them. `record_write` adds a
  name for every write that goes through `translate_pattern`: an assignment, each name of a tuple
  pattern, and the `ec_r<N>` binding of an invoke. A sampling adds its target too. A write inside a
  `then` branch counts after the `if`. No caller reads or sets the set.
- **`translate_sample`** is the sampling arm, moved out of `translate_stmt`. A table entry, and a
  target for which `holds_a_value` is true, go through `declare_sample_temp` and get a copy.
  `holds_a_value` is true for `OracleArg` and `State`, and for a local that is in the set. The doc
  comment says why: `#pre` can hold a fact about the old value, and sampling straight into the
  target would make the `seq` post false. `translate_stmt` is now simpler than before.
- **Fixture `testdata/easycrypt/story112`.** It has the oracles `St` (a state field), `Assigned`
  (a local assigned and then sampled), `Branch` (a local written in a `then` branch, then sampled
  after the `if`), `Fresh` (a local sampled with no earlier write), and `WritesW` / `SamplesW` (the
  same local, written in one oracle and sampled in another).
- **Docs.** `docs/easycrypt-export.md` gets a paragraph after the oracle-body semantics, with the
  table-entry form next to the new form. In `docs/proving-algorithm.md`, the `seq-post` rows of
  §9.1 and §9.2 and the "defensive" paragraph say that the export now prevents this case, and that
  story 104's check stays for other shapes.

## §3.4: does one listing `SampleTemps` span several frames?

**Yes.** `Lowerer` (`lower.rs:623`) holds one `SampleTemps` for the whole listing. It is created
at `lower.rs:236`, and `Lowerer::translate_stmt` passes it for every frame. **The frames still do
not mix.** The set is keyed by the name that `resolve_name` returns, and in the listing that name
comes from `LocalNames::resolve`. `LocalNames::resolve` keeps one `taken` set for the whole listing
and renames a later frame's clashing local to `<base>_<frame id>`. So a local name belongs to
exactly one frame. A state field's qualified name is shared by the frames, but a state field always
takes the temporary and never reads the set. An inlined callee's argument keeps its `OracleArg`
kind, so it takes the temporary, as it does in the module. The listing also never translates a
statement twice: `lower_if` and `lower_block` walk the branches, and `translate_stmt` sees only
leaf statements. So no name enters the set early. No per-frame key was needed. The `SampleTemps`
doc comment records this reasoning.

## Tests

All runs were filtered and memory-capped (`systemd-run --user --scope -p MemoryMax=6G`, with a
timeout and `--test-threads=1`). Live EasyCrypt tests ran with
`DOMINO_EASYCRYPT=$HOME/.opam/easycrypt/bin/easycrypt`.

| Run | Result |
|---|---|
| `writers::easycrypt::package` (4 new tests; `the_body_still_writes_to_the_argument` now expects `key <- ec_s1;`) | 28 passed. The new tests were red before the change. |
| `writers::easycrypt::lower` (2 new listing tests: story96 `Init`, inline and package shape; story112 `Assigned`/`Branch`/`Fresh`/`SamplesW`) | 21 passed |
| `writers::easycrypt::game`, `writers::easycrypt::typesfile` | 10 and 14 passed |
| `writers::easycrypt::export -- --skip 4whs` (live; includes `story96_full_tree_compiles_in_dependency_order`, the new `story112_full_tree_compiles_in_dependency_order`, kem-dem and the other story fixtures) | 26 passed |
| `cargo clippy --workspace --all-targets` | clean |

**Not run (owner's rule: no export of big projects):**

- §4, the 4WHS regression test. I checked it by inspection instead. I scanned every `<-$` in
  `example-projects/4WHS/packages`: there are 20. None samples into a state field or an argument,
  and none samples into a local that an earlier statement of the same oracle writes. No sampling
  sits in a `for` loop. So no sampling there gets a temporary, and the output should be unchanged.
  The check: export 4WHS before and after the change and run `diff`.
- §5, "the export of `ec4whs/4WHS` (`Full4WHS`) is byte-identical". Deferred, as above.
- The proof runs of story 111 §7, with this story's admit criteria from §5. They are deferred to the
  session that runs them now that both stories are committed. The `domino-ec` binary must be
  rebuilt from this branch and installed first, the way earlier runs did it:
  `source ~/.cache/domino/cvc5-lib-env.sh && cargo build -p domino --release --features cvc5-lib`,
  then copy `target/release/domino` to `~/.cargo/bin/domino-ec` (keep the old binary as a backup).

## Complexity

`.sdlc-workspace/crap-coverage.sh writers::easycrypt::package writers::easycrypt::lower` ingested
coverage. `sdlc crap gate . --since-ref $(git merge-base main HEAD) --threshold 15` failed with
`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`, the sandbox issue that story 111
also met. Cyclomatic complexity by inspection:

| Function | CC |
|---|---|
| `translate_sample` | 4 |
| `holds_a_value` | 2 |
| `record_write` | 1 |
| `translate_pattern` | 3 (unchanged) |
| `translate_stmt` | lower than before (the sampling arm left) |

All of these are well under 15, and the new tests cover them.

## Review

Two sub-agents reviewed the diff: one on standards, one on spec.

- **Fixed:** the write was recorded in two places, and the name `written_name` hid that it records
  something. Now one function, `record_write`, records every write, and `holds_a_value` resolves
  the name itself. I also added a listing test for locals, because the reviewer asked whether the
  listing might translate a statement twice. It does not.
- **Checked, not a problem:**
  - Loops: `easycryptify` rejects every surviving `for`, so `translate_stmt` has it as
    `unreachable!`. The doc comment now says this.
  - The order of the key and the temporary in the table arm: `translate_e` never allocates an
    `ec_s`, and the order of the emitted statements is unchanged.
  - The empty `ssp.toml`: the story96 fixture has one too.
- **Left:**
  - Small duplication between the test assertions.
  - The `String` key of the set. It is correct by the `LocalNames` invariant, and the comment
    states that invariant.

## Open

- The 4WHS and Full4WHS byte-identity checks, and the proof runs (story 111 §7). This story's
  criteria for them: no `seq-post` admit with a claim `sampling: key{…} in #pre` or `key0{…}`, and
  no `program-mismatch` at the `MAC.Init` sampling in hop 11 `Send3` and in `SideInv_H7` `Send2`.
- The `SideInv_H7` admits are attributed to this cause only by inference (story §1). The proof run
  will confirm or refute that.
