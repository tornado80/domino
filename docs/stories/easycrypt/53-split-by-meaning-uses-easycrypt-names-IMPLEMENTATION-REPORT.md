# Story 53 — Implementation report: splitting a leaf by meaning uses the names EasyCrypt knows

## What changed

- **One rule for the op name** (`writers/easycrypt/invariant.rs`). The new
  `pub(crate) fn relation_op_name(raw)` returns `Domino_<mangle_smt_def_name(raw)>`.
  `OpRegistry::define` calls it. It is the only `format!("Domino_{}", …)` in `src/`.
- **`unfold_ops`** (`easycrypt/tactics/mod.rs`). The list of ops that `rewrite /… in hpre` unfolds
  is now built by `fn unfold_ops(relations)`, which names each relation with `relation_op_name`.
  Before, it used the raw SMT name (`Domino_relation-a-b`), and EasyCrypt refused the sentence.
- **`goals::as_forall`** keeps every binder. The `kind != "type"` filter is removed, because
  EasyCrypt writes a value binder (`GTty`) with the kind `"type"`. The doc comment says why no
  binder is skipped.
- **Memory binders.** The JSON name of a memory binder already has its `&`
  (`{"name":"&m",…,"kind":"mem"}`, see `testdata/easycrypt/story25/…after_inline.json`). So no
  change is necessary. A test keeps this fact.
- **Fixed on sight:** ten clippy warnings with `--features cvc5-lib` (deprecated
  `TempDir::into_path`, replaced by `TempDir::keep` in `debug/driver.rs` and
  `debug/lockstep_run.rs`).

## Rejected shapes

- **Make `mangle_smt_def_name` `pub(crate)` and format the prefix in the tactics module.**
  Rejected: then two places write `Domino_`, and the acceptance grep finds two rules.
- The rejected alternatives of the story (read the names from the goal, copy the rule, filter only
  `mem`/`modty`) stay rejected.

## Tests

- Baseline: `cargo test --workspace` had 4 failures in `easycrypt::session::tests`. They pass
  alone. They time shell fakes against wall-clock limits and fail when the machine is loaded.
  They are not related to this story.
- New tests:
  - `tactics::tests::unfold_ops_use_the_writers_op_names`: `relation-a-b` and `state=` give
    `Domino_relation_a_b` and `Domino_state_eq`.
  - `goals::tests::a_value_binder_is_kept_and_the_driver_can_introduce_it`: a binder written as
    `"kind":"type"` gives `["ctr"]` and `move => ctr.`.
  - `goals::tests::a_memory_binder_keeps_its_ampersand`: `&m` gives `["&m"]`.
- After: `cargo test --workspace` 625 passed, 0 failed, 5 ignored. `cargo test --workspace
  --features cvc5-lib` 722 passed, 1 failed (`an_interrupt_never_answered_is_unresponsive_after_six_signals`,
  the same load-sensitive kind; it passes alone). `cargo clippy --workspace --all-targets`, with
  and without `cvc5-lib`: no warnings.

## Runs on `example-projects/4WHS` (theorem Full4WHS)

The user asked not to run the slow equivalences to the end. Thus:

- **H0 ~ H1_0:** before and after, 0 admits, and the proof files are the same.
- **H1_1 ~ H2_0:** before and after (third run, idle machine), 0 admits. See "Open items" for
  the two earlier runs after.
- **H2_1 ~ H3_0, H4 ~ H5, H5 ~ H6_0:** stopped after about 30 minutes. In that part of the
  transcripts, the refused sentences were:

  | Equivalence    | `rewrite … in hpre` refused, before → after | `move =>` refused, before → after |
  |----------------|---------------------------------------------|-----------------------------------|
  | H2_1 ~ H3_0    | 1 → 0                                       | 8 → 0                             |
  | H4 ~ H5        | 0 → 0                                       | 0 → 0                             |
  | H5 ~ H6_0      | 2 → 0                                       | 3 → 0                             |

  The admit counts after this story (before: 24 / 19 / 33) are not measured.

## Open items

- Admit counts of H2_1 ~ H3_0, H4 ~ H5, H5 ~ H6_0 after this story: not measured (runs too long).
  H3_1 ~ H4 was not run.
- **H1_1 ~ H2_0 after:** the first run stopped with "EasyCrypt answered `auto => /#.` with
  something that is not `domino-json/1`: EOF while parsing a string at line 1 column 65536". The
  answer was to an interrupted quick close (`Send2 N3`). The cut at exactly 64 KiB shows that the
  interrupt hit EasyCrypt while it wrote a large answer, after the first buffer flush. This is a
  race in the EasyCrypt fork, not in the changed code. The second run, with `cargo test` running
  in parallel, closed with 4 admits ("reason: interrupted", after a swallowed interrupt). This
  equivalence sends no `move =>` and no `rewrite … in hpre`, so this story cannot change it.
  The third run, on an idle machine, closed every goal with 0 admits.
- The session tests that time shell fakes fail under load (see "Tests"). They need wider limits
  or a fake that does not depend on wall-clock time.
