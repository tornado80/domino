# Story 64 — Implementation report: the leaf procedure

Rust only. The translation does not change.

## What changed

- **`driver.rs`, `leaf_of`.** The three leaf fallbacks are gone. A leaf now does:
  1. `decide_exit_path` (role *exit path*): while a program still has an `if` (side 1 first),
     `rcondt{i} ^if; 1: by auto.` or `rcondf{i} ^if; 1: by auto.`, the predicted decision
     first (`exit_decisions`). The deciding stops at the first `if` that neither decision
     takes. The loop is bounded by the number of top-level `if`s in the goal.
  2. `reduce_leaf` (role *reduce*): `auto => &1 &2 hpre.`, then the premise unfold. If `auto`
     fails or leaves a program goal, the leaf is admitted whole (`equal-output+invariant`). If
     `auto` closes the goal, the leaf is done.
  3. `open_part` (role *split*): `move => <names> /=.`, `move => hpreN /=.` (and the premise
     unfold), `rewrite /<op> /=.` for `inv` and the operators of `invariant_ops`, else
     `do split.`. Each goal of a `do split` that gives more than one goal is a bullet and is
     opened again in the same part. A goal that nothing opens goes to the part fallbacks
     (`atom`, unchanged; story 65 replaces it).
  4. The leaf budget starts after step 2, as before.
- **Prediction** (`exit_decisions`): the router's tail `if (ec_result = None)` gets `rcondt`
  first when that side's terminal is an abort. Every other `if` (a done-flag guard, a
  call-result guard, anything else, or no pair known) gets `rcondf` first. The done-flag guard
  is not recognised by name: its prediction is the same as the default.
- **Parts.** No binary `split.`, so no position rule: `Part::EqualOutput` is no longer given to
  a conjunct. It stays as a variant because the whole-leaf §3.6 check reads it. A part gets a
  claim only from an operator that the loop unfolded (`ambient_step` + `part_of_op`); §3.6 for
  that claim admits the part before the `rewrite` is sent. A part with no claim is `Whole`.
- **`Step`**: `Atom` is gone; `Split` now means "`do split`, else the goal is a part".
- **`Role::LeafFallback(n)`** is replaced by `Role::ExitPath` (slug `exit-path`, no `n`). The
  time-by-role row "leaf fallback" is now "exit path" (same position).
- `goals::as_conjunction` is now read only by tests (`#[cfg(test)]`).

### Rejected shape

A second leaf path behind a flag (old fallbacks first, then the new procedure). The story
removes the fallbacks. The `do split` and the per-step sentences are separate methods
(`split_part`, `open_step`) so `open_part` stays small.

## Tests

New, with a scripted fake EasyCrypt (`run_leaf` in `tactics/tests.rs`, which also answers
`undo k.` by going back to the state of answer `k`):

- `the_exit_decision_that_domino_predicts_comes_first` (pure).
- `the_exit_path_tries_the_predicted_decision_first_then_the_other_one`.
- `an_if_that_no_decision_takes_stops_the_exit_path_and_a_program_after_auto_is_a_whole_admit`.
- `the_leaf_is_opened_until_only_parts_are_left_and_no_split_is_sent`: `forall`, `=>`, a
  claim operator, `do split` into three goals, three parts that nothing opens; the admits have
  claim `invariant/StateRelation_r` and the relation's verdict; no `split.` and no leaf fallback.
- `a_claim_that_fails_in_domino_is_admitted_at_once_and_a_part_without_a_claim_is_the_leafs`.

Changed: `each_record_says_why_the_driver_sent_its_sentence` (story 56), and the role tests in
`transcript.rs`, `session.rs` and `time_by_role.rs`.

Runs: `cargo test --lib` 685 passed, 5 ignored; `cargo clippy --workspace --all-targets` clean,
`cargo build --release --workspace` OK.

## Not done

- `--features cvc5-lib` does not build here (no `cmake` for `cvc5-sys`), so the live tests
  were not compiled or run.
- The measurements for H2_1 ~ H3_0, H4 ~ H5 and H6_1_1 ~ H7_0 (admits, whole-leaf admits, wall
  time, time by role, before and after) were not taken: the owner asked for no EasyCrypt proof
  runs in this session. The "before" numbers are in the story (2026-10-08).
- Risks not checked on Full4WHS: `1: by auto.` may not close some exit-path side goals that
  `auto => /#` closed (then the `if` goes into the formula through `auto`'s wp); `do split` may
  unfold an operator that is not in `invariant_ops`, and such a part has no claim.
- The CRAP gate was not measured (`sdlc` is not available here). The new functions are small
  (`open_part` has the highest CC of them, about 8).
