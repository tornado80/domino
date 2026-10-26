# Story 95 — Implementation report: one CLI vocabulary

Rust, the text that `src` prints, the tests and the docs. No ADR. A hard break: no aliases.

## What changed

### The CLI (`crates/domino/src/cli.rs`)

- `Commands::Proofsteps` is now `Commands::Gamehops` (subcommand `gamehops`), with a doc comment.
- `Prove`, `Debug`, `Inline`, `Html`, `Latex`, `Gamehops`: the fields `path`, `proof` and
  `proofstep` are now `project`, `theorem` and `gamehop`. The `conflicts_with_all` strings changed
  with them. `Prove::gamehop` and `Prove::theorem` have a help text now.
- `EcProve`, `EcCheckAlignment`, `EcDebug`: `proofstep`, `side_inv`, `pkg_inv` and `debug_timeout`
  are now `gamehop`, `game`, `package` and `timeout`. The help text of `EcProve::game` is the text
  of §2.1.
- Each doc comment says "game hop" and "theorem" and refers to `domino gamehops`.

### `crates/domino/src/main.rs`

- The callers use the new field names. `fn proofsteps` is now `fn gamehops`.
- The error messages say `--theorem` and `--gamehop`, and "game hop".
- `easycrypt_prove` was at cyclomatic complexity 15 (the budget limit). The construction of
  `TacticsOptions` moved to the new function `tactics_options`. The behaviour does not change.

### The text that `src` prints

- Each printed flag name in `src/debug/*`, `src/easycrypt/*`, `src/game_invariant/*`,
  `src/package_invariant/context.rs` is the new name: hints of the debug index, the warnings of
  `easycrypt prove`, the comment line of the base frame (`domino easycrypt debug --game`).
- "proofstep" in printed text is now "game hop": the stdout reports, `summary.txt`, the titles of
  the viewers (`lockstep_viewer.html`, `report.rs`), the debug index (row text and the column
  header), the live page and the oracle page of a tactics run, the `.smt2` comment headers, the
  `check-alignment` report, the `inline` header and the errors of `domino debug` and `inline`.
- Not changed (§3): the JSON field `proofstep` (the pages read `T.proofstep`), the result record,
  the Rust names (`proofstep_dir`, `debug_proofsteps`, `Project::proofsteps`, `num_proofsteps`,
  `TacticsOptions::proofstep`, `side_inv`, `pkg_inv`) and the CSS custom property `--proof` in
  `src/writers/html.rs`.

### The callers

- `crates/domino/tests/*.rs`: all old flags.
- `scripts/test-known-examples.sh`: `$DOMINO gamehops`.
- `Readme.md`, `docs/symbolic-execution-plan.md`, ADR 0014, 0016 and 0021: the command lines.
  ADR 0021 kept its consequence about the EasyCrypt flag names, with a note "Amended by story
  EC 95".
- The goldens that hold the printed text: `testdata/story03/inline-hello-world.txt`,
  `testdata/easycrypt/story08/*.txt`, `testdata/easycrypt/story27/*_tactics_report.txt`,
  `testdata/debug/se25*/side_inputs.golden`.

## Tests

`cargo test --workspace --features cvc5-lib`: 1103 passed, 0 failed, 7 ignored.
`cargo clippy --workspace --all-targets --features cvc5-lib`: no warnings. New or changed tests:

- `cli::tests::every_command_takes_the_one_vocabulary`: each command line of §6 parses.
- `cli::tests::the_old_names_are_refused`: each old flag on each command, and the subcommand
  `proofsteps`, gives a clap error.
- `cli::tests::the_easycrypt_targets_still_conflict`: `--gamehop` with `--game` or `--package`,
  and `--game` with `--package`, give `ArgumentConflict` on `easycrypt prove` and `easycrypt debug`.
- `cli::tests::no_help_page_names_an_old_flag`: the long help of each command and subcommand
  (more than 10 pages) has no old flag and no "proofstep" or "proof step".
- `prove_game::clap_refuses_game_with_the_other_targets`: the error of `main.rs` says
  `--game cannot be used with --theorem or --gamehop`.
- `prove_game::gamehops_lists_the_game_hops_of_each_theorem`: `domino gamehops` prints the table.

Deviation from test-first: the renames in `cli.rs` came before the clap tests, because `main.rs`
does not compile with the old field names. The tests did not go red first.

The acceptance grep finds only the Rust names of §3, the CSS property `--proof` of
`src/writers/html.rs`, and the old names in the test `the_old_names_are_refused`.

## Complexity (cyclomatic, `crap_scope`)

`crates/domino/src/main.rs`: the highest values are `debug_proofsteps` 12, `check_prove_args` 11,
`easycrypt_debug` 11. `easycrypt_prove` was 15; `tactics_options` took the 7 match arms out of it.
New test helpers in `cli.rs`: `old_name` 5, `help_pages` 3.

## A problem outside the story

`scripts/test-known-examples.sh` fails on `test-projects/test-oracle-rename`: `domino prove`
gives `sat` for the claims `invariant` and `same-output` of the oracle `ChangeNameUsefulOracle`.
The binary of commit a3dbb3c1 (before this story) gives the same failure, so this story did not
cause it. It is not fixed here. All other projects of the script pass.

## Not done

- The owner's check: a lockstep page title, a stdout report and an error message.
- `scripts/test-known-examples.sh` does not pass (see above).
