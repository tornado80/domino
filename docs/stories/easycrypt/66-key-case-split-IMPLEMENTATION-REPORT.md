# Story 66 — Implementation report: a case split on updated keys

Rust only. The translation does not change.

## What changed

- **`json.rs`, `Form`**: new optional fields `name`, `scope`, `path`, `mem` (the `local` and
  `pvar` nodes of `json-output.md`).
- **`goals.rs`, `key_pairs`** (§3.1): walks the conclusion (head, args, body, pre, post) in
  order. A read `Top.FMap._.[_]` or a membership test `Top.FMap.dom` (what `\in` expands to)
  whose index is a `local` in the introduced binders, on a map that is a chain of
  `Top.FMap._.[_<-_]`, gives a `KeyPair { binder, key }` for each atom key of the chain. An atom
  is a `local` (its name) or a `pvar` at a memory: `Comp_H3.Pkg_Inst_KX.ctr{2}` (global: the
  path without `Top.`, `./` as `.`) or `x{1}` (local). Other keys are skipped. No duplicates.
  `MAX_KEY_PAIRS = 6`. The operator is matched by the path suffix (`op_ends`), because the
  FMap operator names have dots.
- **`driver.rs`**:
  - `Prover::binders` (new): the binders that the opening loop introduced (`Step::Intro`),
    cleared at each leaf and truncated after each bullet of `split_part`, as `premises`.
  - `PART_FALLBACKS = 4`. `atom` runs `key_case_split` after fallback 3.
  - `key_case_split` (fallback 4, role `part-fallback` n=4, live `fallback 4/4`): with 1 to 6
    pairs, `split_cases` sends `case (b = k) => [->|?].`, then each case is a bullet; in the
    `->` case the pairs of `b` are dropped; at the end of each case `smt(<hints>).` must close
    the goal. It stops at the first failure, and everything is undone to the state before the
    first `case`.
  - Admit comment (§3.3): `smt:` is the outcome of fallback 4's last `smt` when it ran; else
    (no pair, more than 6, or the first `case` refused) the outcome of fallback 3 (or of the
    last fallback that ran).

### Rejected shape

The split as a list of sentences for `attempt`: the bullets and the "stop at the first case
that fails" need the recursion, so `split_cases` is a recursive method, and `key_case_split`
does the snapshot and the rollback around it. The alternatives of §3.4 were not implemented.

## Tests

- `goals.rs`: `a_read_of_an_updated_map_at_a_binder_gives_one_pair` (one pair `(c,
  Comp_H3.Pkg_Inst_KX.k{2})`; the same read plus `dom` gives it once),
  `a_key_that_is_not_an_atom_and_a_binder_outside_an_updated_map_give_no_pair` (`k{2} + 1`, a
  read of a plain map, an index that was not introduced),
  `a_chain_of_updates_gives_a_pair_for_each_key_in_order`.
- `tests.rs` (scripted fake EasyCrypt, `run_leaf`, which now also returns the script):
  `two_key_pairs_split_into_four_cases_each_a_bullet` (the 7 sentences of §3.2 in order, and
  the bullets in the script), `one_failing_case_undoes_the_whole_split` (an `undo`, then an
  admit with `smt: error`, no `case` in the script), `seven_key_pairs_give_no_split`.
- The story-64/65 test `the_leaf_is_opened_until_only_parts_are_left_and_no_split_is_sent` is
  unchanged and passes (its parts have no pair, so fallback 4 does not run).

Runs: `cargo test --lib` 693 passed, 5 ignored; `cargo clippy --workspace --all-targets`
clean; `cargo build --release --workspace` OK.

## Not done

- `--features cvc5-lib` does not build here (no `cmake` for `cvc5-sys`).
- The table for H2_1 ~ H3_0 and H6_1_1 ~ H7_0 (how often fallback 4 ran and closed, admits
  before and after) was not measured: the owner asked for no EasyCrypt proof runs in this
  session.
- Risk not checked on Full4WHS: the walk does not go into `if`, `let`, `tuple` or `proj` nodes
  (the `Form` struct does not read them), so a read under such a node gives no pair. `/=`
  removes most `let`s and projections first.
- The CRAP gate was not measured (`sdlc` is not available here). The new functions are small
  (the highest CC is about 5, `collect_key_pairs` and `split_cases`).
