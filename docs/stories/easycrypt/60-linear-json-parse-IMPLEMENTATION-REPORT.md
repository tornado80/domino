# Story 60 — Implementation report: Domino parses an answer in linear time

Domino only. The sentences, the protocol and the proof files do not change.

## What changed

- **`json.rs`.** `one_or_many` is a hand-written `Visitor`: `visit_seq` reads a list of
  `Form`s, `visit_map` reads one `Form` (through `MapAccessDeserializer`) into a list of one.
  There is no `#[serde(untagged)]`, so nothing is buffered into serde's `Content`. The
  signature and `Form` do not change.
- **`session.rs`.** The reader thread measures `parse_response` for each line (`Line::parse_ms`).
  The value goes into the transcript record and into the oracle's time by role.
- **`transcript.rs`.** A sentence record has `"parse_ms"` after `"ms"`. `ms` stays the full round
  trip, so the time-by-role rows still sum to the oracle's EasyCrypt time.
- **`time_by_role.rs`.** `Sentence::parse_ms`; `EcSums` sums it. The `EasyCrypt:` line ends with
  `serialize …, Domino parse …`. Like the other sums, it is counted only for answers with
  `timing`.

## Tests

- `args_parse_as_a_list_and_as_a_single_formula`: list, single object (`pr`), absent.
- `a_formula_nested_two_thousand_deep_parses_fast`: a chain of 2,000 `/\`, bound 500 ms. The
  new parser takes a few ms in a debug build. With the old untagged enum put back, the test
  fails (2.3 s in a debug build).
- The record and `EasyCrypt:` line tests now check `parse_ms` and `Domino parse`.

## Not done

- The wall time and "rest of round trip" after the change for H2_1 ~ H3_0 and H6_1_1 ~ H7_0
  are not measured: the hops were not run (the owner asked for no EasyCrypt proof runs in this
  session). The before numbers are in `Proof_Statistics.md` (2026-10-08). Run story 60 §5 to
  get the after numbers.
