# cvc5 unsat diagnostics and proof translation into EasyCrypt

Status: research note. Date: 2026-10-23.
Language: ASD-STE100 Simplified Technical English (best effort).

## How to read this note

- Each fact has a source tag such as [S3]. The source list is at the end.
- "Source code" facts come from the cvc5 tag `cvc5-1.4.0`
  (commit `b432cd77ebeb41091de42637ca8523f8437a1db1`). We read a local
  clone of this tag that the `cvc5-sys` 0.6.1 build script made.
- "Test" facts come from small runs of the local binary
  `cvc5 1.4.2 [git 282d5e0]`. The test files are less than 25 lines each.
- EasyCrypt facts come from upstream `EasyCrypt/easycrypt` main at commit
  `d1e7c102e9942649cba2499cb5c34a46951ba993` (2026-10-23). The local fork in
  `easycrypt/` has the same code for the parts that we cite.
- Text in a box that starts with **Opinion** is our opinion. All other text
  states facts from the sources.

## Summary of findings

1. cvc5 1.4.x gives unsat cores, unsat assumptions, unsat core lemmas,
   difficulty, timeout cores, learned literals, quantifier instantiations
   and full proofs. The Rust crate `cvc5` 0.6.1 exposes all of them [S1][S20].
2. The option name is `print-cores-full`. The name `print-unsat-cores-full`
   does not exist in cvc5 1.4.0 [S2].
3. There is no SMT-LIB command `get-instantiations`. You get instantiations
   from the option `dump-instantiations` or from the API function
   `Solver::getInstantiations()` (crate: `get_instantiations()`), which
   returns a string, not terms [S3][S5].
4. cvc5 prints only the instantiations that the refutation uses **only** when
   full proofs are on (`produce-proofs`) and the result is `unsat`. With
   unsat cores only, cvc5 prints all instantiations [S6].
5. Instantiation terms can be internal Skolem constants
   (`@quantifiers_skolemize_2`) and terms after rewriting (`(+ 1 k)`, not
   `(+ k 1)`) (Test T3, T5).
6. cvc5 Alethe output failed on our small test with a `Maybe` datatype
   ("Proof unsupported by Alethe: contains operator DUMMY_SKOLEM" and
   "... APPLY_CONSTRUCTOR"). Without datatypes it gave a proof with a
   `hole` step (Test T4). The cvc5 documentation lists Alethe support only
   for EUF, linear arithmetic, bit-vectors and parts of strings [S8].
7. EasyCrypt `smt(l1 l2)` sends only the named lemmas plus **all** local
   hypotheses. It adds no lemmas from the relevance filter. Plain `smt`
   adds up to 50 lemmas from a MePo-like filter [S12][S13][S14].
8. EasyCrypt does not select local hypotheses. The source has the comment
   `FIXME: Selection of hypothesis` [S13]. EasyCrypt simplifies the goal,
   but not the hypotheses, before it calls the provers [S12][S16].
9. CVC5 is not in the EasyCrypt default prover list
   (`["Z3"; "CVC4"; "Alt-Ergo"; "Eprover"; "Yices"]`) [S14].
10. We found no prior work that translates SMT proofs, unsat cores or
    instantiations into EasyCrypt tactics. The nearest work is
    QuerySMT (Lean, 2026), which turns cvc5 proof facts into `have` steps
    plus a final automatic tactic [S25].

## A. cvc5 unsat diagnostics (version 1.4.x)

### A.1 Unsat cores

#### A.1.1 Options and commands

| Item | Kind | Default | What it does | Since | Source |
|---|---|---|---|---|---|
| `produce-unsat-cores` | option (common) | false | Turns on unsat cores. Without other settings, cvc5 uses SAT solving under assumptions plus preprocessing proofs. | 1.0 | [S2] |
| `unsat-cores-mode` | option (expert) | `off` | Values: `off`, `sat-proof`, `assumptions`. See A.1.2. | 1.0 | [S2][S7] |
| `minimal-unsat-cores` | option (expert) | false | Reduces the core to a minimal core. See A.1.3. | 1.0 | [S2][S7] |
| `print-cores-full` | option (regular) | false | Prints all formulas in a core, also unnamed ones. | — | [S2] |
| `check-unsat-cores` | option (common) | false | Makes and checks a core after `unsat`. The help text says "expensive". | — | [S2] |
| `produce-unsat-assumptions` | option (common) | false | Turns on `get-unsat-assumptions`. | — | [S2] |
| `dump-unsat-cores` | option (regular) | false | Prints the core after each `unsat`. | — | [S3] |
| `(get-unsat-core)` | command | — | Returns the core. | — | [S4] |
| `(get-unsat-assumptions)` | command | — | Returns the failed assumptions of the last `check-sat-assuming`. | — | [S4] |
| `-o unsat-core-benchmark` | output tag | — | Prints the core as an SMT-LIB benchmark. | — | [S3b] |

Facts about the options:

- If you set `minimal-unsat-cores`, `produce-unsat-assumptions`,
  `check-unsat-cores`, `dump-unsat-cores` or a non-`off`
  `unsat-cores-mode`, cvc5 sets `produce-unsat-cores` to true [S7].
- If `produce-unsat-cores` is true and the mode is `off`, cvc5 sets the
  mode to `assumptions` [S7].
- If you turn on `produce-proofs`, cvc5 also turns on unsat cores and sets
  the mode to `sat-proof` (unless the proof mode is `pp-only`) [S7].
- Unsat cores disable some preprocessing: deep restarts, learned rewrites,
  pseudo-boolean rewrites and `global-negate`. If you set one of these
  yourself, cvc5 stops with an error. ITE simplification always gives an
  error with unsat cores [S7].
- The source code calls `assumptions` mode the "safe" mode. It says that
  the other modes are experimental [S7].

#### A.1.2 Values of `unsat-cores-mode`

| Value | Help text in source | What it means |
|---|---|---|
| `off` | "Do not produce unsat cores." | No cores. |
| `assumptions` | "Produce unsat cores using solving under assumptions and preprocessing proofs." | Default when cores are on. cvc5 sets the proof mode to `pp-only` (preprocessing proofs only) [S7]. |
| `sat-proof` | "Produce unsat cores from the SAT proof and prepocessing proofs." | cvc5 sets the proof mode to `sat-proof`. You need this mode for `get-unsat-core-lemmas` [S4][S7]. |

Source: [S2], `src/options/smt_options.toml`.

#### A.1.3 How `minimal-unsat-cores` minimizes

The function `UnsatCoreManager::reduceUnsatCore` does the work [S6]:

1. It takes the core that cvc5 found first.
2. For each formula in the core, in order, it removes the formula. Then it
   makes a new subsolver and asserts the rest of the core.
3. If the subsolver says `unsat`, the formula stays removed.
   If not, cvc5 puts the formula back.
4. If the subsolver says `unknown`, cvc5 also puts the formula back and
   prints the warning "could not reduce unsat core due to unknown result".

This is a "deletion-based" algorithm. Consequences:

- Cost: one extra `check-sat` for each formula in the first core. Each
  check runs in a fresh subsolver, without proofs [S6].
- The source does not give a time limit to these subsolvers
  (`initializeSubsolver(coreChecker, d_env)` without a timeout) [S6][S6b].
  The subsolver copies the options of the main solver, so it can get the
  `tlimit-per` value through the copy. We did not confirm this in a test.
- Guarantee: the result is minimal only with respect to the subsolver
  answers. If a subsolver says `unknown`, the result can contain a
  formula that is not necessary. This happened in our test T2: cvc5
  kept a definition after an `unknown` answer and printed the warning.
- The warning text goes to the normal output stream in our test, in the
  same line as the core. A parser of the output must allow for this
  (Test T2).

#### A.1.4 Names, `:named` and the API

- In SMT-LIB, `(get-unsat-core)` prints only the names of `:named`
  assertions. With `print-cores-full`, it prints all formulas
  (`GetUnsatCoreCommand::printResult`) [S9].
- The C++ API `Solver::getUnsatCore()` does not separate named and unnamed
  assertions. It returns terms. After `checkSatAssuming`, it can also
  contain some of the assumptions [S4].
- Definitions (`define-fun`) can be part of a full core. In our test,
  the full core contained `(= inv (lambda ...))` (Test T2). The source
  separates "definitions" from "assertions" when it prints a core
  benchmark (`partitionUnsatCore`) [S6].
- Crate warning: `SymbolManager::get_named_terms()` in crate 0.6.1 is
  `unsafe`. The crate documentation says that the names "are read from
  freed memory" because of a bug in the C function
  `cvc5_sm_get_named_terms` [S20]. A safe way to get names is to send
  the text `(get-unsat-core)` through the input parser and read the
  output string of `Command::invoke` [S20]. (Domino already uses the
  parser path.)

#### A.1.5 `check-sat-assuming` and `get-unsat-assumptions`

- Test T6: we asserted the invariant and two goal literals `g1`, `g2` as
  equations, then ran `(check-sat-assuming (g1 g2))`. cvc5 answered
  `unsat`, and `(get-unsat-assumptions)` gave `(g1)`. The core gave the
  named invariant only.
- This gives a cheap way to find which goal conjuncts are false. You do
  not need push/pop for each conjunct.

#### A.1.6 Push/pop, incremental mode and models

- Test T1: with `incremental` on, cores worked inside `push`/`pop`. The core
  contained assertions from the outer level (the invariant) and from
  the inner level (the goal).
- Test T6: `produce-models`, `produce-unsat-cores`,
  `produce-unsat-assumptions`, `produce-difficulty` and `incremental`
  worked together in one run.
- In cvc5 1.4.0, CaDiCaL is the default SAT solver, but "MiniSat is still
  selected by default in incremental mode" [S10].
- The API check for `getUnsatCore` requires the last result to be `unsat`
  ("cannot get unsat core unless in unsat mode") [S5].

#### A.1.7 Quantifiers and timeouts

- An unsat core is a subset of the input assertions. A quantified
  assertion is in the core if the proof uses it, for example through an
  instantiation (Test T1: `invariant_old` is in the core of `goal_b`).
- After a `tlimit-per` timeout, the result is `unknown`. `getUnsatCore`
  then fails, because it needs the `unsat` mode [S5]. Use a timeout core
  (A.3) for this case.
- F* documentation warns about the same effect with Z3: a core is
  unsatisfiable, but the solver may not prove it again, because
  quantifier heuristics can depend on facts that are outside the core [S27].

### A.2 Unsat core lemmas and learned literals

Both exist.

- `get-unsat-core-lemmas` (API `getUnsatCoreLemmas`): returns "the lemmas
  used to derive unsatisfiability". It needs
  `unsat-cores-mode=sat-proof`. It is marked experimental [S4][S5].
  Added in cvc5 1.1.0 [S10].
- There is no option `produce-unsat-core-lemmas`. The related options are
  `dump-unsat-cores-lemmas` and the output tag
  `-o unsat-core-lemmas-benchmark` [S3][S3b]. `dump-unsat-cores-lemmas`
  turns on full proofs [S7].
- `get-learned-literals` (API `getLearnedLiterals(LearnedLitType)`): needs
  `produce-learned-literals`. It works after `sat`, `unsat` or `unknown`.
  It returns literals "entailed by the current set of assertions" [S4][S5].
  Types: `PREPROCESS_SOLVED`, `PREPROCESS`, `INPUT`, `SOLVABLE`,
  `CONSTANT_PROP`, `INTERNAL` [S11]. Available since cvc5 1.0 [S10].
- Note: `learned-rewrite` (a different option) is not supported with
  proofs or unsat cores [S2].

### A.3 Difficulty and timeout cores

#### Difficulty

- Options: `produce-difficulty`, `difficulty-mode` (values `lemma-literal`,
  `lemma-literal-all` (default), `model-check`) [S2].
- `get-difficulty` returns a map from some input assertions to a value.
  Assertions that are not in the map have difficulty zero. It works after
  `sat`, `unsat` or `unknown`. It is experimental [S4][S5].
- In the default mode, the difficulty of an assertion is "how many lemmas
  use a literal that the assertion depends on to be satisfied" [S2].
- `produce-difficulty` turns on preprocessing proofs (`pp-only`) [S7].
- Test T6 output: `((g1 1) (invariant_old 1) (<definition of g1> 1))`.
- Since cvc5 1.0 [S10].

#### Timeout cores

- `get-timeout-core` and `get-timeout-core-assuming` exist. API:
  `getTimeoutCore()`, `getTimeoutCoreAssuming(assumptions)` [S4].
  The first came in cvc5 1.0.6, the second in 1.1.0 [S10].
- They need `produce-unsat-cores` [S5].
- Each internal check has the limit `timeout-core-timeout`
  (default 10000 ms) [S2].
- Result [S4]:
  - `unknown` with reason timeout: the set is a subset of the assertions
    that causes a timeout in that limit.
  - `unsat`: the set is an unsat core.
  - `sat`: the set is empty.
- `getTimeoutCoreAssuming` does not need an earlier `checkSat` [S4].
- Algorithm (header comment of `TimeoutCoreManager`) [S6c]: cvc5 keeps a
  set C and a set of models M. It adds one assertion that the current
  model makes false, and removes assertions that are not needed to block
  a model. In the worst case it makes N checks for N assertions. Only one
  of the checks is a timeout. The comment estimates about 25% of N checks
  on average.
- Test T6: after the `unsat` checks, `(get-timeout-core)` on the plain
  assertions answered `sat` (the plain assertions are satisfiable).

### A.4 Quantifier instantiations

#### Options

| Option | Default | What it does | Source |
|---|---|---|---|
| `dump-instantiations` | false | Prints instantiations after each `unsat`. | [S3] |
| `dump-instantiations-debug` | false | Same, with debug data (the source of each instance). | [S3] |
| `print-inst` | `list` | `list`: print the instances. `num`: print only the count per quantified formula. | [S2b] |
| `print-inst-full` | true | Also print instances of quantified formulas without a name. | [S2b] |
| `-o inst`, `-o trigger`, `-o inst-strategy` | — | Diagnostic output during solving. | [S3b] |

- You can name a quantified formula with the `:qid` attribute. When
  `print-inst-full` is false, cvc5 prints only named quantified formulas
  (`getNameForQuant(..., reqNames)`) [S6]. (The regression file name
  `qid-debug-inst.smt2` in [S3b] shows this use of `:qid`.)

#### API

- C++: `std::string Solver::getInstantiations() const`. It is experimental.
  It returns a string, not terms. It works after `unsat`, `sat` or
  `unknown` [S4][S5].
- There is no SMT-LIB command for it. The parser has no command
  `get-instantiations` (we listed all `get-*` commands in the parser
  source) [S9b].
- The crate has `Solver::get_instantiations(&self) -> Result<String>` [S20].

#### Relevant or all instances

`SolverEngine::printInstantiations` [S6]:

- If `produce-proofs` is on, the proof mode is `full` (or `full-strict`)
  and the last result is `unsat`, cvc5 walks the SAT proof. It collects
  only the `INSTANTIATE` and `SKOLEMIZE` steps of that proof. So it prints
  only the instances that the refutation uses.
- In all other cases (for example unsat cores in `assumptions` mode),
  cvc5 prints **all** instances that the quantifier module made.
- Source detail: the test for a negated `forall` in
  `getRelevantQuantTermVectors` is
  `q.getKind() == Kind::NOT && q.getKind() == Kind::FORALL`. This can never
  be true. So in proof mode, cvc5 does not print the Skolem list for a
  negated `forall` [S6]. Test T5 agrees: with proofs, cvc5 printed no
  `skolem` block; without proofs, it printed one.

#### Output format (tests T3, T5)

```
(instantiations (forall ((x Int)) (= (select T1 x) (select T2 x)))
  ( (+ 1 k) )
)
```

With `dump-instantiations-debug`:

```
(instantiations (forall ((x Int)) (= (select T1 x) (select T2 x)))
  (! ( @quantifiers_skolemize_2 ) :source QUANTIFIERS_INST_CBQI_CONFLICT)
)
```

Without proofs, cvc5 also prints the Skolem block:

```
(skolem (forall ((x Int)) (let ((_let_1 ((as Some (Maybe Int)) v))) ... (ite _let_2 _let_1 (select T1 x)) ...))
  ( @quantifiers_skolemize_2 )
)
```

Facts from these tests:

- The quantified formula is printed after `define-fun` expansion and
  rewriting. In T5, `store` became `ite`.
- Instance terms are rewritten (`(+ k 1)` became `(+ 1 k)`).
- An instance term can be an internal Skolem. In T5 the Skolem is the
  witness for the negated new-state invariant. The Skolem block tells which
  formula the Skolem comes from.

### A.5 Proofs

#### Options and API

| Item | Values / default | Source |
|---|---|---|
| `produce-proofs` | bool, false | [S2] |
| `proof-mode` (expert) | `off`, `pp-only`, `sat-proof`, `full-proof`, `full-proof-strict` | [S2] |
| `proof-format-mode` (expert) | `none`, `dot`, `lfsc`, `alethe`, `cpc` (default `cpc`) | [S2] |
| `proof-granularity` | `macro` (default), `rewrite`, `theory-rewrite`, `dsl-rewrite`, `dsl-rewrite-strict` | [S2] |
| `proof-check` | `eager`, `eager-simple`, `lazy`, `none` | [S2] |
| `check-proofs`, `check-proofs-complete`, `dump-proofs` | bool | [S2][S3] |
| `proof-prune-input` | prune unused input assumptions | [S2] |
| `proof-alethe-define-skolems`, `proof-alethe-res-pivots` | Alethe printing options | [S2] |
| `(get-proof)` / `Solver::getProof(ProofComponent c = FULL)` | needs `produce-proofs`, needs `unsat` | [S4][S5] |
| `Solver::proofToString(proof, format, assertionNames)` | prints one proof in a format | [S4] |

- When you set `produce-proofs`, cvc5 raises the granularity to
  `dsl-rewrite` (unless you set it), and for Alethe to at least
  `theory-rewrite` [S7].
- `ProofComponent` values [S11]: `RAW_PREPROCESS`, `PREPROCESS`, `SAT`,
  `THEORY_LEMMAS`, `FULL`. `FULL` is "a proof of false whose free
  assumptions are a subset of the input formulas". The other components
  are only valid immediately after `unsat`.
- The `Proof` API object gives `getRule()`, `getRewriteRule()`,
  `getResult()`, `getChildren()`, `getArguments()` (crate: `rule()`,
  `rewrite_rule()`, `result()`, `children()`, `arguments()`) [S20].
- The API for proof objects came in cvc5 1.1.0 [S10].

#### CPC, Eunoia, Ethos, Logos

- CPC (Cooperating Proof Calculus) is the default format since cvc5 1.2.0.
  It "was designed to faithfully represent cvc5's internal reasoning" [S8b][S10].
- The rules of CPC are written in the Eunoia language, in the file
  `proofs/eo/cpc/Cpc.eo` of the cvc5 repository [S8b].
- Ethos is the checker for CPC. It is written in C++. If a proof has a
  `trust` step, Ethos prints `incomplete`. Else it prints `correct` [S8b].
- cvc5 1.4.0 proofs are checkable by Ethos 0.2.4 [S10].
- cvc5 1.3.0 states: "we expect that CPC proofs are complete for *all*
  theories and features allowed in safe mode" [S10].
- cvc5 1.4.0 adds Logos, a CPC checker in Lean with a soundness proof.
  Logos does not yet support "parametric datatypes and `define-fun`" [S10].
  Domino uses a parametric `Maybe` and definitions, so Logos does not
  apply now.
- Test T3 (CPC, 1.4.2): the proof of our array/`Maybe` goal had an
  `instantiate` step with the argument `(@list (+ 1 k))`, and steps
  `arith_poly_norm`, `cong`, `eq_resolve`, `scope`, `chain_m_resolution`.
  Test T5: `skolemize`, `skolem_intro` and `instantiate` steps, with the
  Skolem written as `(@quantifiers_skolemize @t24 0)`.

#### Alethe

- The cvc5 documentation says: "Currently, the theories of equality with
  uninterpreted functions, linear arithmetic, bit-vectors and parts of the
  theory of strings (with or without quantifiers) are supported in cvc5's
  Alethe proofs" [S8].
- The Alethe specification itself says cvc5 "supports Alethe
  experimentally" [S21].
- The Alethe specification has quantifier rules `forall_inst`, `bind`,
  `sko_ex`, `sko_forall`, `qnt_cnf`, `onepoint`, `qnt_join`,
  `qnt_rm_unused`. It has no rules for arrays or datatypes. A `hole` step
  is a "placeholder for rules not defined here" [S21].
- cvc5 option `proof-alethe-testing` text: "do not support experimental
  features such as BV, Strings, Datatypes" [S2].
- Test T4 (1.4.2): with the `Maybe` datatype, Alethe output failed with
  "Proof unsupported by Alethe: contains operator DUMMY_SKOLEM". With
  `--proof-alethe-testing` it failed with "... APPLY_CONSTRUCTOR". Without
  the datatype (plain `Int` arrays), cvc5 printed an Alethe proof with a
  `forall_inst` step and one `hole` step with argument
  `"untranslated rewrite"` (for the arithmetic normalization).

### A.6 What the Rust crate `cvc5` 0.6.1 exposes

The crate is `cvc5` 0.6.1 (git `e9d50786`). It builds cvc5 1.4.0
(`[package.metadata.cvc5] version = "1.4.0"` in `cvc5-sys`) [S20].

| cvc5 C++ API | Crate 0.6.1 | Return type |
|---|---|---|
| `getUnsatCore` | `get_unsat_core(&self)` | `Result<Vec<Term>>` |
| `getUnsatCoreLemmas` | `get_unsat_core_lemmas(&self)` | `Result<Vec<Term>>` |
| `getUnsatAssumptions` | `get_unsat_assumptions(&self)` | `Result<Vec<Term>>` |
| `getProof` | `get_proof(&self, c: ProofComponent)` | `Result<Vec<Proof>>` |
| `proofToString` | `proof_to_string(&self, proof, format, assertions, names)` | `String` |
| `getLearnedLiterals` | `get_learned_literals(&self, LearnedLitType)` | `Result<Vec<Term>>` |
| `getDifficulty` | `get_difficulty(&self)` | `Result<(Vec<Term>, Vec<Term>)>` (inputs, values) |
| `getTimeoutCore` | `get_timeout_core(&mut self)` | `Result<(SmtResult, Vec<Term>)>` |
| `getTimeoutCoreAssuming` | `get_timeout_core_assuming(&mut self, &[Term])` | `Result<(SmtResult, Vec<Term>)>` |
| `getInstantiations` | `get_instantiations(&self)` | `Result<String>` |
| `checkSatAssuming` | `check_sat_assuming(&mut self, &[Term])` | `Result<SmtResult>` |
| `SymbolManager::getNamedTerms` | `unsafe fn get_named_terms(&self)` | `Vec<(Term, String)>` (names can dangle) |

Sources: crate source `src/solver.rs`, `src/proof.rs`, `src/parser.rs`, and
docs.rs [S20].

## B. Translating SMT proofs and diagnostics into interactive provers

### B.1 Isabelle Sledgehammer

- Sledgehammer sends the goal plus "a heuristic selection of facts" to
  ATPs and SMT solvers (CVC4, cvc5, veriT, Z3) [S22].
- The default relevance filter is MeSh, a mix of MePo (Meng–Paulson,
  symbol-based) and MaSh (machine learning) [S22].
- The result is "source text that typically reconstructs the proof
  within Isabelle", often with `metis` [S22].
- Minimization: "Sledgehammer includes a proof minimization tool that takes
  a set of facts returned by a prover and repeatedly calls a prover or
  proof method with subsets of those facts to find a minimal set" [S22].
- Preplay: Sledgehammer tries the one-line proof before it shows it
  (`preplay_timeout`, default 1 s) [S22].
- `instantiate` option: Metis "should try to infer variable
  instantiations before proof reconstruction, which results in
  instantiations of facts using `of`" (for example
  `map_prod_surj_on[of f A "f `A" g B "g `B"]`). The default `smart` does
  this only if reconstruction failed or timed out [S22].
- ITP 2025 (Lachnitt et al.): Isabelle now replays cvc5 Alethe proofs
  in the `smt` method. Before that, Alethe reconstruction was available
  only for veriT [S23]. The pipeline: ATPs give unsat cores, Isabelle
  tries simple tactics, then calls `smt` [S23].
- The target fragment of that work is "the (quantified) theory of linear
  (real and integer) arithmetic with uninterpreted functions" [S23].
  Bit-vectors, strings, regular expressions and finite sets are future
  work. The paper does not cover arrays or datatypes [S23].
- Results (ITP 2025, Table 2): cvc5 Alethe proofs were reconstructed in
  1326 of 1327 cases (16 facts) and 2906 of 2924 (1024 facts). Replay of
  cvc5 proofs took more time than veriT (1303 ms vs 334 ms at 1024
  facts) [S23].
- Z3 reconstruction in Isabelle/HOL and HOL4: Böhme and Weber, ITP 2010,
  "Fast LCF-style proof reconstruction for Z3" [S24].

### B.2 SMTCoq (Rocq/Coq)

- SMTCoq is a "certified checker for proof witnesses coming from the SAT
  solver ZChaff and the SMT solvers veriT and CVC4" [S26].
- It uses cvc5 only to compute abducts ("possibly missing hypotheses") when
  a solver fails [S26].
- The Alethe specification says: "The SMTCoq tool can reconstruct an older
  version of the format ... An effort to update the tool to the latest
  version of Alethe is ongoing" [S21].
- We did not find a release of SMTCoq that checks cvc5 CPC or cvc5 Alethe
  proofs.

### B.3 Lean

- **lean-smt** (Mohamed et al., arXiv 2505.15796, 2025): reconstructs cvc5
  CPC proofs step by step, then the Lean kernel checks the full proof [S28].
  - It uses Lean-Auto to reduce the goal to first-order logic [S28].
  - It supports "around 200" of more than 662 CPC rules (about 30%) [S28].
  - Fragments: UF, IDL, RDL, LIA, LRA, LIRA, with and without quantifiers.
    Arrays and datatypes are not listed; datatypes are future work [S28].
  - A step it cannot replay "is presented to the user to be proved
    manually" [S28].
- **Lean-Auto** (Qian, Clune, Barrett, Avigad, CAV 2025): a translation
  from Lean 4 (dependent type theory) to ATP/SMT input [S29].
- **QuerySMT** ("Hint-Based SMT Proof Reconstruction", Clune, Barbosa,
  Avigad, arXiv 2601.14495, TACAS 2026) [S25]:
  - It takes "hints" from the internal cvc5 proof: preprocessing lemmas,
    theory lemmas and rewrite steps. Only hints "used in the final proof"
    stay.
  - It uses the cvc5 unsat core to reduce the premise set.
  - It emits each hint as a `have` step, proves each with `grind`, then
    closes the goal with `duper` (a superposition prover in Lean).
  - It runs a `skolemizeAll` tactic before translation. It does not
    replay cvc5 Skolems.
  - It does not use quantifier instances as hints. The paper names this as
    future work.
  - After filtering, the final suggestions have on average 0.2 to 0.8 hints.
  - Limits reported: empty types, Nat encoding, AC normalization not in the
    hints, no induction, and `duper` "degrades significantly" with many
    unnecessary premises.

### B.4 Other work

- **Carcara** (Andreotti, Lachnitt, Barbosa, TACAS 2023): Alethe checker
  and elaborator in Rust. It can elaborate coarse steps into fine steps.
  It treats `lia_generic` as a hole by default, or calls an external solver
  such as cvc5 for it [S30].
- **F\***: records Z3 unsat cores as "hints" (`--record_hints`,
  `--use_hints`). On replay, Z3 sees only the facts in the core. If replay
  fails, F* runs Z3 again without hints. Hints can become stale [S27].
  F* does not reconstruct proofs.
- **Why3**: the prover answer type is `Valid`, `Invalid`, `Timeout`,
  `OutOfMemory`, `StepLimitExceeded`, `Unknown`, `Failure`, `HighFailure`
  [S31]. Why3 gets a verdict, not a proof object. EasyCrypt reads only
  this verdict (see C.1).
- **Dafny**: a 2026 Dafny paper (ProofPulse) notes that SMT solvers do not
  guarantee minimal cores, so tools add a deletion-based minimization
  step [S32]. We did not read the full paper.

### B.5 Typical failure modes of reconstruction

| Failure mode | Evidence | Relevance for Domino |
|---|---|---|
| Unsupported theory | Alethe from cvc5: EUF, LA, BV, parts of strings only [S8]. lean-smt: no arrays, no datatypes [S28]. ITP 2025: no arrays, no datatypes [S23]. Test T4: Alethe fails on `Maybe`. | Domino uses `Array` and `Maybe`. A full proof replay is not available in any of the tools we checked for this mix. |
| Holes and trust steps | Alethe `hole` for "untranslated rewrite" (Test T4). CPC `trust` steps for rules without Eunoia signature [S8b]. Isabelle times out on holes and `la_generic` [S23]. | A replay must prove these steps by other means. |
| Rewrites | cvc5 uses many internal rewrites; Isabelle needs IsaRARE lemmas for RARE rewrites [S23]. QuerySMT: AC normalization is not in the hints [S25]. | Instance terms come out rewritten (Test T3). A translator must map them back. |
| Skolemization | QuerySMT skolemizes in Lean first and does not replay cvc5 Skolems [S25]. Test T5: instance term `@quantifiers_skolemize_2`. | The Skolem for the negated goal invariant maps to the variable that `move=> x` introduces in EasyCrypt (opinion, see D). |
| Datatypes | lean-smt future work [S28]; Logos: no parametric datatypes [S10]; QuerySMT needs `Inhabited` for selector functions or leaves `sorry` [S25]. | `val` on `None` has no defined value in SMT; EasyCrypt `oget` has a fixed `witness` value. |
| Trigger brittleness | F*: a core is unsat, but the solver may not prove it again [S27]. | A core-based `smt(...)` hint list can fail in EasyCrypt with a different prover. |
| Too many premises | QuerySMT: `duper` degrades with unneeded premises [S25]. Sledgehammer minimizes facts [S22]. | Use minimal cores (A.1.3) or a delete-and-retry loop on the EasyCrypt side. |

## C. EasyCrypt

### C.1 How the `smt` tactic works

Syntax (parser `ecParser.mly`) [S12]:

- `smt` — default options.
- `smt(l1 l2 @Th -l3)` — hint lemmas. `@Th` adds all lemmas of theory `Th`;
  `-x` removes; `+x` (default) adds.
- `smt [opts]` — option names: `all`, `quorum`, `timeout`, `maxprovers`,
  `maxlemmas`, `wantedlemmas`, `unwantedlemmas`, `prover`, `verbose`,
  `lazy`, `full`, `dumpin`, `selected`, `debug`. The parser matches a
  short form of a name (`String.option_matching`) and gives an error if
  the short form is ambiguous. A bare integer (`smt 10`) sets `maxlemmas`;
  `timeout=n` and `prover=[...]` have their own syntax (`smt_info1`).
- `/#` and `//#` intro patterns call `smt` with `maxlemmas = 0`
  (`simple_smt_option`).
- `#smt` is also a rewrite step.

How the tactic chooses lemmas (`ecScope.ml` lines 696–699, `ecSmt.ml`
`select`) [S13][S14]:

| Call | `maxlemmas` used | Global lemmas sent |
|---|---|---|
| `smt` | default 50 (`pr_max = 50`) | Up to 50 lemmas from the relevance filter. |
| `smt()` | 0 | None. |
| `smt(l1 l2)` | 0 | Only `l1`, `l2`. No relevance filter lemmas. |
| `smt maxlemmas=n wantedlemmas=...` (or `smt n`) | n | The wanted lemmas plus up to n from the filter. |
| `smt all` | not used | All lemmas that are not `nosmt` and not unwanted. |
| `/#` | 0 | None. |

- The relevance filter follows "Lightweight Relevance Filtering for
  Machine-Generated Resolution Problems" (Meng and Paulson). It starts
  from the operators in the goal and in the local hypotheses
  (`f_ops_goal unwanted_ops hyps.h_local concl`), with start pass mark
  0.6 and factor 2.4 [S13].
- Only lemmas with `ax_smt = true` (lemmas not declared `nosmt`) take part,
  unless the user names them [S13].
- **Local hypotheses**: EasyCrypt sends **all** local hypotheses as axioms.
  `trans_hyp` adds every `LD_hyp f` with the comment
  `(* FIXME: Selection of hypothesis *)` [S13]. Local definitions
  (`LD_var` with a body) go to Why3 as definitions [S13]. Module types and
  abstract state are skipped [S13].
- Before the call, `process_smt` runs `t_simplify ~delta:`No` on the goal
  [S16]. A maintainer wrote in issue #918: "Before sending to `smt`, we
  simplify the goal (but not the hypotheses)" [S17].
- Default options (`dft_prover_infos`): `pr_timelimit = 3`, `pr_quorum = 1`,
  `pr_maxprocs = 3`, `pr_max = 50` [S14].
- Default provers: `dft_prover_names = ["Z3"; "CVC4"; "Alt-Ergo";
  "Eprover"; "Yices"]`, filtered by what Why3 knows [S14][S15].
  **CVC5 is not in this list.** You must name it with `prover=[...]` or
  the command-line prover option. The local `easycrypt config` shows
  `CVC5@1.4.0` as a known prover.
- `smt` modes: `Admit` (admits the goal), `Strict`, `Sloppy`, `Report`
  [S16].
- `selected` prints the selected lemmas as a warning. `dumpin` writes the
  Why3 task to a file (also with the environment variable `EC_WHY3`) [S13].
- `lazy` and `full` are parsed into `pprov_version`. We found no code that
  reads `pprov_version` in `ecScope.ml` or in the local source tree [S12].
  Treat these two options as no-ops (not confirmed by a test).
- EasyCrypt reads only the Why3 verdict (`Valid` etc.) [S14][S31]. It does
  not ask the prover for a core or a proof.

### C.2 Prior work: SMT diagnostics into EasyCrypt

We found **no** work that translates SMT proofs, unsat cores or
quantifier instances into EasyCrypt proofs or tactics.

What we searched:

- GitHub issues and PRs of `EasyCrypt/easycrypt` for "unsat core"
  (0 results), "proof reconstruction" (1 result: PR #1019, an LLM agent
  interface, not related), "cvc5" (20 results, about prover versions and
  issue #918 above) [S18].
- Web search for EasyCrypt with SMT proof reconstruction, unsat cores,
  hints. The EasyUC paper (2019) only says that a user "may specify the
  list of previously proven EasyCrypt lemmas the solvers may use" [S19].
- A 2018 EasyCrypt MPC paper says: "The SMT-solver does not provide
  information which lemmas were used" (reported by the search engine; we
  did not open the PDF) [S19b].
- We could not search the EasyCrypt Zulip or mailing list archives. They
  are not public on the web pages that we could reach.

Related crypto frameworks:

- **SSProve** (Rocq): we found no use of SMTCoq or other SMT
  reconstruction in SSProve or Nominal-SSProve [S33].
- **CryptHOL** (Isabelle): the paper uses relational parametricity "to
  adapt Isabelle's existing proof automation". We found no statement about
  Sledgehammer or SMT reconstruction in CryptHOL sources that we read [S34].
  Sledgehammer is available in any Isabelle theory, but we have no
  evidence on how much CryptHOL proofs use it.

## D. Synthesis: what each artifact can give an EasyCrypt proof step

> **Opinion.** All text in this section is our opinion. It is based on the
> evidence in A–C. We did not test any of these ideas in Domino.

| Artifact | What it can give EasyCrypt | Main obstacle | Evidence |
|---|---|---|---|
| Unsat core (`assumptions` mode) | Premise selection. Map named Domino assertions (definitions, invariant conjuncts, lemmas) to EasyCrypt lemma names and give them as `smt(l1 l2)`. Also: `clear` the local hypotheses that are not in the core, because EasyCrypt sends all hypotheses. | Domino must keep a map from SMT names to EasyCrypt names. A core can depend on cvc5 rewrites and triggers that Z3/Alt-Ergo through Why3 do not reproduce. `smt(l1 l2)` sends no other lemmas, so the list must be complete. | A.1, C.1 [S13][S27] |
| Minimal unsat core | Same, with fewer premises. Fewer premises help the receiving prover. | One extra check per core element; no time limit in the source; `unknown` answers keep extra elements. | A.1.3 [S6][S22][S25] |
| Unsat assumptions | Tells which goal conjunct fails. Useful to split an EasyCrypt goal with `split` and give hints per conjunct. | Needs the goal in conjuncts as Boolean assumption literals. | A.1.5 |
| Unsat core lemmas | Theory lemmas that the refutation uses. Possible `have` steps (QuerySMT style). | Needs `sat-proof` mode; lemmas are internal terms after preprocessing. | A.2 [S25] |
| Quantifier instances (with `produce-proofs`) | Explicit instance terms: `have := H k` or `have := Hinv (k+1)` in EasyCrypt, then `smt()`. A Skolem instance from the negated new invariant maps to the variable of `move=> x`. This is like Sledgehammer `instantiate` (`fact[of ...]`). | Output is a string, not terms. Terms are rewritten and can contain Skolems and `ite` from `store`. Domino must map them back to EasyCrypt syntax. Relevant instances only come with full proofs, which cost more. | A.4 [S6][S22] |
| Difficulty | Tells which assertions cause work. A hint to split the EasyCrypt goal (case split on a key equality) or to drop a hypothesis. | A heuristic score, not a proof artifact. | A.3 [S2][S4] |
| Timeout core | When cvc5 times out: the small set of assertions that still times out. Tells which invariant part or definition to treat by hand (for example `rewrite` or a helper lemma). | Up to N internal checks of 10 s each by default. | A.3 [S4][S6c] |
| Full CPC proof | In theory, a tactic script. In practice, the proof gives instances, Skolems and case structure (resolution on literals). | No checked translation exists for arrays plus parametric datatypes in any ITP that we found; lean-smt covers about 30% of the CPC rules; Alethe fails on datatypes (Test T4). EasyCrypt has no proof-term import. A step-by-step translation to EasyCrypt tactics is a research project. | A.5, B [S8][S10][S28] |

> **Opinion (order of value).** The cheapest useful path is: (1) name
> each Domino assertion, (2) get a minimal core and the relevant instances,
> (3) emit `have` steps for the instances and `smt(core lemmas)` for the
> rest, (4) on failure, fall back to the current admit. This is the
> QuerySMT approach [S25] and the F* hint approach [S27], adapted to
> EasyCrypt. A full proof translation is not a good first target.

## Things that contradict or refine the context

1. `print-unsat-cores-full` does not exist. The option is
   `print-cores-full` [S2].
2. There is no `get-instantiations` SMT-LIB command and no term-level API.
   `getInstantiations()` gives a string [S4][S9b].
3. The cvc5 Alethe printer does not support datatypes; our test with
   `Maybe` failed (Test T4) [S8].
4. EasyCrypt does not drop local hypotheses. It sends all of them. It also
   does not add relevance-filter lemmas when you give `smt(...)` hints
   [S13][S14].
5. CVC5 is not an EasyCrypt default prover [S14].
6. The crate function `get_named_terms` is `unsafe` because of a
   use-after-free in the C API [S20].
7. Relevant-only instances need full proofs, not only unsat cores [S6].
8. Domino uses `tlimit-per`. After a timeout, there is no unsat core;
   use `get-timeout-core` (needs `produce-unsat-cores`) [S4][S5].

## Test log (cvc5 1.4.2, local binary)

Test files were in the session scratch directory. They are not in the
repository. All were run without other options unless stated.

- **T1**: `incremental`, `produce-unsat-cores`, `Maybe` datatype, `Array Int
  (Maybe Int)`, `define-fun inv` with `forall`. Two push/pop goals. Cores:
  `(goal_a)` and `(invariant_old goal_b)`.
- **T2**: T1 with `--minimal-unsat-cores --print-cores-full`. Second core
  contained `(= inv (lambda ...))`, `(inv T1 T2)` and the goal. The
  warning "could not reduce unsat core due to unknown result" appeared on
  the output stream.
- **T3**: `produce-proofs`, `--dump-instantiations`: one instance
  `( (+ 1 k) )` of the invariant; an unused quantified assertion had no
  printed instances. CPC proof printed; `incremental` plus proofs also
  worked.
- **T4**: `--proof-format-mode=alethe`. With `Maybe`: error
  `DUMMY_SKOLEM`; with `--proof-alethe-testing`: error
  `APPLY_CONSTRUCTOR`. With `Int` arrays: proof with `forall_inst` and a
  `hole` ("untranslated rewrite").
- **T5**: goal `(not (inv (store T1 k (Some v)) (store T2 k (Some v))))`.
  Instance `@quantifiers_skolemize_2`. Debug source
  `QUANTIFIERS_INST_CBQI_CONFLICT`. Without proofs, a `skolem` block was
  printed with `store` rewritten to `ite`.
- **T6**: `check-sat-assuming (g1 g2)` → `unsat`, unsat assumptions
  `(g1)`; difficulty map printed; `get-timeout-core` → `sat`.

## Sources

cvc5 source paths are at tag `cvc5-1.4.0`
(`https://github.com/cvc5/cvc5/tree/cvc5-1.4.0`, commit `b432cd77`).

- [S1] cvc5 C++ API header `include/cvc5/cvc5.h` (getUnsatCore ...
  getInstantiations). https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/include/cvc5/cvc5.h
- [S2] `src/options/smt_options.toml`, `src/options/proof_options.toml`.
  https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/options/smt_options.toml ,
  https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/options/proof_options.toml .
  Online: https://cvc5.github.io/docs/cvc5-1.4.0/options.html
- [S2b] `src/options/quantifiers_options.toml` (`print-inst`,
  `print-inst-full`). https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/options/quantifiers_options.toml
- [S3] `src/options/main_options.toml` (`dump-instantiations`,
  `dump-instantiations-debug`, `dump-unsat-cores`, `dump-unsat-cores-lemmas`,
  `dump-proofs`, `dump-difficulty`). https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/options/main_options.toml
- [S3b] `src/options/base_options.toml` (output tags `inst`, `trigger`,
  `inst-strategy`, `learned-lits`, `unsat-core-benchmark`,
  `unsat-core-lemmas-benchmark`; `tlimit-per`). https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/options/base_options.toml
- [S4] Doc comments in `include/cvc5/cvc5.h` lines about 5957–6160 and
  6638–6644 (same file as S1).
- [S5] `src/api/cpp/cvc5.cpp`: `Solver::getUnsatCore` (line 7939),
  `getUnsatCoreLemmas` (≈7966), `getDifficulty` (7985), `getTimeoutCore`
  (≈8009), `getProof` (≈8051), `getLearnedLiterals` (≈8092),
  `getInstantiations` (8554). https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/api/cpp/cvc5.cpp
- [S6] `src/smt/unsat_core_manager.cpp` (`getUnsatCoreInternal`,
  `getRelevantQuantTermVectors`, `reduceUnsatCore` line 224) and
  `src/smt/solver_engine.cpp` (`printInstantiations` line 1970).
  https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/smt/unsat_core_manager.cpp ,
  https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/smt/solver_engine.cpp
- [S6b] `src/theory/smt_engine_subsolver.cpp` (`initializeSubsolver`).
  https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/theory/smt_engine_subsolver.cpp
- [S6c] `src/smt/timeout_core_manager.h`.
  https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/smt/timeout_core_manager.h
- [S7] `src/smt/set_defaults.cpp` lines 200–380, 625–650, 1297–1359.
  https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/smt/set_defaults.cpp
- [S8] cvc5 docs, "Proof format: Alethe" (page for 1.4.2).
  https://cvc5.github.io/docs/latest/proofs/output_alethe.html ; source
  `docs/proofs/output_alethe.rst` at cvc5-1.4.0.
- [S8b] cvc5 docs, "Proof format: Cooperating Proof Calculus"
  (`docs/proofs/output_cpc.rst`), and "Proof Production" (`proofs.rst`).
  https://cvc5.github.io/docs/cvc5-1.4.0/proofs/output_cpc.html
- [S9] `src/parser/commands.cpp` (`GetUnsatCoreCommand::printResult`,
  `GetTimeoutCoreCommand::printResult`). https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/src/parser/commands.cpp
- [S9b] `src/parser/smt2/` command keywords (`get-abduct` ...
  `get-value`; no `get-instantiations`). https://github.com/cvc5/cvc5/tree/cvc5-1.4.0/src/parser/smt2
- [S10] `NEWS.md` at cvc5-1.4.0 (sections 1.4.0, 1.3.0, 1.2.0, 1.1.2,
  1.1.0, 1.0.6, 1.0). https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/NEWS.md
- [S11] `include/cvc5/cvc5_types.h` (`ProofComponent`, `LearnedLitType`).
  https://github.com/cvc5/cvc5/blob/cvc5-1.4.0/include/cvc5/cvc5_types.h
- [S12] EasyCrypt `src/ecParser.mly` (smt options lines ≈196–356, `smt(...)`
  line 2931, `@Theory` line 2861, `smt_info` line 3985).
  https://github.com/EasyCrypt/easycrypt/blob/d1e7c102e9942649cba2499cb5c34a46951ba993/src/ecParser.mly
- [S13] EasyCrypt `src/ecSmt.ml` (`trans_hyp` 1164, FIXME 1195,
  `lenv_of_hyps` 1219, relevance filter 1401–1640, `select` 1666, `check`
  1684). https://github.com/EasyCrypt/easycrypt/blob/d1e7c102e9942649cba2499cb5c34a46951ba993/src/ecSmt.ml
- [S14] EasyCrypt `src/ecProvers.ml` (`dft_prover_infos` 412–426,
  `dft_prover_names` 428, `Driver.prove_task`) and `src/ecScope.ml`
  (lines 696–699, `set_default` ≈763).
  https://github.com/EasyCrypt/easycrypt/blob/d1e7c102e9942649cba2499cb5c34a46951ba993/src/ecProvers.ml ,
  https://github.com/EasyCrypt/easycrypt/blob/d1e7c102e9942649cba2499cb5c34a46951ba993/src/ecScope.ml
- [S15] Local `easycrypt config` output (known provers include
  `CVC5@1.4.0`), 2026-10-23.
- [S16] EasyCrypt `src/ecHiGoal.ml` `process_smt` (line 260).
  https://github.com/EasyCrypt/easycrypt/blob/d1e7c102e9942649cba2499cb5c34a46951ba993/src/ecHiGoal.ml
- [S17] EasyCrypt issue #918 "SMT not using hypothesis" (comment by
  strub). https://github.com/EasyCrypt/easycrypt/issues/918
- [S18] GitHub search API, repo EasyCrypt/easycrypt, queries "unsat core",
  "proof reconstruction", "cvc5", 2026-10-23.
  https://api.github.com/search/issues?q=repo:EasyCrypt/easycrypt+unsat+core
- [S19] Canetti et al., "EasyUC: Using EasyCrypt to Mechanize Proofs of
  Universally Composable Security", 2019. https://eprint.iacr.org/2019/582.pdf
- [S19b] "Computer-aided proofs for multiparty computation with active
  security", 2018 (statement as reported by search; PDF not read).
  https://arxiv.org/pdf/1806.07197
- [S20] Rust crate `cvc5` 0.6.1 source (`src/solver.rs` lines 288–640,
  763; `src/proof.rs`; `src/parser.rs` lines 114–160, 195–210) and
  `cvc5-sys` 0.6.1 `Cargo.toml` (`[package.metadata.cvc5] version =
  "1.4.0"`). https://docs.rs/cvc5/0.6.1/cvc5/struct.Solver.html ,
  https://github.com/cvc5/cvc5-rs
- [S21] Barbosa, Fleury, Fontaine, Schurr, "The Alethe Proof Format: An
  Evolving Specification and Reference", typeset 2026-03-31.
  https://verit.gitlabpages.uliege.be/alethe/specification.pdf
- [S22] Blanchette et al., "Hammering Away: A User's Guide to Sledgehammer
  for Isabelle/HOL" (PDF built 2026-01-18).
  https://isabelle.in.tum.de/doc/sledgehammer.pdf
- [S23] Lachnitt, Fleury, Barbosa, Jakpor, Andreotti, Reynolds, Schurr,
  Barrett, Tinelli, "Improving the SMT Proof Reconstruction Pipeline in
  Isabelle/HOL", ITP 2025, LIPIcs 352, paper 26.
  https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.26
- [S24] Böhme, Weber, "Fast LCF-Style Proof Reconstruction for Z3", ITP
  2010, LNCS 6172. https://user.it.uu.se/~tjawe125/publications/boehme10fast.html
- [S25] Clune, Barbosa, Avigad, "Hint-Based SMT Proof Reconstruction",
  arXiv 2601.14495 (2026), TACAS 2026.
  https://arxiv.org/html/2601.14495v1 ,
  https://link.springer.com/chapter/10.1007/978-3-032-22752-2_13
- [S26] SMTCoq repository README. https://github.com/smtcoq/smtcoq ;
  package page https://rocq-prover.org/p/coq-smtcoq
- [S27] F* wiki, "Robust, replayable proofs using unsat cores".
  https://github.com/FStarLang/FStar/wiki/Robust,-replayable-proofs-using-unsat-cores,-(aka,-hints,-or-how-to-replay-verification-in-milliseconds-instead-of-minutes)
- [S28] Mohamed et al., "Lean-SMT: An SMT tactic for discharging proof
  goals in Lean", arXiv 2505.15796 (2025). https://arxiv.org/html/2505.15796
- [S29] Qian, Clune, Barrett, Avigad, "Lean-Auto: An Interface Between
  Lean 4 and Automated Theorem Provers", CAV 2025, LNCS 15931.
  https://arxiv.org/abs/2505.14929
- [S30] Andreotti, Lachnitt, Barbosa, "Carcara: An Efficient Proof Checker
  and Elaborator for SMT Proofs in the Alethe Format", TACAS 2023.
  https://link.springer.com/chapter/10.1007/978-3-031-30823-9_19 ;
  https://github.com/ufmg-smite/carcara
- [S31] Why3 API, module `Call_provers` (prover answers).
  https://why3.lri.fr/api/Call_provers.html
- [S32] "ProofPulse: Interactive Proof Coverage Analysis for Dafny",
  arXiv 2608.30818 (statement as reported by search; not read in full).
  https://arxiv.org/pdf/2608.30818
- [S33] Abate et al., "SSProve: A Foundational Framework for Modular
  Cryptographic Proofs in Coq", https://eprint.iacr.org/2021/397 ;
  Nominal-SSProve, https://pure.itu.dk/en/publications/nominal-state-separating-proofs/
- [S34] Basin, Lochbihler, Sefidgar, "CryptHOL: Game-based Proofs in Higher-order Logic",
  https://eprint.iacr.org/2017/753 ; AFP entry https://isa-afp.org/entries/Game_Based_Crypto.html
