// SPDX-License-Identifier: MIT OR Apache-2.0

//! Invariant synthesis for equivalence proofsteps.
//!
//! Instead of checking the invariant provided by the user, we leave `invariant` open and ask a
//! solver to find one. For each requested oracle and goal we state the clause
//!
//! ```text
//! forall old states, oracle arguments, ...:
//!     invariant(old states) /\ randomness mapping /\ dependencies => goal
//! ```
//!
//! where the goal is a claim of the proof tree of the oracle or, if no claim is requested, one of
//! the two basic claims `invariant(new states)` and `same-output`. One more clause requires the
//! invariant to hold in the initial states, so that `false` is not a solution.
//!
//! `prove` declares the old states, oracle arguments, return values, etc. as global constants and
//! constrains them with assertions. Here, each of these constants becomes a quantified variable and
//! each of these assertions becomes a hypothesis of the clause. User-defined functions that read
//! such a constant are inlined into the clauses, because a quantifier can't bind a name inside the
//! body of a `define-fun`.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use wildcard::Wildcard;

use crate::{
    gamehops::equivalence::error::{Error, Result},
    package::Export,
    project::Project,
    theorem::Claim,
    ui::TheoremUI,
    util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse},
    writers::smt::{
        contexts::EquivalenceContext,
        exprs::{SmtAnd, SmtAssert, SmtExpr, SmtForall, SmtImplies, SmtLet},
        patterns::datastructures::DatastructurePattern,
    },
};

const INVARIANT_NAME: &str = "invariant";
const CLAIM_GROUP_NAME: &str = "invariant-synthesis";
const SYGUS_SOLVER: &str = "cvc5";

/// How the invariant synthesis problem is posed to the solver.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvariantSynthesisEncoding {
    /// `(declare-fun invariant ...)` and one `(assert (forall ...))` per clause, solved with the
    /// configured SMT solver. The clauses are constrained Horn clauses, so the query file can also
    /// be given to a CHC solver such as z3's Spacer.
    Smt,
    /// A SyGuS problem with `(synth-fun invariant ...)`, `(declare-var ...)` and one
    /// `(constraint ...)` per clause, solved with cvc5.
    Sygus,
}

impl InvariantSynthesisEncoding {
    fn query_file_name(self) -> &'static str {
        match self {
            Self::Smt => "query.smt2",
            Self::Sygus => "query.sy",
        }
    }
}

/// Splits an smt command like `(assert t)` into its name and arguments.
fn command(expr: &SmtExpr) -> Option<(&str, &[SmtExpr])> {
    let SmtExpr::List(items) = expr else {
        return None;
    };
    let (SmtExpr::Atom(name), args) = items.split_first()? else {
        return None;
    };
    Some((name, args))
}

fn atom(name: &str) -> SmtExpr {
    SmtExpr::Atom(name.to_string())
}

fn for_each_atom<'e>(expr: &'e SmtExpr, f: &mut impl FnMut(&'e str)) {
    match expr {
        SmtExpr::Atom(name) => f(name),
        SmtExpr::List(items) => {
            for item in items {
                for_each_atom(item, f);
            }
        }
        SmtExpr::Comment(_) => {}
    }
}

/// Whether an atom of `expr` is in `names` but not in `except`.
fn mentions_any_except(expr: &SmtExpr, names: &HashSet<String>, except: &HashSet<&str>) -> bool {
    let mut found = false;
    for_each_atom(expr, &mut |name| {
        found |= names.contains(name) && !except.contains(name);
    });
    found
}

fn mentions_any(expr: &SmtExpr, names: &HashSet<String>) -> bool {
    mentions_any_except(expr, names, &HashSet::new())
}

fn is_definition_of(expr: &SmtExpr, name: &str) -> bool {
    matches!(command(expr), Some(("=", [SmtExpr::Atom(lhs), _])) if lhs == name)
}

fn conjunction(mut terms: Vec<SmtExpr>) -> SmtExpr {
    match terms.len() {
        0 => atom("true"),
        1 => terms.pop().unwrap(),
        _ => SmtAnd(terms).into(),
    }
}

/// The smt code that `prove` emits as global constants and assertions, rephrased as quantified
/// variables and hypotheses.
#[derive(Clone, Debug, Default, PartialEq)]
struct Segment {
    binders: Vec<(String, SmtExpr)>,
    hypotheses: Vec<SmtExpr>,
    /// commands that neither declare nor constrain a constant, e.g. helper function definitions
    definitions: Vec<SmtExpr>,
}

impl Segment {
    fn new(exprs: impl IntoIterator<Item = SmtExpr>) -> Self {
        let mut segment = Self::default();

        for expr in exprs {
            match command(&expr) {
                Some(("declare-const", [SmtExpr::Atom(name), sort])) => {
                    segment.binders.push((name.clone(), sort.clone()));
                }
                Some(("define-fun", [SmtExpr::Atom(name), SmtExpr::List(params), sort, body]))
                    if params.is_empty() =>
                {
                    segment.binders.push((name.clone(), sort.clone()));
                    segment
                        .hypotheses
                        .push(("=", name.as_str(), body.clone()).into());
                }
                Some(("assert", [term])) => segment.hypotheses.push(term.clone()),
                _ if matches!(expr, SmtExpr::Comment(_)) => {}
                _ => segment.definitions.push(expr),
            }
        }

        segment
    }

    fn extend(&mut self, other: Segment) {
        self.binders.extend(other.binders);
        self.hypotheses.extend(other.hypotheses);
        self.definitions.extend(other.definitions);
    }
}

/// A clause `forall binders. hypotheses => goal` of the synthesis problem.
#[derive(Clone, Debug, PartialEq)]
struct Clause {
    binders: Vec<(String, SmtExpr)>,
    hypotheses: Vec<SmtExpr>,
    goal: SmtExpr,
}

impl Clause {
    fn new(
        segment: &Segment,
        hypotheses: impl IntoIterator<Item = SmtExpr>,
        goal: SmtExpr,
    ) -> Self {
        Self {
            binders: segment.binders.clone(),
            hypotheses: segment
                .hypotheses
                .iter()
                .cloned()
                .chain(hypotheses)
                .collect(),
            goal,
        }
    }

    fn binder_names(&self) -> HashSet<String> {
        self.binders.iter().map(|(name, _)| name.clone()).collect()
    }

    fn inline(&mut self, user_code: &UserCode) {
        for hypothesis in &mut self.hypotheses {
            *hypothesis = user_code.inline(hypothesis);
        }
        self.goal = user_code.inline(&self.goal);
    }

    /// Drops the quantified variables the clause doesn't need. A variable that occurs nowhere is
    /// dropped, and so is a variable `x` whose only occurrence is a hypothesis `(= x e)`, together
    /// with that hypothesis: `forall x. (= x e) /\ H => G` is equivalent to `H => G` when `x` occurs
    /// neither in `e` nor in `H` or `G`.
    ///
    /// This keeps the clauses of an oracle free of the return values, states and arguments of all
    /// other oracles.
    fn prune(&mut self) {
        loop {
            let mut occurrences: HashMap<&str, usize> = HashMap::new();
            for expr in self.hypotheses.iter().chain(std::iter::once(&self.goal)) {
                for_each_atom(expr, &mut |name| *occurrences.entry(name).or_default() += 1);
            }

            let removable = self
                .binders
                .iter()
                .enumerate()
                .find_map(|(idx, (name, _))| match occurrences.get(name.as_str()) {
                    None => Some((idx, None)),
                    Some(1) => self
                        .hypotheses
                        .iter()
                        .position(|hypothesis| is_definition_of(hypothesis, name))
                        .map(|hypothesis_idx| (idx, Some(hypothesis_idx))),
                    Some(_) => None,
                });

            let Some((idx, definition)) = removable else {
                break;
            };
            self.binders.remove(idx);
            if let Some(hypothesis_idx) = definition {
                self.hypotheses.remove(hypothesis_idx);
            }
        }
    }

    fn implication(&self) -> SmtExpr {
        SmtImplies(conjunction(self.hypotheses.clone()), self.goal.clone()).into()
    }

    fn to_smt(&self) -> SmtExpr {
        if self.binders.is_empty() {
            return SmtAssert(self.implication()).into();
        }

        SmtAssert(SmtForall {
            bindings: self.binders.clone(),
            body: self.implication(),
        })
        .into()
    }

    fn to_sygus(&self) -> SmtExpr {
        ("constraint", self.implication()).into()
    }
}

/// A function from the user-provided smt files.
#[derive(Clone, Debug, PartialEq)]
struct UserFunction {
    params: Vec<String>,
    body: SmtExpr,
}

/// The code of the user-provided smt files, split by whether it reads constants that are quantified
/// variables during synthesis.
#[derive(Debug, Default)]
struct UserCode {
    /// commands that don't read quantified variables and are emitted as they are
    closed: Vec<SmtExpr>,
    /// functions that read quantified variables, directly or through other such functions. They
    /// can't be defined globally, so calls to them are inlined.
    open_functions: HashMap<String, UserFunction>,
    /// assertions that read quantified variables, added as hypotheses to the clauses
    open_assertions: Vec<SmtExpr>,
}

impl UserCode {
    fn new(exprs: impl IntoIterator<Item = SmtExpr>, quantified: &HashSet<String>) -> Self {
        let mut code = Self::default();
        // reading one of these makes code open
        let mut open_names = quantified.clone();

        for expr in exprs {
            match command(&expr) {
                // this is what we are looking for, so the user's version is dropped
                Some(("define-fun", [SmtExpr::Atom(name), ..])) if name == INVARIANT_NAME => {}
                Some(("define-fun", [SmtExpr::Atom(name), SmtExpr::List(params), _sort, body])) => {
                    let params: Vec<String> = params
                        .iter()
                        .filter_map(|param| command(param).map(|(name, _sort)| name.to_string()))
                        .collect();
                    let shadowed = params.iter().map(String::as_str).collect();

                    if mentions_any_except(body, &open_names, &shadowed) {
                        let function = UserFunction {
                            params,
                            body: body.clone(),
                        };
                        open_names.insert(name.clone());
                        code.open_functions.insert(name.clone(), function);
                    } else {
                        code.closed.push(expr.clone());
                    }
                }
                Some(("assert", [term])) if mentions_any(term, &open_names) => {
                    code.open_assertions.push(term.clone());
                }
                _ => code.closed.push(expr.clone()),
            }
        }

        code
    }

    /// Replaces calls to open functions with their bodies, binding the parameters with `let`.
    fn inline(&self, expr: &SmtExpr) -> SmtExpr {
        match expr {
            SmtExpr::Atom(name) => match self.open_functions.get(name) {
                Some(function) if function.params.is_empty() => self.inline(&function.body),
                _ => expr.clone(),
            },
            SmtExpr::List(items) => {
                if let Some((SmtExpr::Atom(name), args)) = items.split_first() {
                    if let Some(function) = self.open_functions.get(name) {
                        if function.params.len() == args.len() {
                            let bindings = function
                                .params
                                .iter()
                                .cloned()
                                .zip(args.iter().map(|arg| self.inline(arg)))
                                .collect();

                            return SmtLet {
                                bindings,
                                body: self.inline(&function.body),
                            }
                            .into();
                        }
                    }
                }

                SmtExpr::List(items.iter().map(|item| self.inline(item)).collect())
            }
            SmtExpr::Comment(_) => expr.clone(),
        }
    }
}

/// A synthesis problem, independent of how it is posed to the solver.
struct Problem {
    /// datatypes, oracle functions, etc.; the same as for `prove`
    prefix: Vec<SmtExpr>,
    /// parameter names and sorts of the invariant
    invariant_params: Vec<(String, SmtExpr)>,
    user_code: UserCode,
    /// helper functions of the oracles, e.g. the randomness mappings and relations
    definitions: Vec<SmtExpr>,
    clauses: Vec<Clause>,
}

impl Problem {
    fn to_smt(&self) -> Vec<SmtExpr> {
        let sorts = self
            .invariant_params
            .iter()
            .map(|(_name, sort)| sort.clone())
            .collect();

        let mut out = self.prefix.clone();
        out.push(("declare-fun", INVARIANT_NAME, SmtExpr::List(sorts), "Bool").into());
        out.extend(self.user_code.closed.iter().cloned());
        out.extend(self.definitions.iter().cloned());
        out.extend(self.clauses.iter().map(Clause::to_smt));
        out
    }

    fn to_sygus(&self) -> Vec<SmtExpr> {
        // SyGuS has no assertions. Assumptions constrain the uninterpreted functions in the same
        // way.
        let assert_to_assume = |expr: &SmtExpr| -> SmtExpr {
            match command(expr) {
                Some(("assert", [term])) => ("assume", term.clone()).into(),
                _ => expr.clone(),
            }
        };

        let params = self
            .invariant_params
            .iter()
            .map(|(name, sort)| (name.as_str(), sort.clone()).into())
            .collect();

        let mut out: Vec<SmtExpr> = self.prefix.iter().map(assert_to_assume).collect();
        out.push(("synth-fun", INVARIANT_NAME, SmtExpr::List(params), "Bool").into());
        out.extend(self.user_code.closed.iter().map(assert_to_assume));
        out.extend(self.definitions.iter().cloned());

        // all constraints are quantified over all variables, so clauses can share them
        let mut declared = HashSet::new();
        for (name, sort) in self.clauses.iter().flat_map(|clause| &clause.binders) {
            if declared.insert(name) {
                out.push(("declare-var", name.as_str(), sort.clone()).into());
            }
        }

        out.extend(self.clauses.iter().map(Clause::to_sygus));
        out.push(SmtExpr::List(vec![atom("check-synth")]));
        out
    }
}

/// Finds `(define-fun <name> ...)` in solver output.
fn extract_define_fun(output: &str, name: &str) -> Option<String> {
    let start = output.find(&format!("(define-fun {name} "))?;

    let mut depth = 0usize;
    for (offset, c) in output[start..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(output[start..=start + offset].to_string());
                }
            }
            _ => {}
        }
    }

    None
}

/// What an invariant is synthesized for.
enum Scope<'a> {
    Proofstep,
    Oracle(&'a str),
    Claim {
        oracle_name: &'a str,
        claim: &'a str,
    },
}

impl Scope<'_> {
    fn description(&self) -> String {
        match self {
            Self::Proofstep => "all oracles".to_string(),
            Self::Oracle(oracle_name) => format!("oracle {oracle_name}"),
            Self::Claim { oracle_name, claim } => format!("claim {claim} of oracle {oracle_name}"),
        }
    }

    /// The directory below the synthesis directory of the equivalence.
    fn path(&self) -> PathBuf {
        match self {
            Self::Proofstep => PathBuf::from("!all-oracles!"),
            Self::Oracle(oracle_name) => PathBuf::from(oracle_name),
            Self::Claim { oracle_name, claim } => PathBuf::from(oracle_name).join(claim),
        }
    }
}

fn io_error(path: &Path, err: std::io::Error) -> Error {
    Error::InvariantSynthesisIo {
        path: path.to_path_buf(),
        err,
    }
}

pub(crate) struct InvariantSynthesisDriver<'a, Backend: SmtSolverBackend, Proj: Project> {
    eqctx: &'a EquivalenceContext<'a>,
    project: &'a Proj,
    backend: &'a Backend,
    encoding: InvariantSynthesisEncoding,
    req_oracle: Option<&'a str>,
    req_claim: Option<&'a str>,
}

impl<'a, Backend: SmtSolverBackend, Proj: Project> InvariantSynthesisDriver<'a, Backend, Proj> {
    pub(crate) fn new(
        eqctx: &'a EquivalenceContext<'a>,
        project: &'a Proj,
        backend: &'a Backend,
        encoding: InvariantSynthesisEncoding,
        req_oracle: Option<&'a str>,
        req_claim: Option<&'a str>,
    ) -> Self {
        Self {
            eqctx,
            project,
            backend,
            encoding,
            req_oracle,
            req_claim,
        }
    }

    pub(crate) fn synthesize<UI: TheoremUI>(&self, ui: &mut UI) -> Result<()> {
        self.eqctx.verify_exports_match()?;

        let scope = self.scope()?;
        let problem = self.problem()?;

        let eq = self.eqctx.equivalence();
        let theorem_name = &self.eqctx.theorem().name;
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());

        let dir = self
            .project
            .get_root_dir()
            .join("_build/invariant_synthesis")
            .join(theorem_name)
            .join(format!("{}-{}", eq.left_name(), eq.right_name()))
            .join(scope.path());
        std::fs::create_dir_all(&dir).map_err(|err| io_error(&dir, err))?;
        let query_file = dir.join(self.encoding.query_file_name());

        ui.proofstep_set_claim_groups_count(theorem_name, &proofstep_name, 1);
        ui.start_claim_group(theorem_name, &proofstep_name, CLAIM_GROUP_NAME, 1);
        ui.start_claim(
            theorem_name,
            &proofstep_name,
            CLAIM_GROUP_NAME,
            &scope.description(),
        );

        let result = match self.encoding {
            InvariantSynthesisEncoding::Smt => self.solve_smt(&problem, &query_file, &scope),
            InvariantSynthesisEncoding::Sygus => self.solve_sygus(&problem, &query_file, &scope),
        };

        ui.finish_claim(
            theorem_name,
            &proofstep_name,
            CLAIM_GROUP_NAME,
            &scope.description(),
        );
        ui.finish_claim_group(theorem_name, &proofstep_name, CLAIM_GROUP_NAME);

        let invariant = result?;
        let invariant_file = dir.join("invariant.smt2");
        std::fs::write(&invariant_file, format!("{invariant}\n"))
            .map_err(|err| io_error(&invariant_file, err))?;

        // not `ui.println`: indicatif drops it when stderr is not a terminal
        println!(
            "synthesized invariant for {} of {proofstep_name}:\n{invariant}\nwritten to {}\nquery: {}",
            scope.description(),
            invariant_file.display(),
            query_file.display(),
        );
        Ok(())
    }

    fn scope(&self) -> Result<Scope<'a>> {
        match (self.req_oracle, self.req_claim) {
            (None, None) => Ok(Scope::Proofstep),
            (Some(oracle_name), None) => Ok(Scope::Oracle(oracle_name)),
            (Some(oracle_name), Some(claim)) => Ok(Scope::Claim { oracle_name, claim }),
            (None, Some(claim)) => Err(Error::InvariantSynthesisClaimWithoutOracle {
                claim_pattern: claim.to_string(),
            }),
        }
    }

    fn oracles(&self) -> Result<Vec<&'a Export>> {
        let oracles = self.eqctx.oracle_sequence();

        let Some(req_oracle) = self.req_oracle else {
            return Ok(oracles);
        };

        match oracles.iter().find(|export| export.name() == req_oracle) {
            Some(export) => Ok(vec![*export]),
            None => {
                let eq = self.eqctx.equivalence();
                Err(Error::InvariantSynthesisUnknownOracle {
                    oracle_name: req_oracle.to_string(),
                    left_game_inst_name: eq.left_name().to_string(),
                    right_game_inst_name: eq.right_name().to_string(),
                    exported_oracle_names: oracles
                        .iter()
                        .map(|export| export.name().to_string())
                        .collect(),
                })
            }
        }
    }

    /// The claims the invariant has to prove for the oracle: the requested claims of its proof
    /// tree, or the basic claims if no claim is requested.
    fn goals(&self, oracle_name: &str) -> Result<Vec<Claim>> {
        let Some(req_claim) = self.req_claim else {
            return Ok(["invariant", "same-output"]
                .map(|name| Claim::from_tuple((name.to_string(), vec![], false)))
                .into());
        };

        let pattern = Wildcard::new(req_claim.as_bytes()).unwrap();
        let (matching, others): (Vec<_>, Vec<_>) = self
            .eqctx
            .equivalence()
            .proof_tree_by_oracle_name(oracle_name)
            .into_iter()
            .partition(|claim| pattern.is_match(claim.name().as_bytes()));

        if matching.is_empty() {
            return Err(Error::InvariantSynthesisUnknownClaim {
                claim_pattern: req_claim.to_string(),
                oracle_name: oracle_name.to_string(),
                available_claim_names: others
                    .iter()
                    .map(|claim| claim.name().to_string())
                    .collect(),
            });
        }

        Ok(matching)
    }

    fn problem(&self) -> Result<Problem> {
        let eqctx = self.eqctx;

        let mut prefix = eqctx.emit_base_declarations();
        prefix.extend(eqctx.emit_theorem_paramfuncs());
        prefix.extend(eqctx.emit_game_definitions());

        let constants = Segment::new(eqctx.emit_constant_declarations());
        let mut definitions = Vec::new();
        let mut clauses = Vec::new();

        for oracle in self.oracles()? {
            let oracle_name = oracle.name();

            let mut segment = constants.clone();
            segment.extend(Segment::new(
                eqctx
                    .emit_auto_randomness(oracle_name)
                    .into_iter()
                    .chain(eqctx.emit_return_value_helpers(oracle_name))
                    .chain(eqctx.emit_randomness_mapping_condition(oracle_name)),
            ));
            definitions.append(&mut segment.definitions);

            for claim in self.goals(oracle_name)? {
                let parts = eqctx.oracle_claim_parts(&claim, oracle_name);
                // Package and game invariants are not assumed, because proving them relies on the
                // invariant we are looking for.
                let hypotheses = [parts.randomness_mapping, parts.invariant_old]
                    .into_iter()
                    .chain(parts.dependencies);

                clauses.push(Clause::new(&segment, hypotheses, parts.postcondition));
            }
        }

        let initial = Segment::new(eqctx.emit_initial_state_values());
        clauses.push(Clause::new(&initial, [], eqctx.invariant_start_call()));
        definitions.extend(initial.definitions);

        let quantified: HashSet<String> = clauses.iter().flat_map(Clause::binder_names).collect();
        let user_code = UserCode::new(eqctx.emit_invariant(), &quantified);

        for clause in &mut clauses {
            // an assertion reading variables that the clause doesn't quantify over can't be stated
            // in it
            let unbound = &quantified - &clause.binder_names();
            clause.hypotheses.extend(
                user_code
                    .open_assertions
                    .iter()
                    .filter(|assertion| !mentions_any(assertion, &unbound))
                    .cloned(),
            );

            clause.inline(&user_code);
            clause.prune();
        }

        let state_sort = |gctx: crate::writers::smt::contexts::GameInstanceContext| {
            atom(&gctx.datastructure_game_state_pattern().sort_name())
        };
        let invariant_params = vec![
            (
                "state-left".to_string(),
                state_sort(eqctx.left_game_inst_ctx()),
            ),
            (
                "state-right".to_string(),
                state_sort(eqctx.right_game_inst_ctx()),
            ),
        ];

        Ok(Problem {
            prefix,
            invariant_params,
            user_code,
            definitions,
            clauses,
        })
    }

    fn failed(&self, scope: &Scope, query_file: &Path, answer: String) -> Error {
        let eq = self.eqctx.equivalence();

        Error::InvariantSynthesisFailed {
            left_game_inst_name: eq.left_name().to_string(),
            right_game_inst_name: eq.right_name().to_string(),
            scope: scope.description(),
            answer,
            query_file: query_file.to_path_buf(),
        }
    }

    fn solve_smt(&self, problem: &Problem, query_file: &Path, scope: &Scope) -> Result<String> {
        let description = scope.description();
        let solver_error = |err: crate::util::smtsolver::Error| {
            Error::prover_process_error(&description, CLAIM_GROUP_NAME, err)
        };

        let transcript =
            std::fs::File::create(query_file).map_err(|err| io_error(query_file, err))?;
        let mut solver = self
            .backend
            .new_smtsolver_with_transcript(transcript)
            .map_err(solver_error)?;

        for expr in problem.to_smt() {
            solver.write_smt(expr).map_err(solver_error)?;
        }

        let result = match solver.check_sat().map_err(solver_error)? {
            SmtSolverResponse::Sat => {
                let (model, _) = solver.get_model().map_err(solver_error)?;
                extract_define_fun(&model, INVARIANT_NAME).ok_or_else(|| {
                    self.failed(
                        scope,
                        query_file,
                        format!("sat, but the model doesn't define {INVARIANT_NAME}"),
                    )
                })
            }
            SmtSolverResponse::Unsat => Err(self.failed(
                scope,
                query_file,
                "unsat, so no invariant satisfies all clauses".to_string(),
            )),
            response => Err(self.failed(scope, query_file, response.to_string())),
        };

        solver.close();
        result
    }

    fn solve_sygus(&self, problem: &Problem, query_file: &Path, scope: &Scope) -> Result<String> {
        let query: String = problem
            .to_sygus()
            .iter()
            .map(|expr| format!("{expr}\n"))
            .collect();
        std::fs::write(query_file, query).map_err(|err| io_error(query_file, err))?;

        let output = std::process::Command::new(SYGUS_SOLVER)
            .arg("--lang=sygus2")
            .arg(query_file)
            .output()
            .map_err(|err| Error::InvariantSynthesisSolverSpawn {
                solver: SYGUS_SOLVER,
                err,
            })?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        extract_define_fun(&stdout, INVARIANT_NAME).ok_or_else(|| {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let answer = [stdout.trim(), stderr.trim()]
                .into_iter()
                .filter(|text| !text.is_empty())
                .collect::<Vec<_>>()
                .join("\n");

            self.failed(scope, query_file, answer)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parses smt code into expressions. Only supports what the tests below use.
    fn parse(code: &str) -> Vec<SmtExpr> {
        fn parse_expr(tokens: &mut std::iter::Peekable<std::vec::IntoIter<String>>) -> SmtExpr {
            let token = tokens.next().expect("unexpected end of input");
            if token != "(" {
                return SmtExpr::Atom(token);
            }

            let mut items = Vec::new();
            while tokens.peek().expect("unclosed list") != ")" {
                items.push(parse_expr(tokens));
            }
            tokens.next();
            SmtExpr::List(items)
        }

        let mut tokens = code
            .replace('(', " ( ")
            .replace(')', " ) ")
            .split_whitespace()
            .map(str::to_string)
            .collect::<Vec<_>>()
            .into_iter()
            .peekable();

        let mut exprs = Vec::new();
        while tokens.peek().is_some() {
            exprs.push(parse_expr(&mut tokens));
        }
        exprs
    }

    fn parse_one(code: &str) -> SmtExpr {
        let mut exprs = parse(code);
        assert_eq!(exprs.len(), 1, "expected a single expression in {code}");
        exprs.pop().unwrap()
    }

    fn names(names: &[&str]) -> HashSet<String> {
        names.iter().map(|name| name.to_string()).collect()
    }

    #[test]
    fn segment_turns_constants_into_variables_and_assertions_into_hypotheses() {
        let segment = Segment::new(parse(
            "(declare-const old State)
             (define-fun consts () Consts (mapping theorem-consts))
             (assert (= ret (oracle old consts)))
             (define-fun helper ((x Int)) Bool (> x 0))",
        ));

        assert_eq!(
            segment.binders,
            vec![
                ("old".to_string(), atom("State")),
                ("consts".to_string(), atom("Consts")),
            ]
        );
        assert_eq!(
            segment.hypotheses,
            parse("(= consts (mapping theorem-consts)) (= ret (oracle old consts))")
        );
        assert_eq!(
            segment.definitions,
            parse("(define-fun helper ((x Int)) Bool (> x 0))")
        );
    }

    #[test]
    fn prune_drops_variables_that_are_only_defined() {
        let mut clause = Clause {
            binders: ["old", "ret", "new", "other-ret", "ctr"]
                .iter()
                .map(|name| (name.to_string(), atom("S")))
                .collect(),
            hypotheses: parse(
                "(= ret (oracle old))
                 (= new (state ret))
                 (= other-ret (other-oracle old))
                 (= ctr (rand old))
                 (= ctr 0)",
            ),
            goal: parse_one("(invariant new)"),
        };

        clause.prune();

        let binders: Vec<_> = clause
            .binders
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        // `other-ret` is only defined, `ctr` is also constrained to 0 and so must stay
        assert_eq!(binders, vec!["old", "ret", "new", "ctr"]);
        assert_eq!(
            clause.hypotheses,
            parse("(= ret (oracle old)) (= new (state ret)) (= ctr (rand old)) (= ctr 0)")
        );
    }

    #[test]
    fn prune_drops_chains_of_unused_definitions() {
        let mut clause = Clause {
            binders: ["old", "ret", "value", "is-abort"]
                .iter()
                .map(|name| (name.to_string(), atom("S")))
                .collect(),
            hypotheses: parse(
                "(= ret (oracle old)) (= value (get ret)) (= is-abort (abort value))",
            ),
            goal: parse_one("(invariant old)"),
        };

        clause.prune();

        assert_eq!(clause.binders, vec![("old".to_string(), atom("S"))]);
        assert!(clause.hypotheses.is_empty());
    }

    #[test]
    fn user_code_inlines_functions_reading_quantified_variables() {
        let code = UserCode::new(
            parse(
                "(define-fun invariant ((l S) (r S)) Bool true)
                 (define-fun closed ((x Int)) Bool (> x 0))
                 (define-fun open ((x Int)) Bool (= x arg))
                 (define-fun uses-open ((y Int)) Bool (open y))
                 (define-fun shadows ((arg Int)) Bool (= arg 1))
                 (assert (closed 1))
                 (assert (uses-open 2))",
            ),
            &names(&["arg"]),
        );

        assert_eq!(
            code.closed,
            parse(
                "(define-fun closed ((x Int)) Bool (> x 0))
                 (define-fun shadows ((arg Int)) Bool (= arg 1))
                 (assert (closed 1))"
            )
        );
        assert_eq!(code.open_assertions, parse("(uses-open 2)"));

        let mut open: Vec<_> = code.open_functions.keys().map(String::as_str).collect();
        open.sort();
        assert_eq!(open, vec!["open", "uses-open"]);

        assert_eq!(
            code.inline(&parse_one("(and (uses-open 5) (closed 3))")),
            parse_one("(and (let ((y 5)) (let ((x y)) (= x arg))) (closed 3))")
        );
    }

    #[test]
    fn extract_define_fun_finds_balanced_definition() {
        let model = "(
(define-fun invariant-other ((s Int)) Bool true)
(define-fun invariant ((s0 A) (s1 B)) Bool (= (ctr s0) (ctr s1)))
)";

        assert_eq!(
            extract_define_fun(model, "invariant").as_deref(),
            Some("(define-fun invariant ((s0 A) (s1 B)) Bool (= (ctr s0) (ctr s1)))")
        );
        assert_eq!(extract_define_fun("infeasible", "invariant"), None);
    }

    #[test]
    fn clauses_without_variables_or_hypotheses_are_plain_assertions() {
        let clause = Clause {
            binders: vec![],
            hypotheses: vec![],
            goal: parse_one("(invariant init)"),
        };

        assert_eq!(
            clause.to_smt(),
            parse_one("(assert (=> true (invariant init)))")
        );
    }

    #[test]
    fn sygus_declares_shared_variables_once_and_assumes_assertions() {
        let clause = |goal: &str| Clause {
            binders: vec![("old".to_string(), atom("S"))],
            hypotheses: parse("(invariant old)"),
            goal: parse_one(goal),
        };

        let problem = Problem {
            prefix: parse("(set-logic ALL) (assert (= (f 0) 5))"),
            invariant_params: vec![("state".to_string(), atom("S"))],
            user_code: UserCode::default(),
            definitions: vec![],
            clauses: vec![clause("(p old)"), clause("(q old)")],
        };

        assert_eq!(
            problem.to_sygus(),
            parse(
                "(set-logic ALL)
                 (assume (= (f 0) 5))
                 (synth-fun invariant ((state S)) Bool)
                 (declare-var old S)
                 (constraint (=> (invariant old) (p old)))
                 (constraint (=> (invariant old) (q old)))
                 (check-synth)"
            )
        );
    }
}
