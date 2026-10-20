// SPDX-License-Identifier: MIT OR Apache-2.0

//! The SMT context for proving the invariant of a single package.
//!
//! This is the single-game counterpart of
//! [`EquivalenceContext`](crate::writers::smt::contexts::EquivalenceContext): it emits the
//! declarations of one game (the closed package alone, from [`super::open_game`]), the call-result
//! records of its oracles (ADR 0017), and the two kinds of claims a package invariant consists of.

use std::collections::HashSet;

use crate::{
    gamehops::equivalence::smtrewrite::{self, SmtStatementKind, SmtStmt},
    package::{Package, PackageInstance},
    project::Project,
    statement::{Assignment, AssignmentRhs, Pattern, Statement},
    theorem::{
        BuiltInFact, ClaimKind, GameInstance, InvariantSide, ResolvedClaim, ResolvedDependency,
        Theorem,
    },
    transforms::{
        samplify::SampleInfo,
        theorem_transforms::{self, GameInstAux},
    },
    types::{Type, TypeKind},
    writers::smt::{
        contexts::{game_defs, GameInstanceContext, GenericOracleContext},
        declare::{declare_const, declare_single_constructor_datatype},
        exprs::{SmtAnd, SmtAssert, SmtExpr, SmtImplies, SmtNot},
        names,
        patterns::{
            self,
            functions::FunctionPattern,
            oracle_args::{
                GameStateOracleArgPattern, GameStateOracleArgVariant, OracleArgPattern,
                UnitOracleArgPattern,
            },
            theorem_constants::ConstantPattern,
            ReturnIsAbortConst,
        },
    },
};

use super::{
    error::{Error, Result},
    open_calls, open_game,
};

/// Everything needed to emit the SMT for the invariant of one package.
pub(crate) struct PackageInvariantContext<'a> {
    pkg: &'a Package,
    theorem: Theorem<'a>,
    game_inst_name: String,
    pkg_inst_name: String,
    types: HashSet<Type>,
    sample_info: SampleInfo,
    /// the rewritten contents of the package's invariant files
    invariants: Vec<SmtStmt>,
}

impl<'a> PackageInvariantContext<'a> {
    /// Closes `pkg` (open calls), builds its one-game theorem, runs it through the usual
    /// transformation pipeline and reads the package's invariant files.
    ///
    /// Errors: [`Error::NoInvariant`], [`Error::OpenCallInLoop`], and the errors of reading and
    /// rewriting the invariant files.
    pub(crate) fn new(pkg: &'a Package, project: &impl Project) -> Result<Self> {
        if pkg.invariants.is_empty() {
            return Err(Error::NoInvariant {
                pkg_name: pkg.name.clone(),
            });
        }

        let closed = open_calls::close_package(pkg)?;
        let theorem = open_game::open_game_theorem(&closed);
        let game_inst_name = theorem.instances[0].name().to_string();
        let pkg_inst_name = pkg.name.clone();

        let (
            game_inst,
            GameInstAux {
                types, sample_info, ..
            },
        ) = theorem_transforms::transform_game_inst(&theorem.instances[0])
            .expect("transforming the closed package game failed unexpectedly");

        let theorem = theorem.with_new_instances(vec![game_inst]);

        let mut this = Self {
            pkg,
            theorem,
            game_inst_name,
            pkg_inst_name,
            types,
            sample_info,
            invariants: Vec::new(),
        };

        this.load_invariants(project)?;

        Ok(this)
    }

    fn load_invariants(&mut self, project: &impl Project) -> Result<()> {
        let mut out = Vec::new();

        for file_name in &self.pkg.invariants {
            let file_contents =
                project
                    .read_input_file(file_name)
                    .map_err(|err| Error::InvariantFileRead {
                        invariant_file_name: file_name.clone(),
                        err,
                    })?;

            out.append(
                &mut smtrewrite::rewrite_standalone_package(
                    self.game_inst(),
                    self.pkg_inst(),
                    &file_contents,
                )
                .map_err(Box::new)?,
            );
        }

        self.invariants = out;
        Ok(())
    }

    pub(crate) fn pkg_name(&self) -> &'a str {
        &self.pkg.name
    }

    fn game_inst(&self) -> &GameInstance {
        &self.theorem.instances[0]
    }

    fn game_inst_ctx(&self) -> GameInstanceContext<'_> {
        GameInstanceContext::new(self.game_inst())
    }

    fn pkg_inst(&self) -> &PackageInstance {
        self.game_inst()
            .game()
            .pkgs
            .iter()
            .find(|pkg_inst| pkg_inst.name == self.pkg_inst_name)
            .expect("the package is the only package of its game")
    }

    /// One claim for each named invariant of the package (`package-invariant!<name>!<P>!`), in
    /// declaration order. The game has one side only; the claims say `Left`.
    pub(crate) fn invariant_claims(&self) -> Vec<ResolvedClaim> {
        self.invariants
            .iter()
            .filter(|stmt| matches!(stmt.kind, SmtStatementKind::PackageInvariant { .. }))
            .map(|stmt| ResolvedClaim {
                name: stmt.kind.name(),
                kind: ClaimKind::PackageInvariant {
                    side: InvariantSide::Left,
                },
                dependencies: vec![ResolvedDependency {
                    name: BuiltInFact::NoAbort.name().to_string(),
                    kind: ClaimKind::BuiltIn(BuiltInFact::NoAbort),
                }],
                admitted: false,
            })
            .collect()
    }

    /// The names of the oracles the package exposes, in declaration order.
    pub(crate) fn oracle_names(&self) -> Vec<String> {
        self.pkg
            .oracles
            .iter()
            .map(|odef| odef.sig.name.clone())
            .collect()
    }
}

// emitting SMT
impl PackageInvariantContext<'_> {
    pub(crate) fn emit_base_declarations(&self) -> Vec<SmtExpr> {
        let mut types: Vec<Type> = self
            .types
            .union(&game_defs::theorem_const_bits_types(&self.theorem))
            .cloned()
            .collect();
        types.sort();

        game_defs::emit_base_declarations(&types)
    }

    /// One `declare-datatype` for each oracle with import calls: its call-result record
    /// `<P>-<O>-calls`, with one field for each call site, in control-flow order (ADR 0017). The
    /// oracle functions take the record as an argument, so this comes before them.
    pub(crate) fn emit_call_records(&self) -> Vec<SmtExpr> {
        self.pkg_inst()
            .pkg
            .oracles
            .iter()
            .filter_map(|odef| match odef.code.0.first() {
                Some(Statement::Assignment(
                    Assignment {
                        pattern: Pattern::Tuple(fields),
                        rhs: AssignmentRhs::Expression(expr),
                    },
                    _,
                )) => match expr.get_type().into_kind() {
                    TypeKind::UserDefined(record) => Some(declare_single_constructor_datatype(
                        &record,
                        &names::call_record_constructor(&record),
                        fields.iter().enumerate().map(|(i, field)| {
                            (
                                names::call_record_field(&record, i + 1),
                                field.get_type().into(),
                            )
                        }),
                    )),
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    pub(crate) fn emit_theorem_paramfuncs(&self) -> Vec<SmtExpr> {
        game_defs::emit_theorem_paramfuncs(&self.theorem)
    }

    pub(crate) fn emit_game_definitions(&self) -> Vec<SmtExpr> {
        game_defs::emit_game_definitions(
            &self.theorem,
            &[(self.game_inst_ctx(), &self.sample_info)],
        )
    }

    /// The definition of the package invariant itself.
    pub(crate) fn emit_invariant(&self) -> Vec<SmtExpr> {
        self.invariants
            .iter()
            .map(|stmt| stmt.expr.clone())
            .collect()
    }

    /// Declares the constants the oracle claims talk about: the old game state, the game
    /// constants, the oracle arguments, the oracle return values and the randomness.
    pub(crate) fn emit_constant_declarations(&self) -> Vec<SmtExpr> {
        let gctx = self.game_inst_ctx();
        let game_inst = self.game_inst();
        let game_inst_name = &self.game_inst_name;
        let game_name = gctx.game_name();

        let mut out = Vec::new();

        // the old game state, i.e. the arbitrary state we assume the invariant to hold in
        let game_state = gctx.oracle_arg_game_state_pattern();
        out.push(game_state.declare_old(game_inst_name));

        // the theorem constants are arbitrary: this is what makes the proof hold for arbitrary
        // package constants. The game constants are derived from them.
        let theorem_consts = patterns::oracle_args::TheoremConstsPattern {
            theorem_name: &self.theorem.name,
        };
        let game_consts = patterns::oracle_args::GameConstsPattern { game_name };

        // the interface requires us to pass in a game instance name, but for the theorem constants
        // that gets ignored.
        let ignored_game_inst_name = "<ignored>";
        out.push(theorem_consts.unit_declare(ignored_game_inst_name));

        let const_mapping = patterns::const_mapping::GameConstMappingFunction {
            theorem_name: &self.theorem.name,
            game_name,
            game_inst_name,
        };
        let const_mapping_call = const_mapping
            .call(&[theorem_consts
                .unit_global_const_name(ignored_game_inst_name)
                .into()])
            .unwrap();

        out.push(
            game_consts
                .unit_define(game_inst_name, const_mapping_call)
                .into(),
        );

        // the arguments of every oracle the package exposes
        for export in &game_inst.game().exports {
            let mut octx = gctx
                .exported_oracle_ctx_by_name(export.name())
                .expect("every export of the game points at an oracle");
            octx.set_renamed(export.alias());

            for (arg_name, arg_type) in &export.sig().args {
                out.push(declare_const(
                    octx.smt_arg_name(arg_name),
                    arg_type.clone().into(),
                ));
            }
        }

        out.extend(game_defs::build_returns(game_inst, None));

        // the counters are left arbitrary: the claim holds for every old randomness counter
        for (decl_ctr, constrain_ctr, _zero_ctr) in
            game_defs::build_rands(&self.sample_info, game_inst)
        {
            out.push(decl_ctr);
            out.push(constrain_ctr);
        }

        out
    }

    /// Declares the initial game state and fixes every state variable to the default value of its
    /// type.
    pub(crate) fn emit_initial_state_values(&self) -> Vec<SmtExpr> {
        game_defs::emit_game_initial_state_values(self.game_inst_ctx())
    }

    /// `(assert (not (<claim> <initial state>)))`
    pub(crate) fn emit_invariant_start_assert(&self, claim: &ResolvedClaim) -> SmtExpr {
        let initial_state = self
            .game_inst_ctx()
            .oracle_arg_game_state_pattern()
            .global_const_name(&self.game_inst_name, &GameStateOracleArgVariant::Initial);

        SmtAssert(SmtNot((claim.name(), initial_state))).into()
    }

    /// `(assert (not (=> (and <each invariant on the old state> (not <aborted>)) (<claim> <new state>))))`
    ///
    /// Each claim assumes every named invariant of the package on the old state. We only require the invariant to be preserved by calls that return normally: when an oracle
    /// aborts, the whole game aborts, so the state it leaves behind is never observed again.
    pub(crate) fn emit_oracle_claim_assert(
        &self,
        claim: &ResolvedClaim,
        oracle_name: &str,
    ) -> SmtExpr {
        let gctx = self.game_inst_ctx();
        let game_inst_name = &self.game_inst_name;

        let octx = gctx
            .exported_oracle_ctx_by_name(oracle_name)
            .expect("the oracle is exported by the game");

        let state = octx.oracle_arg_game_state_pattern();
        let old_state = state.old_global_const_name(game_inst_name);
        let new_state = state.new_global_const_name(game_inst_name, oracle_name.to_string());

        let is_abort = ReturnIsAbortConst {
            game_inst_name,
            pkg_inst_name: &self.pkg_inst_name,
            oracle_name,
            ty: octx.oracle_return_type(),
        };

        let mut precondition: Vec<SmtExpr> = self
            .invariant_claims()
            .iter()
            .map(|invariant| (invariant.name(), old_state.as_str()).into())
            .collect();
        precondition.push(SmtNot(is_abort.name()).into());
        let postcondition: SmtExpr = (claim.name(), new_state).into();
        let precondition = SmtAnd(precondition);

        SmtAssert(SmtNot(SmtImplies(precondition, postcondition))).into()
    }
}

#[cfg(test)]
mod tests {
    use crate::project::{DirectoryFiles, DirectoryProject, Project};

    use super::PackageInvariantContext;

    fn load(root: &str) -> DirectoryProject<'static> {
        let files = Box::leak(Box::new(
            DirectoryFiles::load(std::path::Path::new(root)).unwrap(),
        ));
        DirectoryProject::load(std::path::PathBuf::from(root), files).unwrap()
    }

    #[test]
    fn each_oracle_with_import_calls_has_one_record_with_a_field_for_each_site() {
        let project = load("test-projects/err-package-invariant-open-calls-differ");
        let ctx =
            PackageInvariantContext::new(project.get_package("Flag").unwrap(), &project).unwrap();
        let records: Vec<String> = ctx
            .emit_call_records()
            .iter()
            .map(|r| {
                r.to_string()
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ")
            })
            .collect();
        assert_eq!(records.len(), 1, "{records:?}");
        let record = &records[0];
        assert!(
            record.starts_with("(declare-datatype Flag-Twice-calls ((mk-Flag-Twice-calls"),
            "{record}"
        );
        let first = record.find("(Flag-Twice-calls-1 (Maybe").unwrap();
        let second = record.find("(Flag-Twice-calls-2 (Maybe").unwrap();
        assert!(first < second && !record.contains("calls-3"), "{record}");
    }

    #[test]
    fn an_oracle_without_import_calls_has_no_record() {
        let project = load("test-projects/test-package-invariant-imports");
        let ctx =
            PackageInvariantContext::new(project.get_package("Ctr").unwrap(), &project).unwrap();
        let records: Vec<String> = ctx
            .emit_call_records()
            .iter()
            .map(ToString::to_string)
            .collect();
        // Step and Get call an import, Peek does not
        assert_eq!(records.len(), 2, "{records:?}");
        assert!(records.iter().all(|r| !r.contains("Ctr-Peek-calls")));
    }

    /// `None` in the field of a call site aborts the oracle (the abort cascade).
    #[cfg(feature = "cvc5-lib")]
    #[test]
    fn an_import_that_aborts_aborts_the_oracle() {
        use crate::util::smtsolver::{
            cvc5lib::Cvc5LibBackend, SmtSolver, SmtSolverBackend, SmtSolverResponse,
        };
        use crate::writers::smt::{
            contexts::GenericOracleContext,
            exprs::SmtExpr,
            patterns::{theorem_constants::ConstantPattern, ReturnIsAbortConst},
        };

        let project = load("test-projects/test-package-invariant-import-aborts");
        let ctx =
            PackageInvariantContext::new(project.get_package("Ctr").unwrap(), &project).unwrap();
        let gctx = ctx.game_inst_ctx();
        let octx = gctx.exported_oracle_ctx_by_name("Step").unwrap();
        let calls = octx.smt_arg_name(super::open_calls::CALLS_ARG);
        let is_abort = ReturnIsAbortConst {
            game_inst_name: &ctx.game_inst_name,
            pkg_inst_name: &ctx.pkg_inst_name,
            oracle_name: "Step",
            ty: octx.oracle_return_type(),
        };

        let mut smt = ctx.emit_base_declarations();
        smt.extend(ctx.emit_call_records());
        smt.extend(ctx.emit_theorem_paramfuncs());
        smt.extend(ctx.emit_game_definitions());
        smt.extend(ctx.emit_constant_declarations());
        let field = format!("(Ctr-Step-calls-1 {calls})");
        let mut solver = Cvc5LibBackend::new(true, None).new_smtsolver().unwrap();
        for expr in smt {
            solver.write_smt(expr).unwrap();
        }
        solver
            .write_smt(SmtExpr::Atom(format!("(assert (is-mk-none {field}))")))
            .unwrap();
        solver
            .write_smt(SmtExpr::Atom(format!("(assert (not {}))", is_abort.name())))
            .unwrap();
        assert_eq!(solver.check_sat().unwrap(), SmtSolverResponse::Unsat);
    }

    #[test]
    fn the_package_check_has_one_claim_for_each_named_invariant() {
        let project = load("test-projects/test-package-invariant-imports");
        let ctx =
            PackageInvariantContext::new(project.get_package("Ctr").unwrap(), &project).unwrap();

        let names: Vec<String> = ctx
            .invariant_claims()
            .iter()
            .map(|claim| claim.name().to_string())
            .collect();
        assert_eq!(
            names,
            [
                "package-invariant!nonneg!Ctr!",
                "package-invariant!unseen!Ctr!"
            ]
        );
    }
}
