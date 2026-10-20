use std::fmt::Display;

use crate::{
    gamehops::equivalence::smtrewrite::SmtStatementKind,
    theorem::{
        BuiltInFact, ClaimKind, InvariantSide, RandomnessMappingInjectivityCheck, RandomnessType,
        ResolvedClaim, ResolvedDependency,
    },
    types::Type,
    writers::smt::{
        contexts::{game_defs, EquivalenceContext, GameInstanceContext, GenericOracleContext},
        declare::declare_const,
        exprs::{SmtAnd, SmtAssert, SmtEq2, SmtExpr, SmtImplies, SmtNot},
        names, patterns,
        patterns::{
            const_mapping::GameConstMappingFunction, functions::FunctionPattern,
            oracle_args::GameStateOracleArgPattern, oracle_args::OracleArgPattern,
            oracle_args::UnitOracleArgPattern, theorem_constants::ConstantPattern,
            ReturnIsAbortConst, SmtDefineFun,
        },
        sorts::Sort,
    },
};

impl RandomnessMappingInjectivityCheck {
    /// Emits the smt code that searches for a counterexample to injectivity of the randomness
    /// mapping relation on the given component.
    ///
    /// Injectivity on the left means that no two distinct left sampling
    /// points are related to the same right sampling point (and similarly for the right). We declare
    /// the three sampling points involved as constants, assert that both pairs are in the
    /// relation, and assert that the two points on `component` differ. A sat result is therefore a
    /// counterexample to injectivity, and unsat means the relation is injective on that component.
    ///
    /// The relation may also read the old game states, the oracle arguments and the theorem
    /// constants. Those are declared (and constrained) by the equivalence-wide smt code, so they
    /// stay free here and the check quantifies over them implicitly.
    pub(crate) fn emit_randomness_mapping_injectivity_check(
        self,
        oracle_name: &str,
    ) -> Vec<SmtExpr> {
        // the two sampling points on the component we check injectivity on
        const FIRST_ID: &str = "<injective-randmap-first-id>";
        const FIRST_CTR: &str = "<injective-randmap-first-ctr>";
        const SECOND_ID: &str = "<injective-randmap-second-id>";
        const SECOND_CTR: &str = "<injective-randmap-second-ctr>";
        // the sampling point on the other component that both are related to
        const SHARED_ID: &str = "<injective-randmap-shared-id>";
        const SHARED_CTR: &str = "<injective-randmap-shared-ctr>";

        let sample_id_sort = || Sort::Other("SampleId".to_string(), vec![]);

        let relation_call = |id: &str, ctr: &str| -> SmtExpr {
            let (id_left, id_right, ctr_left, ctr_right) = match self {
                Self::Left => (id, SHARED_ID, ctr, SHARED_CTR),
                Self::Right => (SHARED_ID, id, SHARED_CTR, ctr),
            };

            (
                format!("randomness-mapping-{oracle_name}"),
                id_left,
                id_right,
                ctr_left,
                ctr_right,
            )
                .into()
        };

        vec![
            declare_const(FIRST_ID, sample_id_sort()),
            declare_const(FIRST_CTR, Sort::Int),
            declare_const(SECOND_ID, sample_id_sort()),
            declare_const(SECOND_CTR, Sort::Int),
            declare_const(SHARED_ID, sample_id_sort()),
            declare_const(SHARED_CTR, Sort::Int),
            // R(first_id, shared_id, first_ctr, shared_ctr)
            SmtAssert(relation_call(FIRST_ID, FIRST_CTR)).into(),
            // R(second_id, shared_id, second_ctr, shared_ctr)
            SmtAssert(relation_call(SECOND_ID, SECOND_CTR)).into(),
            // (first_id, first_ctr) != (second_id, second_ctr)
            SmtAssert(SmtNot(SmtAnd(vec![
                SmtEq2 {
                    lhs: FIRST_ID,
                    rhs: SECOND_ID,
                }
                .into(),
                SmtEq2 {
                    lhs: FIRST_CTR,
                    rhs: SECOND_CTR,
                }
                .into(),
            ])))
            .into(),
        ]
    }
}

pub(crate) const RANDOMNESS_MAPPING_CONDITION_NAME: &str = "<randomness-mapping>";

#[derive(Clone, Debug)]
pub(crate) struct RandomnessMappingEntry {
    /// Index of the left sampling in its game instance's `SampleInfo::positions`.
    pub(crate) sample_left: usize,
    /// Likewise for the right sampling.
    pub(crate) sample_right: usize,
    pub(crate) sample_id_left: SmtExpr,
    pub(crate) sample_id_right: SmtExpr,
    pub(crate) offset_left: usize,
    pub(crate) offset_right: usize,
    // the sampling type shared by both sides (guaranteed identical by `types_match`), used to
    // pick the concrete `__sample-rand-*` functions to compare directly.
    pub(crate) ty: Type,
}

impl Display for RandomnessMappingEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "left id: {}, right id: {}, left offset: {}, right offset: {}, ty: {:?}",
            self.sample_id_left, self.sample_id_right, self.offset_left, self.offset_right, self.ty
        )
    }
}

impl<'a> EquivalenceContext<'a> {
    pub(crate) fn emit_invariant(&self) -> Vec<SmtExpr> {
        self.invariants
            .iter()
            .chain(self.left_invariants.iter())
            .chain(self.right_invariants.iter())
            .map(|stmt| stmt.expr.clone())
            .collect()
    }

    pub(crate) fn emit_initial_state_values(&self) -> Vec<SmtExpr> {
        let mut out = Vec::new();

        out.extend(game_defs::emit_game_initial_state_values(
            self.left_game_inst_ctx(),
        ));
        out.extend(game_defs::emit_game_initial_state_values(
            self.right_game_inst_ctx(),
        ));

        out
    }

    pub(crate) fn emit_invariant_start_assert(&self) -> SmtExpr {
        let state_left = self.left_game_inst_ctx().oracle_arg_game_state_pattern();
        let state_right = self.right_game_inst_ctx().oracle_arg_game_state_pattern();

        SmtAssert(SmtNot((
            "invariant",
            state_left.global_const_name(
                self.equivalence.left_name(),
                &patterns::oracle_args::GameStateOracleArgVariant::Initial,
            ),
            state_right.global_const_name(
                self.equivalence.right_name(),
                &patterns::oracle_args::GameStateOracleArgVariant::Initial,
            ),
        )))
        .into()
    }

    pub(crate) fn emit_game_or_package_invariant_start_assert(
        &self,
        claim: &ResolvedClaim,
    ) -> SmtExpr {
        let gctx = match claim.kind().invariant_side() {
            Some(InvariantSide::Left) => self.left_game_inst_ctx(),
            Some(InvariantSide::Right) => self.right_game_inst_ctx(),
            None => unreachable!("only package and game invariant claims have a start assert"),
        };
        let game_inst_name = gctx.game_inst_name();
        let state = gctx.oracle_arg_game_state_pattern();
        let initial_state = state.global_const_name(
            game_inst_name,
            &patterns::oracle_args::GameStateOracleArgVariant::Initial,
        );
        SmtAssert(SmtNot((claim.name(), initial_state.clone()))).into()
    }

    /// The claim's assumptions (each an SMT *term*, not an assert) and its goal term.
    ///
    /// `emit_oracle_claim_assert` combines them into the single refutation
    /// `(assert (not (=> (and <deps>) <goal>)))` that `prove` fires one `check-sat` on.
    /// The debugger instead asserts the assumptions positively and up front (via
    /// [`emit_claim_assumptions`](Self::emit_claim_assumptions)) so they constrain the
    /// branch-reachability queries it makes while walking the execution tree, and only adds
    /// the negated goal (via [`emit_claim_goal_negated`](Self::emit_claim_goal_negated)) at a
    /// terminal pair. `assert(d1) … assert(dn)` plus `assert(not goal)` is equisatisfiable
    /// with the single combined refutation.
    pub(crate) fn claim_assumptions_and_goal(
        &self,
        claim: &ResolvedClaim,
        oracle_name: &str,
    ) -> (Vec<SmtExpr>, SmtExpr) {
        let (mut deps, own, goal) = self.claim_assumption_parts(claim, oracle_name);
        deps.extend(own);
        (deps, goal)
    }

    /// [`claim_assumptions_and_goal`](Self::claim_assumptions_and_goal), with the assumptions
    /// split by scope (story 19): what every claim of the oracle shares (the randomness-mapping
    /// condition and the invariants on the old states), then the claim's own declared
    /// dependencies, then the goal.
    pub(crate) fn claim_assumption_parts(
        &self,
        claim: &ResolvedClaim,
        oracle_name: &str,
    ) -> (Vec<SmtExpr>, Vec<SmtExpr>, SmtExpr) {
        let gctx_left = self.left_game_inst_ctx();
        let gctx_right = self.right_game_inst_ctx();

        let octx_left = gctx_left.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let octx_right = gctx_right.exported_oracle_ctx_by_name(oracle_name).unwrap();

        let state_left = octx_left.oracle_arg_game_state_pattern();
        let state_right = octx_right.oracle_arg_game_state_pattern();

        let game_inst_name_left = self.equivalence.left_name();
        let game_inst_name_right = self.equivalence.right_name();

        let game_name_left = gctx_left.game().name();
        let game_name_right = gctx_right.game().name();

        let game_params_left = &gctx_left.game_inst().consts;
        let game_params_right = &gctx_right.game_inst().consts;

        let pkg_name_left = octx_left.pkg_inst_ctx().pkg_name();
        let pkg_name_right = octx_right.pkg_inst_ctx().pkg_name();

        let pkg_params_left = &octx_left.pkg_inst_ctx().pkg_inst().params;
        let pkg_params_right = &octx_right.pkg_inst_ctx().pkg_inst().params;

        let args: Vec<_> = self
            .oracle_sig_by_exported_name(oracle_name)
            .unwrap()
            .args
            .iter()
            .map(|(arg_name, arg_type)| patterns::OracleArgs {
                oracle_name,
                game_name: game_name_left, // left/right doesn't matter as both exist and are asserted to be equal
                arg_name,
                arg_type,
            })
            .collect();

        // find the package instance which is marked as exporting
        // the oracle of this name, both left and right.
        let left_return = patterns::ReturnConst {
            game_inst_name: game_inst_name_left,
            game_name: game_name_left,
            game_params: game_params_left,
            pkg_name: pkg_name_left,
            pkg_params: pkg_params_left,
            oracle_name,
            oracle_import_name: oracle_name,
        };

        let right_return = patterns::ReturnConst {
            game_inst_name: game_inst_name_right,
            game_name: game_name_right,
            game_params: game_params_right,
            pkg_name: pkg_name_right,
            pkg_params: pkg_params_right,
            oracle_name,
            oracle_import_name: oracle_name,
        };

        // this helper builds an smt expression that calls the
        // function with the given name with the old states,
        // return values and the respective arguments.
        // We expect that function to return a boolean, which makes
        // it a relation.
        let build_lemma_call = |name: &str| {
            let call_args: Vec<SmtExpr> = vec![
                state_left.old_global_const_name(game_inst_name_left).into(),
                state_right
                    .old_global_const_name(game_inst_name_right)
                    .into(),
                left_return.name().into(),
                right_return.name().into(),
            ]
            .into_iter()
            .chain(args.into_iter().map(|arg| arg.name().into()))
            .collect();

            let relation = self.relation_pattern(name, oracle_name);
            relation.call(&call_args).unwrap()
        };

        let build_relation_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_left.new_global_const_name(game_inst_name_left, oracle_name.to_string()),
                &state_right.new_global_const_name(game_inst_name_right, oracle_name.to_string()),
            )
                .into()
        };

        let build_invariant_old_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_left.old_global_const_name(game_inst_name_left),
                &state_right.old_global_const_name(game_inst_name_right),
            )
                .into()
        };
        let build_left_invariant_old_call = |name: &str| -> SmtExpr {
            (name, &state_left.old_global_const_name(game_inst_name_left)).into()
        };
        let build_right_invariant_old_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_right.old_global_const_name(game_inst_name_right),
            )
                .into()
        };

        let build_left_invariant_new_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_left.new_global_const_name(game_inst_name_left, oracle_name.to_string()),
            )
                .into()
        };
        let build_right_invariant_new_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_right.new_global_const_name(game_inst_name_right, oracle_name.to_string()),
            )
                .into()
        };

        // a call of the fact `name` on the new states, by the kind of its declaration
        let build_new_call = |name: &str, kind: ClaimKind| -> SmtExpr {
            match kind {
                ClaimKind::BuiltIn(_) | ClaimKind::ProjectLemma => build_lemma_call.clone()(name),
                ClaimKind::StateRelation => build_relation_call(name),
                ClaimKind::PackageInvariant { side } | ClaimKind::GameInvariant { side } => {
                    match side {
                        InvariantSide::Left => build_left_invariant_new_call(name),
                        InvariantSide::Right => build_right_invariant_new_call(name),
                    }
                }
            }
        };

        let dep_calls: Vec<_> = claim
            .dependencies()
            .iter()
            .map(|dep: &ResolvedDependency| build_new_call(dep.name(), dep.kind()))
            .collect();

        let postcond_call = build_new_call(claim.name(), claim.kind());

        let mut dependencies_code: Vec<SmtExpr> = vec![
            RANDOMNESS_MAPPING_CONDITION_NAME.into(),
            build_invariant_old_call("invariant"),
        ];

        dependencies_code.extend(
            self.left_invariants
                .iter()
                .filter_map(|stmt| match stmt.kind {
                    SmtStatementKind::GameInvariant { .. }
                    | SmtStatementKind::PackageInvariant { .. } => {
                        Some(build_left_invariant_old_call(&stmt.kind.name()))
                    }
                    _ => None,
                }),
        );
        dependencies_code.extend(
            self.right_invariants
                .iter()
                .filter_map(|stmt| match stmt.kind {
                    SmtStatementKind::GameInvariant { .. }
                    | SmtStatementKind::PackageInvariant { .. } => {
                        Some(build_right_invariant_old_call(&stmt.kind.name()))
                    }
                    _ => None,
                }),
        );

        (dependencies_code, dep_calls, postcond_call)
    }

    /// The single-refutation claim assertion `prove` uses:
    /// `(assert (not (=> (and <deps>) <goal>)))`.
    pub(crate) fn emit_oracle_claim_assert(
        &self,
        claim: &ResolvedClaim,
        oracle_name: &str,
    ) -> SmtExpr {
        let (deps, goal) = self.claim_assumptions_and_goal(claim, oracle_name);
        crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(SmtAnd(deps), goal))).into()
    }

    /// One `(assert <dep>)` per assumption, in the same order
    /// [`claim_assumptions_and_goal`](Self::claim_assumptions_and_goal) returns them. The
    /// debugger asserts these up front so they constrain intermediate reachability queries.
    ///
    /// `emit_claim_assumptions(..)` followed by `emit_claim_goal_negated(..)` is
    /// equisatisfiable with the single `(assert (not (=> (and d1..dn) goal)))` that
    /// [`emit_oracle_claim_assert`](Self::emit_oracle_claim_assert) produces.
    // Consumed by `domino debug` (story 06); no non-test caller on this branch yet.
    #[allow(dead_code)]
    pub(crate) fn emit_claim_assumptions(
        &self,
        claim: &ResolvedClaim,
        oracle_name: &str,
    ) -> Vec<SmtExpr> {
        let (deps, _goal) = self.claim_assumptions_and_goal(claim, oracle_name);
        deps.into_iter()
            .map(|dep| crate::writers::smt::exprs::SmtAssert(dep).into())
            .collect()
    }

    /// The assumptions every claim of `oracle_name` shares, asserted positively (story 19):
    /// the randomness-mapping condition and the invariants on the old states.
    pub(crate) fn emit_shared_assumptions(&self, oracle_name: &str) -> Vec<SmtExpr> {
        // Any claim will do: the shared part does not depend on it.
        let claim = ResolvedClaim {
            name: "invariant".to_string(),
            kind: ClaimKind::StateRelation,
            dependencies: Vec::new(),
            admitted: false,
        };
        let (shared, _own, _goal) = self.claim_assumption_parts(&claim, oracle_name);
        shared
            .into_iter()
            .map(|dep| crate::writers::smt::exprs::SmtAssert(dep).into())
            .collect()
    }

    /// `claim`'s own declared dependencies (`no-abort`, project lemmas, …), asserted positively
    /// — what [`emit_claim_assumptions`](Self::emit_claim_assumptions) has beyond
    /// [`emit_shared_assumptions`](Self::emit_shared_assumptions). Story 19 asserts these at the
    /// terminal pair in an all-claim run.
    pub(crate) fn emit_claim_own_assumptions(
        &self,
        claim: &ResolvedClaim,
        oracle_name: &str,
    ) -> Vec<SmtExpr> {
        let (_shared, own, _goal) = self.claim_assumption_parts(claim, oracle_name);
        own.into_iter()
            .map(|dep| crate::writers::smt::exprs::SmtAssert(dep).into())
            .collect()
    }

    /// `(assert (not <goal>))` — the refutation the debugger checks at a terminal pair,
    /// once the assumptions from [`emit_claim_assumptions`](Self::emit_claim_assumptions)
    /// are already on the stack.
    // Consumed by `domino debug` (story 06); no non-test caller on this branch yet.
    #[allow(dead_code)]
    pub(crate) fn emit_claim_goal_negated(
        &self,
        claim: &ResolvedClaim,
        oracle_name: &str,
    ) -> SmtExpr {
        let (_deps, goal) = self.claim_assumptions_and_goal(claim, oracle_name);
        crate::writers::smt::exprs::SmtAssert(SmtNot(goal)).into()
    }

    /// One claim for each named package and game invariant of both game instances, each under
    /// `no-abort`. The side tree (symbolic-execution story 25) checks the left ones until story
    /// 77; an equivalence checks only [`generate_game_invariant_claims`](Self::generate_game_invariant_claims).
    pub(crate) fn generate_game_or_package_invariant_claims(&self) -> Vec<ResolvedClaim> {
        fn invariant_claims(
            stmts: &[crate::gamehops::equivalence::smtrewrite::SmtStmt],
            side: InvariantSide,
        ) -> Vec<ResolvedClaim> {
            stmts
                .iter()
                .filter_map(|stmt| {
                    let kind = match stmt.kind {
                        SmtStatementKind::PackageInvariant { .. } => {
                            ClaimKind::PackageInvariant { side }
                        }
                        SmtStatementKind::GameInvariant { .. } => ClaimKind::GameInvariant { side },
                        _ => return None,
                    };
                    Some(ResolvedClaim {
                        admitted: false,
                        dependencies: vec![ResolvedDependency {
                            name: BuiltInFact::NoAbort.name().to_string(),
                            kind: ClaimKind::BuiltIn(BuiltInFact::NoAbort),
                        }],
                        kind,
                        name: stmt.kind.name(),
                    })
                })
                .collect()
        }

        let mut claims = invariant_claims(&self.left_invariants, InvariantSide::Left);
        claims.extend(invariant_claims(
            &self.right_invariants,
            InvariantSide::Right,
        ));
        claims
    }

    /// The game-invariant claims of this equivalence: what `prove` and the debugger's claim
    /// sets check. Package invariants are not claims of an equivalence (story 74): `domino prove`
    /// checks each package once on its own, and the equivalence only assumes them on the old
    /// states.
    pub(crate) fn generate_game_invariant_claims(&self) -> Vec<ResolvedClaim> {
        self.generate_game_or_package_invariant_claims()
            .into_iter()
            .filter(|claim| matches!(claim.kind(), ClaimKind::GameInvariant { .. }))
            .collect()
    }

    /// The base frame's assumption of one-sided execution (symbolic-execution story 25): each
    /// package and game invariant of the **left** game instance on its old state, asserted. The
    /// right side is not read.
    pub(crate) fn emit_left_side_invariants_old(&self, oracle_name: &str) -> Vec<SmtExpr> {
        let gctx = self.left_game_inst_ctx();
        let octx = gctx.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let old_state = octx
            .oracle_arg_game_state_pattern()
            .old_global_const_name(gctx.game_inst_name());
        self.generate_game_or_package_invariant_claims()
            .into_iter()
            .filter(|claim| claim.kind().invariant_side() == Some(InvariantSide::Left))
            .map(|claim| SmtAssert::<SmtExpr>((claim.name.as_str(), &old_state).into()).into())
            .collect()
    }

    pub(crate) fn randomness_mapping_candidates(
        &self,
        oracle_name: &str,
    ) -> Vec<RandomnessMappingEntry> {
        let left_export = self
            .left_game_inst_ctx()
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)
            .unwrap_or_else(|| unreachable!("oracle resolution should have caught this: could not find left export {oracle_name}"));
        let right_export = self
            .right_game_inst_ctx()
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)
            .unwrap_or_else(|| unreachable!("oracle resolution should have caught this: could not find right export {oracle_name}"));

        let left_offsets = self
            .max_offsets_left()
            .get(left_export)
            .unwrap_or_else(|| unreachable!("sample_max_counter_extractor should have filled this: could not find max offsets for left export {oracle_name}"));
        let right_offsets = self
            .max_offsets_right()
            .get(right_export)
            .unwrap_or_else(|| unreachable!("sample_max_counter_extractor should have filled this: could not find max offsets for right export {oracle_name}"));

        let mut left_entries: Vec<_> = left_offsets
            .iter()
            .flat_map(|(position, max_offset)| {
                (0..*max_offset)
                    .map(move |offset| (position, SmtExpr::from(position), offset, &position.ty))
            })
            .collect();
        let mut right_entries: Vec<_> = right_offsets
            .iter()
            .flat_map(|(position, max_offset)| {
                (0..*max_offset)
                    .map(move |offset| (position, SmtExpr::from(position), offset, &position.ty))
            })
            .collect();

        left_entries.sort_by_key(|(position, _, offset, _)| (position.sample_id, *offset));
        right_entries.sort_by_key(|(position, _, offset, _)| (position.sample_id, *offset));

        left_entries
            .iter()
            .flat_map(|(left_position, sample_id_left, offset_left, ty_left)| {
                right_entries
                    .iter()
                    .filter(move |(_, _, _, ty_right)| ty_left.types_match(ty_right))
                    .map(move |(right_position, sample_id_right, offset_right, _)| {
                        RandomnessMappingEntry {
                            sample_left: left_position.sample_id,
                            sample_right: right_position.sample_id,
                            sample_id_left: sample_id_left.clone(),
                            sample_id_right: sample_id_right.clone(),
                            offset_left: *offset_left,
                            offset_right: *offset_right,
                            // `types_match` guarantees left and right resolve to the same SMT
                            // sort, so either type can be used to pick the `__sample-rand-*`
                            // functions for both sides.
                            ty: (*ty_left).clone(),
                        }
                    })
            })
            .collect()
    }

    /// The condition `randomness-mapping-<O>` states for one candidate: that the
    /// mapping pairs the left draw with the right one. It is a term over the
    /// global constants, so it may depend on the state and the oracle's
    /// arguments; the debugger asks the solver, it never reads it.
    pub(crate) fn randomness_mapping_premise(
        &self,
        oracle_name: &str,
        entry: &RandomnessMappingEntry,
    ) -> SmtExpr {
        (
            format!("randomness-mapping-{oracle_name}"),
            entry.sample_id_left.clone(),
            entry.sample_id_right.clone(),
            entry.offset_left,
            entry.offset_right,
        )
            .into()
    }

    /// The names of the equivalence's `define-state-relation`s, in file order.
    /// These are exactly the relations the EasyCrypt `inv` operator conjoins
    /// (`writers::easycrypt::invariant`), each defined here as an SMT function
    /// of the two game states.
    pub(crate) fn state_relation_names(&self) -> Vec<String> {
        self.invariants
            .iter()
            .filter(|stmt| matches!(stmt.kind, SmtStatementKind::StateRelation { .. }))
            .filter_map(|stmt| match &stmt.expr {
                SmtExpr::List(items) => match items.as_slice() {
                    [SmtExpr::Atom(kw), SmtExpr::Atom(name), ..] if kw == "define-fun" => {
                        Some(name.clone())
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    pub(crate) fn emit_randomness_mapping_condition(&self, oracle_name: &str) -> Vec<SmtExpr> {
        let left_game_inst_name = self.left_game_inst_ctx().game_inst().name();
        let right_game_inst_name = self.right_game_inst_ctx().game_inst().name();

        let conjuncts: Vec<SmtExpr> = self
            .randomness_mapping_candidates(oracle_name)
            .iter()
            .map(|entry| {
                let left_rand_fn = names::fn_sample_rand_name(left_game_inst_name, &entry.ty);
                let right_rand_fn = names::fn_sample_rand_name(right_game_inst_name, &entry.ty);

                SmtImplies(
                    self.randomness_mapping_premise(oracle_name, entry),
                    SmtEq2 {
                        lhs: (
                            left_rand_fn,
                            entry.sample_id_left.clone(),
                            entry.offset_left,
                        ),
                        rhs: (
                            right_rand_fn,
                            entry.sample_id_right.clone(),
                            entry.offset_right,
                        ),
                    },
                )
                .into()
            })
            .collect();

        let rhs: SmtExpr = if conjuncts.is_empty() {
            true.into()
        } else {
            SmtAnd(conjuncts).into()
        };

        vec![
            declare_const(RANDOMNESS_MAPPING_CONDITION_NAME, Type::boolean().into()),
            SmtAssert(SmtEq2 {
                lhs: RANDOMNESS_MAPPING_CONDITION_NAME,
                rhs,
            })
            .into(),
        ]
    }

    pub(crate) fn emit_game_definitions(&'a self) -> Vec<SmtExpr> {
        game_defs::emit_game_definitions(self.theorem, &self.game_instances())
    }

    /// The two game instances of this equivalence, paired with their sampling information.
    fn game_instances(&'a self) -> Vec<game_defs::GameInstanceWithSampleInfo<'a>> {
        vec![
            (self.left_game_inst_ctx(), self.sample_info_left()),
            (self.right_game_inst_ctx(), self.sample_info_right()),
        ]
    }

    pub(crate) fn emit_base_declarations(&self) -> Vec<SmtExpr> {
        game_defs::emit_base_declarations(&self.types())
    }

    pub(crate) fn emit_auto_randomness(&self, oracle_name: &str) -> Vec<SmtExpr> {
        match self.equivalence.randomness_by_oracle_name(oracle_name) {
            RandomnessType::Custom => {
                vec![]
            }
            RandomnessType::Simple => {
                let define = SmtDefineFun {
                    is_rec: false,
                    sort: Type::boolean().into(),
                    name: format!("randomness-mapping-{oracle_name}"),
                    body: SmtAnd(vec![
                        SmtEq2 {
                            lhs: "sample-id-0",
                            rhs: "sample-id-1",
                        }
                        .into(),
                        SmtEq2 {
                            lhs: "offset-0",
                            rhs: "0",
                        }
                        .into(),
                        SmtEq2 {
                            lhs: "offset-1",
                            rhs: "0",
                        }
                        .into(),
                    ]),
                    args: vec![
                        (
                            "sample-id-0".to_string(),
                            Sort::Other("SampleId".to_string(), vec![]),
                        ),
                        (
                            "sample-id-1".to_string(),
                            Sort::Other("SampleId".to_string(), vec![]),
                        ),
                        ("offset-0".to_string(), Type::integer().into()),
                        ("offset-1".to_string(), Type::integer().into()),
                    ],
                };
                vec![define.into()]
            }
            RandomnessType::None => {
                let define = SmtDefineFun {
                    is_rec: false,
                    sort: Type::boolean().into(),
                    name: format!("randomness-mapping-{oracle_name}"),
                    body: "false",
                    args: vec![
                        (
                            "sample-id-0".to_string(),
                            Sort::Other("SampleId".to_string(), vec![]),
                        ),
                        (
                            "sample-id-1".to_string(),
                            Sort::Other("SampleId".to_string(), vec![]),
                        ),
                        ("offset-0".to_string(), Type::integer().into()),
                        ("offset-1".to_string(), Type::integer().into()),
                    ],
                };
                vec![define.into()]
            }
        }
    }

    pub(crate) fn emit_theorem_paramfuncs(&'a self) -> Vec<SmtExpr> {
        game_defs::emit_theorem_paramfuncs(self.theorem)
    }

    pub(crate) fn emit_return_value_helpers(&self, oracle_name: &str) -> Vec<SmtExpr> {
        let left_gctx = self.left_game_inst_ctx();
        let left_octx = left_gctx.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let left_pctx = left_octx.pkg_inst_ctx();

        let right_gctx = self.right_game_inst_ctx();
        let right_octx = right_gctx.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let right_pctx = right_octx.pkg_inst_ctx();

        let left_return_value = left_octx.return_value_const_pattern(oracle_name);
        let right_return_value = right_octx.return_value_const_pattern(oracle_name);

        let left_is_abort = ReturnIsAbortConst {
            game_inst_name: left_gctx.game_inst().name(),
            pkg_inst_name: left_pctx.pkg_inst_name(),
            oracle_name,
            ty: left_octx.oracle_return_type(),
        };

        let right_is_abort = ReturnIsAbortConst {
            game_inst_name: right_gctx.game_inst().name(),
            pkg_inst_name: right_pctx.pkg_inst_name(),
            oracle_name,
            ty: right_octx.oracle_return_type(),
        };

        let consts: [(_, SmtExpr); 3] = [
            (
                "<equal-aborts>",
                SmtEq2 {
                    lhs: left_is_abort.value(left_return_value.name()),
                    rhs: right_is_abort.value(right_return_value.name()),
                }
                .into(),
            ),
            (
                "<no-aborts>",
                SmtAnd(vec![
                    SmtNot(left_is_abort.value(left_return_value.name())).into(),
                    SmtNot(right_is_abort.value(right_return_value.name())).into(),
                ])
                .into(),
            ),
            (
                "<same-outputs>",
                SmtEq2 {
                    lhs: left_return_value.name(),
                    rhs: right_return_value.name(),
                }
                .into(),
            ),
        ];

        consts
            .into_iter()
            .flat_map(|(name, value)| {
                let declare = declare_const(name, Sort::Bool);
                let constrain = SmtAssert(SmtEq2 {
                    lhs: name,
                    rhs: value,
                });

                [declare, constrain.into()]
            })
            .chain(std::iter::once(
                self.relation_definition_equal_aborts(oracle_name).into(),
            ))
            .chain(std::iter::once(
                self.relation_definition_left_no_abort(oracle_name).into(),
            ))
            .chain(std::iter::once(
                self.relation_definition_right_no_abort(oracle_name).into(),
            ))
            .chain(std::iter::once(
                self.relation_definition_no_abort(oracle_name).into(),
            ))
            .chain(std::iter::once(
                self.relation_definition_same_output(oracle_name).into(),
            ))
            .collect()

        // out
    }

    /// Declares (and mostly constrains) the base constants for the equivalence check.
    ///
    /// `skip_return_constraint_for` is threaded to [`build_returns`]: with `Some(o)` the
    /// `<return-o>` constant is declared but left unconstrained on both sides, for the
    /// debugger to constrain from its per-path DSA encoding. `prove` passes `None`.
    pub(crate) fn emit_constant_declarations(
        &self,
        skip_return_constraint_for: Option<&str>,
    ) -> Vec<SmtExpr> {
        /*
         *
         * things being declared here:
         * - nonsplit oracle args
         * - for $game_inst in left, right
         *   - old game state $game_inst
         *   - new game state $game_inst
         *   - randomness counters $game_inst
         *   - randomness values $game_inst
         *   - for oracle in game.non-split-exports
         *     - return $game_inst $oracle
         *   - for oracle in game.split-exports
         *     - partial return $game_inst $oracle
         *     - split oracle args
         *
         * things being constrained here:
         * - for $game_inst in left, right
         *   - rand_ctr_$i = get_rand(game_state, $i)
         *   - rand_val_$i = rand_$game_inst($i, rand_ctr_$i)
         *   - for $oracle in $game_inst.non-split-exports
         *     - return = $oracle(state, args...)
         *     - new_game_state_$game_inst = get-state(return)
         *       - wait, maybe this should only be in the procondition of the claim statements
         *   - for $oracle in $game_inst.non-split-exports
         *     - partial return = $oracle(state, args...)
         *
         * Thoughts on the design of the next iteration of this:
         *
         * What can go wrong here?
         *
         *   Underconstraining
         *
         *     The solver would give us a sat where we expect an unsat and we can
         *     use the model to see which constraint is missing. Until that is done, we can't prove
         *     anything but that is not that big of a deal. So I guess this is an easily debuggable
         *     completeness problem.
         *
         *   Overconstraining
         *
         *     We might add too many constraints, which would lead to the solver
         *     reporting unsat where it should return sat. This would break soundness, in ways that
         *     are not easily debuggable.
         *
         *   I feel like soundness is more important than completeness!
         *
         * What can we do to prevent that? (TODO)
         *
         *   Testing
         *
         *     I suppose the best way to guard against this is to have test cases with theorems
         *     that are expected to not go through and make sure that this is actually the case.
         *
         *   Clear Documentation/Spec
         *
         *     Making explicit the model we have of the system helps both
         *     with catching logic bugs (because in order to vet the logic you can read the docs)
         *     and implementation bugs (because you can compare the implementation against the spec).
         *
         * When do we apply the constraints?
         *
         *   Option A: Immediately after declaring
         *
         *     This doesn't work for e.g. the "new state", as that would be constrained in
         *     contradictory ways. My current heuristic is that if the value is the output of a
         *     function and there are several potential functions that it could be the output of,
         *     then it won't work.
         *
         *       Can we maybe avoid that issue by not "overloading" constants? Use constants as
         *       the output of one particular thing? What are other instances of constants that are
         *       constrained differently depending on the call?
         *
         *         Other instances: I was going to say PartialReturn, but not only by "real" oracle
         *         but also by split oracle, but I don' think that is true since because of the
         *         dispatch function. So maybe it's just Return and PartialReturn, by "real" oracle?
         *
         *         We could avoid that by not having a single "new state" constant, but one per
         *         oracle. That might be a tad inconvenient though? Or we just bind the convenient
         *         names using let, either in the lemma/relation/invariant or in the glue code
         *         calling it. This would mean we don't even need the constants and don't need to
         *         constrain them. Sounds like there is less chance of confusion, too!
         *
         *   Option B: First declare all constants, then constrain
         *
         *     Seems difficult to keep track of the constraints we still need to do.
         *
         * So to me it seems the best way is to
         *
         * 1.  declare foundational constants ("old state", "function arguments")
         * 2.  declare constants that conceptually are outputs of a known function taking
         *     foundational constants ("return per oracle") and immediately constrain them
         * 3.  only bind convenience values in (let ..) blocks close to the code using them.
         *     This can be done manually in the user code, or in the glue code calling the user
         *     code.
         *
         *       I think there is a discussion to be had here, though. If we go with the let-bind
         *       approache, we can't make the randomness mapping a bunch of asserts. It needs to be
         *       an expression that evaluates to a bool. Is the user fine with that?
         *
         *       I think this can affect model readability (for a human) in one of two ways:
         *
         *         Possible Impact A: There a fewer global constants, and all the values are in the
         *         specific part of the gamestate. It is more tidy and it is easy to find what you
         *         are looking for.
         *
         *         Possibe Impact B: Instead of having a global constant rand-Real-1-4 as a constant
         *         in the model, you have to sift through the game state structs to find the
         *         correct one to see the value, which makes it more difficult.
         *
         *         I wonder which of these would be stronger, and believe it depends on the habits and
         *         preferences of the user.
         *
         * Which leaves us to specify (and give reasons for) our list of constants and constraints.
         * Afterwards, we also make a list of constants constraints we chose not to include here.
         *
         *   Foundational Constants: Old Gamestate, Old Intermediate State and Arguments
         *
         *     These are only used as inputs to the oracle functions. There is nothing we can tie
         *     them to, we can only constrain them in lemmas, etc.
         *
         *   Function Outputs: Return, PartialReturn
         *
         *     These can be directly computed from the above. They should simply be constrained.
         *
         *   Convenience Values: New Gamestate, New Intermediate State, IsAbort, Return Value,
         *                       Randomness Counters, Random Values
         *
         *     These fall in two categories:
         *
         *     1.  Values where a convenient name would not be globally unique (e.g. new state, is abort)
         *
         *           Here I think using (let ..) bindings really is the best way to handle the
         *           ambiguity.
         *
         *     2.  Values that have unique names, but are rarely needed and are just copied from the
         *         gamestate (e.g. randomness)
         *
         *           Here I am not sure - From a "purity" standpoint it feels nice to me, but I see how
         *           that is not a very strong argument, so we may just declare and constrain them globally.
         *
         */

        let left_game_inst_name = self.equivalence.left_name();
        let right_game_inst_name = self.equivalence.right_name();

        let left = self
            .theorem
            .find_game_instance(self.equivalence.left_name())
            .unwrap();
        let right = self
            .theorem
            .find_game_instance(self.equivalence.right_name())
            .unwrap();

        let gctx_left = GameInstanceContext::new(left);
        let gctx_right = GameInstanceContext::new(right);

        let left_game_name = &gctx_left.game().name;
        let right_game_name = &gctx_right.game().name;

        let mut out = Vec::new();

        /////// state constants

        let game_state_left = gctx_left.oracle_arg_game_state_pattern();
        let game_state_right = gctx_right.oracle_arg_game_state_pattern();

        // the new ones are declared in the declare-then-assert loop below

        out.push(game_state_left.declare_old(left_game_inst_name));
        //out.push(game_state_left.declare_new(left_game_inst_name));
        out.push(game_state_right.declare_old(right_game_inst_name));
        //out.push(game_state_right.declare_new(right_game_inst_name));

        ////// consts constants

        let game_consts_left = patterns::oracle_args::GameConstsPattern {
            game_name: left_game_name,
        };
        let game_consts_right = patterns::oracle_args::GameConstsPattern {
            game_name: right_game_name,
        };

        let theorem_consts = patterns::oracle_args::TheoremConstsPattern {
            theorem_name: &self.theorem().name,
        };

        // the interface requires us to pass in a game instance name, but for the theorem constants
        // that gets ignored. We use a name here that would for sure cause trouble if it were
        // included.
        let hack_this_should_be_ignored = "this is being ignored anyway, but let's make sure it fails if it gets included )))))))))))))";

        out.push(theorem_consts.unit_declare(hack_this_should_be_ignored));

        let theorem_game_const_mapping_left = GameConstMappingFunction {
            theorem_name: &self.theorem().name,
            game_name: left_game_name,
            game_inst_name: left_game_inst_name,
        };

        let theorem_game_const_mapping_right = GameConstMappingFunction {
            theorem_name: &self.theorem().name,
            game_name: right_game_name,
            game_inst_name: right_game_inst_name,
        };

        let theorem_game_const_mapping_call_left =
            theorem_game_const_mapping_left.call(&[theorem_consts
                .unit_global_const_name(hack_this_should_be_ignored)
                .into()]);
        let theorem_game_const_mapping_call_right =
            theorem_game_const_mapping_right.call(&[theorem_consts
                .unit_global_const_name(hack_this_should_be_ignored)
                .into()]);

        out.push(
            game_consts_left
                .unit_define(
                    left_game_inst_name,
                    theorem_game_const_mapping_call_left.unwrap(),
                )
                .into(),
        );
        out.push(
            game_consts_right
                .unit_define(
                    right_game_inst_name,
                    theorem_game_const_mapping_call_right.unwrap(),
                )
                .into(),
        );

        /////// arguments for non-split and split oracles

        for left_export in &left.game().exports {
            let right_export = right
                .game
                .exports
                .iter()
                .find(|exp| exp.name() == left_export.name())
                .unwrap();
            if let (Some(mut left_orcl_ctx), Some(mut right_orcl_ctx)) = (
                gctx_left.exported_oracle_ctx_by_name(left_export.name()),
                gctx_right.exported_oracle_ctx_by_name(right_export.name()),
            ) {
                left_orcl_ctx.set_renamed(left_export.alias());
                right_orcl_ctx.set_renamed(right_export.alias());
                for ((arg_name_left, arg_type), (arg_name_right, _)) in left_export
                    .sig()
                    .args
                    .iter()
                    .zip(right_export.sig().args.iter())
                {
                    if gctx_left.game_inst().game.name() == gctx_right.game_inst().game.name() {
                        out.push(declare_const(
                            left_orcl_ctx.smt_arg_name(arg_name_left),
                            arg_type.clone().into(),
                        ));
                    } else {
                        out.push(declare_const(
                            left_orcl_ctx.smt_arg_name(arg_name_left),
                            arg_type.clone().into(),
                        ));
                        out.push(declare_const(
                            right_orcl_ctx.smt_arg_name(arg_name_right),
                            arg_type.clone().into(),
                        ));
                        out.push(
                            SmtAssert(SmtEq2 {
                                lhs: left_orcl_ctx.smt_arg_name(arg_name_left),
                                rhs: right_orcl_ctx.smt_arg_name(arg_name_right),
                            })
                            .into(),
                        );
                    }
                }
            }
        }

        ////// return values

        out.extend(game_defs::build_returns(left, skip_return_constraint_for));
        out.extend(game_defs::build_returns(right, skip_return_constraint_for));

        /////// randomess counters

        for (decl_ctr, assert_ctr, assert_zero_ctr) in
            game_defs::build_rands(self.sample_info_left(), left)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            // For offset-based randomness mapping, we treat the user-provided
            // counters as actual randomness counters instead of adding them to
            // the old counters (base counters). This requires asserting that
            // old counters are zero and makes the SMT code simpler.
            out.push(assert_zero_ctr);
        }

        for (decl_ctr, assert_ctr, assert_zero_ctr) in
            game_defs::build_rands(self.sample_info_right(), right)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            // For offset-based randomness mapping, we treat the user-provided
            // counters as actual randomness counters instead of adding them to
            // the old counters (base counters). This requires asserting that
            // old counters are zero and makes the SMT code simpler.
            out.push(assert_zero_ctr);
        }

        out
    }
}

/// The claim of the package invariant `name` of package instance `pkg_inst` in the state of
/// `owner`: `package-invariant!<name>!<owner>-<pkg_inst>!`. The owner of the state is a game
/// instance in lockstep execution and a composition in one-sided execution (symbolic-execution
/// story 25). With no owner, the package is checked on its own (`domino prove --package`, story
/// 74) and `pkg_inst` is the package name: `package-invariant!<name>!<P>!`. The one owner of
/// this name.
pub(crate) fn package_invariant_claim_name(
    name: &str,
    owner: Option<&str>,
    pkg_inst: &str,
) -> String {
    match owner {
        Some(owner) => format!("package-invariant!{name}!{owner}-{pkg_inst}!"),
        None => format!("package-invariant!{name}!{pkg_inst}!"),
    }
}

/// The claim of the game invariant `name` on the state of `owner` (a game instance or a
/// composition, as for [`package_invariant_claim_name`]): `game-invariant!<name>!<owner>!`. The one owner of this
/// name.
pub(crate) fn game_invariant_claim_name(name: &str, owner: &str) -> String {
    format!("game-invariant!{name}!{owner}!")
}

#[cfg(test)]
mod story04_tests {
    //! Story 04 — assumptions/goal split + skippable return constraint.
    //!
    //! These pin the `prove`-facing output (`emit_oracle_claim_assert`,
    //! `emit_constant_declarations(None)`) against committed goldens and check the two new
    //! debugger-facing emitters compose back to the single refutation `prove` uses.

    use crate::gamehops::GameHop;
    use crate::project::Project as _;
    use crate::theorem::{BuiltInFact, ClaimKind, ResolvedClaim, ResolvedDependency};
    use crate::transforms::{theorem_transforms::EquivalenceTransform, TheoremTransform};
    use crate::writers::smt::contexts::EquivalenceContext;
    use crate::writers::smt::exprs::{SmtAnd, SmtAssert, SmtExpr, SmtImplies, SmtNot};

    const PROJECT: &str = "example-projects/kem-dem/kem-dem-cca-ssp";
    const THEOREM: &str = "kem_dem_cca_ssp";
    const ORACLE: &str = "PKENC";

    /// A claim that exercises the two-sided arms of `claim_assumptions_and_goal`: a built-in
    /// goal, a state-relation dependency and a project-lemma dependency.
    fn mixed_claim() -> ResolvedClaim {
        let dep = |name: &str, kind| ResolvedDependency {
            name: name.to_string(),
            kind,
        };
        ResolvedClaim {
            name: "same-output".to_string(),
            kind: ClaimKind::BuiltIn(BuiltInFact::SameOutput),
            dependencies: vec![
                dep("relation-no-abort", ClaimKind::StateRelation),
                dep("lemma-kem-correctness", ClaimKind::ProjectLemma),
            ],
            admitted: false,
        }
    }

    fn with_eqctx(f: impl FnOnce(&EquivalenceContext<'_>)) {
        let files = crate::project::DirectoryFiles::load(std::path::Path::new(PROJECT)).unwrap();
        let project =
            crate::project::DirectoryProject::load(std::path::PathBuf::from(PROJECT), &files)
                .unwrap();
        let theorem = project.get_theorem(THEOREM).unwrap();
        let (theorem, auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();

        let eq = theorem
            .game_hops
            .iter()
            .find_map(|hop| match hop {
                GameHop::Equivalence(eq) => Some(eq),
                _ => None,
            })
            .expect("proofstep 0 is an equivalence");

        let eqctx = EquivalenceContext::new(eq, &theorem, &auxs);
        f(&eqctx);
    }

    /// Compares `actual` against `testdata/story04/<name>`. If the golden file is missing it
    /// is written and the test fails, asking for a re-run — so the first run bootstraps it.
    fn check_golden(name: &str, actual: &str) {
        let path = std::path::Path::new("testdata/story04").join(name);
        match std::fs::read_to_string(&path) {
            Ok(expected) => assert_eq!(actual, expected, "golden mismatch for {name}"),
            Err(_) => {
                std::fs::create_dir_all(path.parent().unwrap()).unwrap();
                std::fs::write(&path, actual).unwrap();
                panic!("wrote new golden {}; re-run the test", path.display());
            }
        }
    }

    fn render(exprs: &[SmtExpr]) -> String {
        exprs
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }

    #[test]
    fn emit_oracle_claim_assert_matches_golden() {
        with_eqctx(|eqctx| {
            let out = eqctx.emit_oracle_claim_assert(&mixed_claim(), ORACLE);
            check_golden("emit_oracle_claim_assert.smt2", &out.to_string());
        });
    }

    #[test]
    fn emit_constant_declarations_none_matches_golden() {
        with_eqctx(|eqctx| {
            let out = eqctx.emit_constant_declarations(None);
            check_golden("emit_constant_declarations_none.smt2", &render(&out));
        });
    }

    /// The wrappers compose back to exactly the single refutation `prove` emits.
    #[test]
    fn assumptions_and_negated_goal_compose_to_claim_assert() {
        with_eqctx(|eqctx| {
            let claim = mixed_claim();
            let (deps, goal) = eqctx.claim_assumptions_and_goal(&claim, ORACLE);

            let recombined: SmtExpr =
                SmtAssert(SmtNot(SmtImplies(SmtAnd(deps.clone()), goal.clone()))).into();
            assert_eq!(
                recombined.to_string(),
                eqctx.emit_oracle_claim_assert(&claim, ORACLE).to_string(),
            );

            // one `(assert <dep>)` per assumption, same order
            let assumptions = eqctx.emit_claim_assumptions(&claim, ORACLE);
            assert_eq!(assumptions.len(), deps.len());
            for (asserted, term) in assumptions.iter().zip(&deps) {
                let expected: SmtExpr = SmtAssert(term.clone()).into();
                assert_eq!(asserted.to_string(), expected.to_string());
            }

            // `(assert (not <goal>))`
            let negated = eqctx.emit_claim_goal_negated(&claim, ORACLE);
            let expected: SmtExpr = SmtAssert(SmtNot(goal)).into();
            assert_eq!(negated.to_string(), expected.to_string());
        });
    }

    /// `emit_constant_declarations(Some(o))` differs from `None` by exactly the two
    /// `constrain_return` asserts for `o` (left + right) and nothing else.
    #[test]
    fn skip_return_constraint_drops_exactly_two_asserts() {
        with_eqctx(|eqctx| {
            let none: Vec<String> = eqctx
                .emit_constant_declarations(None)
                .iter()
                .map(|e| e.to_string())
                .collect();
            let some: Vec<String> = eqctx
                .emit_constant_declarations(Some(ORACLE))
                .iter()
                .map(|e| e.to_string())
                .collect();

            // `some` is `none` with two entries removed, order otherwise preserved.
            let mut some_iter = some.iter();
            let mut removed = Vec::new();
            let mut cursor = some_iter.next();
            for line in &none {
                if cursor == Some(line) {
                    cursor = some_iter.next();
                } else {
                    removed.push(line.clone());
                }
            }
            assert_eq!(cursor, None, "`some` is not a subsequence of `none`");
            assert_eq!(removed.len(), 2, "expected exactly two dropped asserts");
            for r in &removed {
                let flat: String = r.split_whitespace().collect::<Vec<_>>().join(" ");
                assert!(
                    flat.starts_with("(assert (= <return-")
                        && flat.contains(&format!("-{ORACLE}> (<oracle-")),
                    "unexpected dropped line: {r}"
                );
            }
            // one for the left game instance, one for the right
            assert_ne!(removed[0], removed[1]);
        });
    }
}

#[cfg(test)]
mod story74_tests {
    //! Story 74 — package invariants leave the equivalence: no claim, but still an assumption.

    use crate::gamehops::GameHop;
    use crate::project::Project as _;
    use crate::theorem::ClaimKind;
    use crate::transforms::{theorem_transforms::EquivalenceTransform, TheoremTransform};
    use crate::writers::smt::contexts::EquivalenceContext;

    const PROJECT: &str = "test-projects/test-package-invariant-imports";

    #[test]
    fn an_equivalence_has_no_package_invariant_claim_but_assumes_each_one() {
        let files = crate::project::DirectoryFiles::load(std::path::Path::new(PROJECT)).unwrap();
        let project =
            crate::project::DirectoryProject::load(std::path::PathBuf::from(PROJECT), &files)
                .unwrap();
        let theorem = project.get_theorem("Proof").unwrap();
        let (theorem, auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();
        let eq = theorem
            .game_hops
            .iter()
            .find_map(|hop| match hop {
                GameHop::Equivalence(eq) => Some(eq),
                _ => None,
            })
            .unwrap();
        let mut eqctx = EquivalenceContext::new(eq, &theorem, &auxs);
        eqctx.load_invariants(&project).unwrap();
        eqctx.resolve_claims().unwrap();

        let claims = eqctx.generate_game_invariant_claims();
        assert!(
            claims
                .iter()
                .all(|c| !matches!(c.kind(), ClaimKind::PackageInvariant { .. })),
            "{claims:?}"
        );

        // the base frame still assumes each named package invariant on both old states
        let claim = eqctx
            .proof_tree("Step")
            .into_iter()
            .find(|c| c.name() == "invariant")
            .unwrap();
        let smt = eqctx.emit_oracle_claim_assert(&claim, "Step").to_string();
        for name in ["nonneg", "unseen"] {
            for owner in ["left", "right"] {
                let fact = format!("package-invariant!{name}!{owner}-ctr!");
                assert!(smt.contains(&fact), "{fact} missing in {smt}");
            }
        }
    }
}
