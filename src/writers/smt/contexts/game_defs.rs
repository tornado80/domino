// SPDX-License-Identifier: MIT OR Apache-2.0

//! SMT declarations and definitions that describe one or more *game instances*.
//!
//! Both the equivalence prover (which works on two game instances at a time) and the package
//! invariant prover (which works on a single, synthetic game instance) need the same set of
//! datatype declarations, constant mapping functions and oracle function definitions. This module
//! holds that shared code, parameterised over the list of game instances it should cover.

use std::collections::{BTreeSet, HashSet};

use crate::{
    hacks,
    identifier::{
        theorem_ident::{TheoremConstIdentifier, TheoremIdentifier},
        Identifier,
    },
    theorem::{GameInstance, Theorem},
    transforms::samplify::SampleInfo,
    types::{CountSpec, Type, TypeKind},
    writers::smt::{
        contexts::{GameInstanceContext, GenericOracleContext},
        declare::declare_const,
        exprs::{SmtAssert, SmtEq2, SmtExpr},
        patterns::{
            self,
            const_mapping::{define_game_const_mapping_fun, define_pkg_const_mapping_fun},
            datastructures::DatastructurePattern,
            declare_datatype,
            functions::FunctionPattern,
            oracle_args::GameStateOracleArgPattern,
            oracle_args::OracleArgPattern,
            oracle_args::UnitOracleArgPattern,
            theorem_constants::ConstantPattern,
            GameStateDeclareInfo, ReturnIsAbortConst,
        },
        sorts::Sort,
        writer::CompositionSmtWriter,
    },
};

/// One game instance together with the sampling information that was collected for it.
pub(crate) type GameInstanceWithSampleInfo<'a> = (GameInstanceContext<'a>, &'a SampleInfo);

/// Emits the sort declarations that every proof needs: the `Bits_*` sorts occurring in `types`,
/// plus the `Maybe`, `ReturnValue`, `TupleN`, `Empty` and `SampleId` helpers.
pub(crate) fn emit_base_declarations(types: &[Type]) -> Vec<SmtExpr> {
    let mut base_declarations: Vec<SmtExpr> = vec![("set-logic", "ALL").into()];

    let mut bits_sort_suffixes = HashSet::new();

    for ty in types {
        if let TypeKind::Bits(count_spec) = &ty.kind() {
            let bits_sort_suffix = count_spec.resolved_suffix();

            log::debug!("found {bits_sort_suffix}");

            // ensure we don't write more than once. Earlier we also dedupe, but we dedupe
            // identifiers, which contain more info than just the name.
            if bits_sort_suffixes.insert(bits_sort_suffix.clone()) {
                base_declarations.extend(hacks::BitsDeclaration(bits_sort_suffix));
            }
        }
    }

    base_declarations.extend(hacks::MaybeDeclaration);
    base_declarations.push(hacks::ReturnValueDeclaration.into());
    base_declarations.extend(hacks::TuplesDeclaration(0..32));
    base_declarations.extend(hacks::EmptyDeclaration);
    base_declarations.push(hacks::SampleIdDeclaration.into());

    base_declarations
}

/// Returns the `Bits(<theorem const>)` types induced by the integer constants of `theorem`.
///
/// These need to be part of the type list handed to [`emit_base_declarations`], because a
/// `Bits(n)` sort may only show up after the package parameter `n` has been resolved to a theorem
/// constant.
pub(crate) fn theorem_const_bits_types(theorem: &Theorem) -> HashSet<Type> {
    theorem
        .consts
        .iter()
        .filter_map(|(name, ty)| match ty.kind() {
            TypeKind::Integer => {
                let id = TheoremConstIdentifier {
                    theorem_name: theorem.name.clone(),
                    name: name.clone(),
                    ty: Type::integer(),
                    inst_info: None,
                };

                Some(Type::bits(CountSpec::Identifier(Box::new(
                    Identifier::TheoremIdentifier(TheoremIdentifier::Const(id)),
                ))))
            }
            _ => None,
        })
        .collect()
}

/// Declares the function-typed theorem constants as plain SMT functions.
///
/// Function-typed constants are excluded from the theorem/game/package constant datatypes (see
/// e.g. [`crate::writers::smt::patterns::theorem_consts::TheoremConstsPattern`]), so that we stay
/// compatible with solvers without higher-order support. Instead they live in the global scope.
pub(crate) fn emit_theorem_paramfuncs(theorem: &Theorem) -> Vec<SmtExpr> {
    theorem
        .consts
        .iter()
        .filter_map(|(name, ty)| match ty.kind() {
            TypeKind::Fn(args, ret) => Some((name.clone(), args.to_vec(), (**ret).clone())),
            _ => None,
        })
        .map(|(func_name, arg_types, ret_type)| {
            let arg_types: SmtExpr = arg_types
                .into_iter()
                .map(|ty| ty.into())
                .collect::<Vec<SmtExpr>>()
                .into();

            (
                "declare-fun",
                format!("<<func-{func_name}>>"),
                arg_types,
                ret_type,
            )
                .into()
        })
        .collect()
}

/// Emits all datatype declarations, constant mapping functions and oracle function definitions
/// for the given game instances.
///
/// Definitions that would be emitted more than once (e.g. because the same package or the same
/// game is instantiated twice) are only emitted the first time.
pub(crate) fn emit_game_definitions<'a>(
    theorem: &'a Theorem<'a>,
    games: &[GameInstanceWithSampleInfo<'a>],
) -> Vec<SmtExpr> {
    let mut out = Vec::new();

    for (gctx, sample_info) in games {
        let mut writer = CompositionSmtWriter::new(gctx.game_inst(), sample_info);
        out.extend(writer.smt_composition_randomness());
    }

    out.extend(smt_package_const_definitions(games));
    out.extend(smt_package_state_definitions(games));
    out.extend(smt_theorem_const_definition(theorem));
    out.extend(smt_game_const_definitions(games));
    out.extend(smt_game_state_definitions(games));
    out.extend(smt_theorem_game_const_mapping_definitions(theorem, games));
    out.extend(smt_game_pkg_const_mapping_definitions(games));
    out.extend(smt_package_return_definitions(games));
    out.extend(smt_oracle_function_definitions(games));

    out
}

/// All the package const datatypes that need to be defined, skipping duplicate definitions.
fn smt_package_const_definitions(games: &[GameInstanceWithSampleInfo]) -> Vec<SmtExpr> {
    let mut already_defined = BTreeSet::new();

    games
        .iter()
        .flat_map(|(gctx, _)| gctx.pkg_inst_contexts())
        .filter_map(|pctx| {
            let pattern = pctx.datastructure_pkg_consts_pattern();
            let spec = pattern.datastructure_spec(pctx.pkg());

            if already_defined.insert(pattern.sort_name()) {
                Some(declare_datatype(&pattern, &spec))
            } else {
                None
            }
        })
        .collect()
}

/// All the package state datatypes that need to be defined, skipping duplicate definitions.
fn smt_package_state_definitions(games: &[GameInstanceWithSampleInfo]) -> Vec<SmtExpr> {
    let mut already_defined = BTreeSet::new();

    games
        .iter()
        .flat_map(|(gctx, _)| gctx.pkg_inst_contexts())
        .filter_map(|pctx| {
            let pattern = pctx.pkg_state_pattern();
            let spec = pattern.datastructure_spec(pctx.pkg());

            if already_defined.insert(pattern.sort_name()) {
                Some(declare_datatype(&pattern, &spec))
            } else {
                None
            }
        })
        .collect()
}

/// All the oracle return datatypes that need to be defined, skipping duplicate definitions.
fn smt_package_return_definitions(games: &[GameInstanceWithSampleInfo]) -> Vec<SmtExpr> {
    let mut already_defined = BTreeSet::new();

    games
        .iter()
        .flat_map(|(gctx, _)| gctx.pkg_inst_contexts())
        .flat_map(|pctx| pctx.oracle_contexts())
        .filter_map(|octx| {
            let pattern = octx.return_pattern();
            let spec = pattern.datastructure_spec(&octx.oracle_sig().ty);

            if already_defined.insert(pattern.sort_name()) {
                Some(declare_datatype(&pattern, &spec))
            } else {
                None
            }
        })
        .collect()
}

/// All the game state datatypes that need to be defined, skipping duplicate definitions.
fn smt_game_state_definitions(games: &[GameInstanceWithSampleInfo]) -> Vec<SmtExpr> {
    let mut already_defined = BTreeSet::new();

    games
        .iter()
        .filter_map(|(gctx, sample_info)| {
            let declare_info = GameStateDeclareInfo {
                game_inst: gctx.game_inst(),
                sample_info,
            };

            let pattern = gctx.datastructure_game_state_pattern();
            let spec = pattern.datastructure_spec(&declare_info);

            if already_defined.insert(pattern.sort_name()) {
                Some(declare_datatype(&pattern, &spec))
            } else {
                None
            }
        })
        .collect()
}

/// The theorem const datatype.
fn smt_theorem_const_definition<'a>(theorem: &'a Theorem<'a>) -> Vec<SmtExpr> {
    let pattern = patterns::theorem_consts::TheoremConstsPattern {
        theorem_name: &theorem.name,
    };
    let spec = pattern.datastructure_spec(theorem);

    vec![declare_datatype(&pattern, &spec)]
}

/// All the game const datatypes that need to be defined, skipping duplicate definitions.
fn smt_game_const_definitions(games: &[GameInstanceWithSampleInfo]) -> Vec<SmtExpr> {
    let mut already_defined = BTreeSet::new();

    games
        .iter()
        .filter_map(|(gctx, _)| {
            let pattern = gctx.datastructure_game_consts_pattern();
            let spec = pattern.datastructure_spec(gctx.game());

            if already_defined.insert(pattern.sort_name()) {
                Some(declare_datatype(&pattern, &spec))
            } else {
                None
            }
        })
        .collect()
}

/// The functions that map the constant values of the theorem to those of a game instance.
fn smt_theorem_game_const_mapping_definitions<'a>(
    theorem: &'a Theorem<'a>,
    games: &[GameInstanceWithSampleInfo<'a>],
) -> Vec<SmtExpr> {
    games
        .iter()
        .filter_map(|(gctx, _)| {
            let game_inst = gctx.game_inst();
            define_game_const_mapping_fun(theorem, game_inst.game(), game_inst.name())
                .map(SmtExpr::from)
        })
        .collect()
}

/// The functions that map the constant values of a game to those of its package instances.
fn smt_game_pkg_const_mapping_definitions(games: &[GameInstanceWithSampleInfo]) -> Vec<SmtExpr> {
    let mut seen_game_names: HashSet<&str> = Default::default();

    games
        .iter()
        .filter(|(gctx, _)| seen_game_names.insert(gctx.game_name()))
        .flat_map(|(gctx, _)| {
            gctx.game().pkgs.iter().filter_map(move |pkg_inst| {
                define_pkg_const_mapping_fun(gctx.game(), &pkg_inst.pkg, &pkg_inst.name)
                    .map(SmtExpr::from)
            })
        })
        .collect()
}

/// The oracle function definitions, skipping oracles that have already been defined.
fn smt_oracle_function_definitions(games: &[GameInstanceWithSampleInfo]) -> Vec<SmtExpr> {
    let mut already_defined = BTreeSet::new();

    games
        .iter()
        .flat_map(|(gctx, sample_info)| {
            gctx.pkg_inst_contexts()
                .map(move |pctx| (pctx, sample_info))
        })
        .flat_map(|(pctx, sample_info)| pctx.oracle_contexts().map(move |octx| (octx, sample_info)))
        .filter_map(|(octx, sample_info)| {
            let gctx = octx.game_inst_ctx();
            let pctx = octx.pkg_inst_ctx();
            let pattern = octx.oracle_pattern();

            let writer = CompositionSmtWriter::new(gctx.game_inst(), sample_info);

            if already_defined.insert(pattern.function_name()) {
                Some(writer.smt_define_nonsplit_oracle_fn(pctx.pkg_inst(), octx.oracle_def()))
            } else {
                None
            }
        })
        .collect()
}

/// Emits, for every exported oracle of `game_inst`, the four declare/constrain pairs the
/// claim machinery relies on: `<return-…>`, `return-value-…`, `<return-is-abort-…>` and the
/// new game state, each declared then constrained, interleaved in that order.
///
/// When `skip_return_constraint_for == Some(o)` and the export's adversary-visible name is
/// `o`, the `<return-o>` **declaration** is still emitted but its constraint
/// `(= <return-o> (<oracle-fn> …))` is **not**. The debugger supplies that constraint itself
/// from its per-path DSA encoding; `return-value-o`, `<return-is-abort-o>` and the new state
/// stay constrained off `<return-o>` exactly as before, so `emit_oracle_claim_assert`, the
/// invariants and the relations keep working unchanged.
pub(crate) fn build_returns(
    game_inst: &GameInstance,
    skip_return_constraint_for: Option<&str>,
) -> Vec<SmtExpr> {
    let gctx = GameInstanceContext::new(game_inst);
    let game_name = &game_inst.game().name;
    let game_inst_name = &game_inst.name();
    let game_params = &game_inst.consts;

    // write declarations of right return constants and constrain them
    let mut out = vec![];
    for export in &game_inst.game().exports {
        let pkg_inst = &game_inst.game().pkgs[export.to()];
        let sig = export.sig();

        let pkg_inst_name = &pkg_inst.name;
        let pkg_params = &pkg_inst.params;
        let pkg_name = &pkg_inst.pkg.name;
        let oracle_name = &sig.name;
        let oracle_import_name = export.name();
        let return_type = &sig.ty;

        let mut octx = gctx
            .exported_oracle_ctx_by_name(export.name())
            .unwrap_or_else(|| {
                panic!(
                    "error looking up exported oracle with name {oracle_name} in game {game_name}"
                )
            });
        octx.set_renamed(export.alias());

        let return_const = patterns::ReturnConst {
            game_inst_name,
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
            oracle_import_name,
        };

        let return_value_const = patterns::ReturnValueConst {
            game_inst_name,
            pkg_inst_name,
            oracle_name: oracle_import_name,
            ty: &sig.ty,
        };

        let is_abort_const_pattern = ReturnIsAbortConst {
            game_inst_name,
            pkg_inst_name,
            oracle_name: oracle_import_name,
            ty: &sig.ty,
        };

        let state = octx.oracle_arg_game_state_pattern();
        let consts = octx.oracle_arg_game_consts_pattern();

        let old_state_const = state.old_global_const_name(game_inst_name);
        let new_state_const =
            state.new_global_const_name(game_inst_name, oracle_import_name.to_string());
        let consts_const = consts.unit_global_const_name(game_inst_name);

        let args = sig
            .args
            .iter()
            .map(|(arg_name, _)| octx.smt_arg_name(arg_name));

        let oracle_func_evaluation = octx
            .smt_call_oracle_fn(old_state_const, consts_const, args)
            .unwrap();

        let return_pattern = octx.return_pattern();
        let return_spec = return_pattern.datastructure_spec(return_type);

        let access_returnvalue = return_pattern
            .access(
                &return_spec,
                &patterns::ReturnSelector::ReturnValueOrAbort {
                    return_type: &sig.ty,
                },
                return_const.name(),
            )
            .unwrap();

        let access_new_state = return_pattern
            .access(
                &return_spec,
                &patterns::ReturnSelector::GameState,
                return_const.name(),
            )
            .unwrap();

        let constrain_return = SmtAssert(SmtEq2 {
            lhs: return_const.name(),
            rhs: oracle_func_evaluation,
        });

        let constrain_return_value = SmtAssert(SmtEq2 {
            lhs: return_value_const.name(),
            rhs: access_returnvalue,
        });

        let constrain_new_state = SmtAssert(SmtEq2 {
            lhs: new_state_const,
            rhs: access_new_state,
        });

        let constrain_is_abort = SmtAssert(SmtEq2 {
            lhs: is_abort_const_pattern.name(),
            rhs: is_abort_const_pattern.value(return_value_const.name()),
        });

        out.push(return_const.declare());
        if skip_return_constraint_for != Some(oracle_import_name) {
            out.push(constrain_return.into());
        }
        out.push(return_value_const.declare());
        out.push(constrain_return_value.into());
        out.push(is_abort_const_pattern.declare());
        out.push(constrain_is_abort.into());
        out.push(state.declare_new(game_inst_name, oracle_import_name.to_string()));
        out.push(constrain_new_state.into());
    }

    out
}

pub(crate) fn build_rands(
    sample_info: &SampleInfo,
    game_inst: &GameInstance,
) -> Vec<(SmtExpr, SmtExpr, SmtExpr)> {
    let gctx = GameInstanceContext::new(game_inst);

    sample_info
        .positions
        .iter()
        .map(|sample_item| {
            let sample_id = sample_item.sample_id;
            let game_inst_name = game_inst.name();

            let state = gctx
                .oracle_arg_game_state_pattern()
                .old_global_const_name(game_inst_name);

            let randctr_name = format!("randctr-{game_inst_name}-{sample_id}");

            let decl_randctr = declare_const(randctr_name.clone(), Sort::Int);

            // pull randomness counter for given sample_id out of the gamestate
            let randctr = gctx
                .smt_access_gamestate_rand(sample_info, state, sample_id)
                .unwrap();

            let constrain_randctr: SmtExpr = SmtAssert(SmtEq2 {
                lhs: randctr_name.as_str(),
                rhs: randctr.clone(),
            })
            .into();

            let zero_constrain_randctr: SmtExpr = SmtAssert(SmtEq2 {
                lhs: randctr_name.as_str(),
                rhs: 0,
            })
            .into();

            (decl_randctr, constrain_randctr, zero_constrain_randctr)
        })
        .collect()
}

/// Declares the initial game state constant and constrains every package state field to the
/// default value of its type.
pub(crate) fn emit_game_initial_state_values(gctx: GameInstanceContext) -> Vec<SmtExpr> {
    let game_inst_name = gctx.game_inst_name();
    let initial_state = gctx.oracle_arg_game_state_pattern().global_const_name(
        game_inst_name,
        &patterns::oracle_args::GameStateOracleArgVariant::Initial,
    );

    let mut out = Vec::new();
    out.push(
        gctx.oracle_arg_game_state_pattern()
            .declare_initial(game_inst_name),
    );

    for pctx in gctx.pkg_inst_contexts() {
        let pkg_state = gctx
            .smt_access_gamestate_pkgstate(&initial_state, pctx.pkg_inst_name())
            .unwrap();

        for (field_name, field_ty, _) in &pctx.pkg().state {
            let field = pctx
                .smt_access_pkgstate(pkg_state.clone(), field_name)
                .unwrap();

            out.push(
                SmtAssert(SmtEq2 {
                    lhs: field,
                    rhs: SmtExpr::from(&field_ty.default_expression()),
                })
                .into(),
            );
        }
    }

    out
}
