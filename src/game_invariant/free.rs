// SPDX-License-Identifier: MIT OR Apache-2.0

//! The free composition: `C` and its copy `C$side`, with each parameter of `C` a free theorem
//! constant, and the equivalence of the two that gives the SMT vocabulary.
//!
//! The claims ([`claims`]) and the base frame ([`base_frame`]) read only the left side (`C`).
//! The side tree of `domino easycrypt debug --side-inv C` and `domino prove --game C` read this
//! one encoding.

use crate::expressions::Expression;
use crate::gamehops::equivalence::Equivalence;
use crate::identifier::game_ident::{GameConstIdentifier, GameIdentifier};
use crate::identifier::theorem_ident::{TheoremConstIdentifier, TheoremIdentifier};
use crate::identifier::Identifier;
use crate::package::{Composition, Package};
use crate::theorem::{
    BuiltInFact, ClaimKind, GameInstance, InvariantSide, RandomnessType, ResolvedClaim,
    ResolvedDependency, Theorem,
};
use crate::types::{CountSpec, Type, TypeKind};
use crate::writers::smt::contexts::EquivalenceContext;
use crate::writers::smt::exprs::SmtExpr;

/// The dependency of every game-invariant claim: the invariant holds under `!abort`.
const NO_ABORT: BuiltInFact = BuiltInFact::LeftNoAbort;

/// The name of the empty theorem of composition `composition`: `<C>$Invariant`.
pub(crate) fn theorem_name(composition: &str) -> String {
    format!("{composition}$Invariant")
}

/// The free theorem of `comp` alone (no theorem of the project): [`free_theorem`] of an empty
/// theorem named [`theorem_name`] that has only the packages of `comp`.
pub(crate) fn composition_theorem<'a>(comp: &Composition) -> (Theorem<'a>, Equivalence) {
    let mut pkgs: Vec<Package> = Vec::new();
    for inst in &comp.pkgs {
        if !pkgs.iter().any(|p| p.name == inst.pkg.name) {
            pkgs.push(inst.pkg.clone());
        }
    }
    let empty = Theorem {
        name: theorem_name(&comp.name),
        consts: Vec::new(),
        instances: Vec::new(),
        assumptions: Vec::new(),
        proofs: Vec::new(),
        game_hops: Vec::new(),
        pkgs,
    };
    free_theorem(&empty, comp)
}

/// The name of the copy of `C` that completes the [`EquivalenceContext`].
fn copy_name(composition: &str) -> String {
    format!("{composition}$side")
}

/// The theorem that one-sided execution of `comp` reads: `theorem` with only two game instances
/// of `comp`, `C` and `C$side`, whose parameters are free theorem constants, and the equivalence
/// of the two that gives the SMT vocabulary. It keeps the name, the constants, the packages and
/// the assumptions of `theorem`, and drops its game instances, game hops and proofs: one-sided
/// execution reads none of them, and a theorem instance named `C` cannot clash (story 85).
pub(crate) fn free_theorem<'a>(
    theorem: &Theorem<'a>,
    comp: &Composition,
) -> (Theorem<'a>, Equivalence) {
    let name = comp.name.clone();
    let copy = copy_name(&name);
    let mut theorem = Theorem {
        instances: Vec::new(),
        game_hops: Vec::new(),
        proofs: Vec::new(),
        ..theorem.clone()
    };
    let params = free_params(&mut theorem, comp);
    for inst_name in [&name, &copy] {
        let inst = GameInstance::new(
            inst_name.clone(),
            theorem.name.clone(),
            comp.clone(),
            Vec::new(),
            params
                .iter()
                .map(|(id, value)| {
                    let id = GameConstIdentifier {
                        game_inst_name: Some(inst_name.clone()),
                        ..id.clone()
                    };
                    (id, value.clone())
                })
                .collect(),
        );
        theorem.instances.push(inst);
    }
    let randomness = comp
        .exports
        .iter()
        .map(|e| (e.name().to_string(), RandomnessType::None))
        .collect();
    let eq = Equivalence::new(
        theorem.name.clone(),
        name,
        copy,
        Vec::new(),
        Vec::new(),
        randomness,
    );
    (theorem, eq)
}

/// One free theorem constant for each parameter of `comp`, added to `theorem` where it has none
/// of that name and type. Integer parameters come first, so `Bits(<param>)` in the type of
/// another parameter is rewritten to `Bits(<constant>)`, as the theorem parser does.
fn free_params(
    theorem: &mut Theorem<'_>,
    comp: &Composition,
) -> Vec<(GameConstIdentifier, Expression)> {
    let (ints, others): (Vec<_>, Vec<_>) = comp
        .consts
        .iter()
        .partition(|(_, ty)| matches!(ty.kind(), TypeKind::Integer));
    let mut rules = Vec::new();
    let mut params = Vec::new();
    for (param, ty) in ints.into_iter().chain(others) {
        let ty = ty.rewrite_type(&rules);
        let const_name = match theorem.consts.iter().find(|(n, _)| n == param) {
            Some((_, existing)) if *existing == ty => param.clone(),
            Some(_) => format!("{}_{param}", comp.name),
            None => param.clone(),
        };
        if !theorem.consts.iter().any(|(n, _)| *n == const_name) {
            theorem.consts.push((const_name.clone(), ty.clone()));
        }
        let ident =
            Identifier::TheoremIdentifier(TheoremIdentifier::Const(TheoremConstIdentifier {
                theorem_name: theorem.name.clone(),
                name: const_name,
                ty: ty.clone(),
                inst_info: None,
            }));
        if matches!(ty.kind(), TypeKind::Integer) {
            rules.push((
                Type::bits(CountSpec::Identifier(Box::new(Identifier::GameIdentifier(
                    GameIdentifier::Const(GameConstIdentifier {
                        game_name: comp.name.clone(),
                        name: param.clone(),
                        ty: Type::integer(),
                        game_inst_name: None,
                        theorem_name: None,
                        inst_info: None,
                        assigned_value: None,
                    }),
                )))),
                Type::bits(CountSpec::Identifier(Box::new(ident.clone()))),
            ));
        }
        let value: Expression = ident.into();
        params.push((
            GameConstIdentifier {
                game_name: comp.name.clone(),
                name: param.clone(),
                ty,
                assigned_value: Some(Box::new(value.clone())),
                inst_info: None,
                game_inst_name: None,
                theorem_name: Some(theorem.name.clone()),
            },
            value,
        ));
    }
    params
}

/// The claims of a side tree: each game invariant of `C` on the new state, under
/// `left-no-abort`. The package invariants are not claims (story 77, ADR 0016): the package
/// tree checks each package once, and `SideInv_<C>_<O>` takes them from the package lemmas.
pub(crate) fn claims(eqctx: &EquivalenceContext<'_>) -> Vec<ResolvedClaim> {
    eqctx
        .generate_game_invariant_claims()
        .into_iter()
        .filter(|c| c.kind().invariant_side() == Some(InvariantSide::Left))
        .map(|c| ResolvedClaim {
            dependencies: vec![ResolvedDependency {
                name: NO_ABORT.name().to_string(),
                kind: ClaimKind::BuiltIn(NO_ABORT),
            }],
            ..c
        })
        .collect()
}

/// The base frame of a side tree: the declarations and definitions `prove` uses (both sides',
/// the copy's never read), and then each invariant of `C` on the old state, the package
/// invariants too: the side tree assumes them, and checks only the game invariants. The return
/// of `oracle` has no constraint: one-sided execution walks its paths.
pub(crate) fn base_frame(eqctx: &EquivalenceContext<'_>, oracle: &str) -> Vec<SmtExpr> {
    let mut base = vec![SmtExpr::Comment(
        " domino easycrypt debug --side-inv — base frame ".to_string(),
    )];
    base.extend(frame(eqctx, oracle, Some(oracle)));
    base
}

/// The frame of a claim of `domino prove --game` for `oracle`: the base frame of the side tree,
/// but the return of `oracle` is the value of its SMT function on the old state, as in `prove`.
pub(crate) fn oracle_frame(eqctx: &EquivalenceContext<'_>, oracle: &str) -> Vec<SmtExpr> {
    let mut base = vec![SmtExpr::Comment(
        " domino prove --game — oracle frame ".to_string(),
    )];
    base.extend(frame(eqctx, oracle, None));
    base
}

/// The frame of `oracle`, with the return constraint of `unconstrained` left out.
fn frame(
    eqctx: &EquivalenceContext<'_>,
    oracle: &str,
    unconstrained: Option<&str>,
) -> Vec<SmtExpr> {
    let mut base = eqctx.emit_base_declarations();
    base.extend(eqctx.emit_theorem_paramfuncs());
    base.extend(eqctx.emit_game_definitions());
    base.extend(eqctx.emit_constant_declarations(unconstrained));
    base.extend(eqctx.emit_auto_randomness(oracle));
    base.extend(eqctx.emit_invariant());
    base.extend(eqctx.emit_return_value_helpers(oracle));
    base.push(SmtExpr::Comment(
        " the side invariants on the old state ".to_string(),
    ));
    base.extend(eqctx.emit_left_side_invariants_old(oracle));
    base
}
