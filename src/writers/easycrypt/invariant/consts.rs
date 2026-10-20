// SPDX-License-Identifier: MIT OR Apache-2.0

//! The game constants of a composition in its game invariants (story 80, ADR 0019 points 3
//! and 4).
//!
//! A game constant is in no memory: the router's `init` passes it to the packages and keeps no
//! copy. So a composition with a game invariant gets the field `<C>_const_<X>` in `<C>_side`
//! for each constant `X` that is an `init` argument ([`side_consts`]), and `game.<X>` reads it.
//! The value of the field comes from a binder of the side-invariant lemmas, and from the game
//! instance's binding in the equivalence. `links_<C>` ([`links_body`]) relates the fields to
//! the module variables: each value parameter field equals the constant or the literal that
//! the composition binds it to.

use miette::SourceSpan;

use crate::identifier::{game_ident::GameIdentifier, Identifier};
use crate::package::Composition;

use super::super::ast::{EcExpr, EcType};
use super::super::game::composition_const_needs_arg;
use super::super::interfaces::composition_span;
use super::super::names::{NameKind, Names};
use super::super::types::{translate_expr, translate_type};
use super::super::EcExportError;
use super::params::{has_side_params, has_value_params, param_fields, params_field_name};
use super::{eq_expr, field_expr, fold_and};

/// One game constant of a composition that is a field of `<C>_side`.
pub(crate) struct SideConst {
    /// The constant's Domino name.
    pub raw: String,
    /// The mangled name: the `<X>` of `<C>_const_<X>`, and the name of the lemma binder.
    pub mangled: String,
    pub ty: EcType,
}

/// The side-record field that holds game constant `mangled`: `<prefix>const_<X>`.
pub(crate) fn const_field_name(prefix: &str, mangled: &str) -> String {
    format!("{prefix}const_{mangled}")
}

/// The game constants of `comp` that are fields of `<C>_side`, in declaration order: each
/// constant that is an `init` argument ([`composition_const_needs_arg`]), when `comp` has a
/// game invariant; else none.
pub(crate) fn side_consts(comp: &Composition) -> Result<Vec<SideConst>, EcExportError> {
    if comp.invariants.is_empty() {
        return Ok(Vec::new());
    }
    let mut names = Names::new();
    let mut out = Vec::new();
    for (name, ty) in &comp.consts {
        if !composition_const_needs_arg(comp, name, ty) {
            continue;
        }
        out.push(SideConst {
            raw: name.clone(),
            mangled: names.mangle(NameKind::Var, name)?,
            ty: translate_type(ty, composition_span(comp))?,
        });
    }
    Ok(out)
}

/// `links_<C>`: the side-record links of composition `<C>`.
pub(crate) fn links_op_name(comp: &str) -> String {
    format!("links_{comp}")
}

/// The body of `links_<C> (s : <C>_side)`, or `None` without links ([`has_links`]). One
/// equation ``s.`<prefix>params_<I>.`<P>_param_<p> = <value>`` for each value parameter `p` of
/// each instance `I` with a params field, in `ordered_pkgs_idx()` order. The value is
/// ``s.`<prefix>const_<X>`` for a binding to constant `X`, or the literal.
pub(crate) fn links_body(
    comp: &Composition,
    prefix: &str,
) -> Result<Option<EcExpr>, EcExportError> {
    if !has_links(comp) {
        return Ok(None);
    }
    let consts = side_consts(comp)?;
    let mut resolve = |id: &Identifier, _: SourceSpan| match id {
        Identifier::GameIdentifier(GameIdentifier::Const(c)) => {
            let constant = consts
                .iter()
                .find(|k| k.raw == c.name)
                .expect("a value parameter is bound to an `init` argument");
            Ok(field_expr(
                "s",
                &const_field_name(prefix, &constant.mangled),
            ))
        }
        other => unreachable!("a parameter binding names only a game constant, not {other:?}"),
    };
    let mut equations = Vec::new();
    for &idx in &comp.ordered_pkgs_idx() {
        let inst = &comp.pkgs[idx];
        if !has_side_params(comp, inst) {
            continue;
        }
        let params = field_expr("s", &params_field_name(prefix, inst.name()));
        for field in param_fields(inst)?.into_iter().filter(|f| f.var.is_some()) {
            let bound = inst
                .params
                .iter()
                .find(|(id, _)| id.name == field.raw)
                .map(|(_, e)| e)
                .expect("a package instance binds every parameter of its package");
            let value = translate_expr(bound, composition_span(comp), &mut resolve)?;
            let projection = EcExpr::Field {
                expr: Box::new(params.clone()),
                field: field.field,
            };
            equations.push(eq_expr(projection, value));
        }
    }
    Ok(Some(fold_and(equations)))
}

/// Whether `comp` has `links_<C>`: it has a game invariant, and an instance with a params
/// field has a value parameter.
pub(crate) fn has_links(comp: &Composition) -> bool {
    !comp.invariants.is_empty()
        && comp
            .pkgs
            .iter()
            .any(|inst| has_side_params(comp, inst) && has_value_params(&inst.pkg))
}
