// SPDX-License-Identifier: MIT OR Apache-2.0

//! The parameters of a package in its package invariants (story 78, ADR 0019 point 1).
//!
//! A package with package invariants and with parameters that its variants do not bake into a
//! type (every Bool, every Integer that [`package::param_needs_var`] keeps, every function
//! parameter) gets the record type `<P>_pkgparams`, next to `<P>_pkgstate`. Its templates take
//! it as the first argument: `PkgInv_<N>_of_<P> (p : <P>_pkgparams) (s : <P>_pkgstate)`. Each
//! place that applies a template builds the params literal with [`pkg_params_lit`]: a value field
//! reads a module variable, a function field is the operator of the theorem constant that the
//! instance binds, so one template serves every variant.
//!
//! A game invariant reads the parameters too (story 79, ADR 0019 point 2): an instance of a
//! composition with a game invariant gets the field `<C>_params_<I>` in `<C>_side` when its
//! package has such a parameter, also without a package invariant ([`has_side_params`]). Then
//! the package declares `<P>_pkgparams` too ([`params_record_packages`]).

use crate::expressions::{Expression, ExpressionKind};
use crate::package::{Composition, Package, PackageInstance};
use crate::theorem::Theorem;
use crate::types::{Type, TypeKind};

use super::super::ast::{EcExpr, EcType};
use super::super::names::{NameKind, Names};
use super::super::package;
use super::super::types::{func_op_name, translate_type};
use super::super::EcExportError;

/// The record type of the parameters of `package`: `<P>_pkgparams`.
pub(crate) fn pkg_params_type_name(package: &str) -> String {
    format!("{package}_pkgparams")
}

/// The side-record field that holds the parameters of instance `instance`:
/// `<prefix>params_<I>` (`<C>_params_<I>` in `<C>_side`).
pub(crate) fn params_field_name(prefix: &str, instance: &str) -> String {
    format!("{prefix}params_{instance}")
}

/// One field of `<P>_pkgparams`.
pub(crate) struct PkgParamField {
    /// The parameter's Domino name.
    pub raw: String,
    /// `<P>_param_<mangled>`. The `_param_` keeps it apart from the `<P>_pkgstate` fields.
    pub field: String,
    pub ty: EcType,
    /// The module variable of a value parameter; `None` for a function parameter.
    pub var: Option<String>,
}

/// Whether the templates of `pkg` take `<P>_pkgparams`: it has a package invariant and a
/// parameter that [`pkg_param_fields`] keeps.
pub(crate) fn has_pkg_params(pkg: &Package) -> bool {
    !pkg.invariants.is_empty() && has_param_fields(pkg)
}

fn has_param_fields(pkg: &Package) -> bool {
    pkg.params
        .iter()
        .any(|(name, ty, _)| is_field(pkg, name, ty))
}

/// Whether `<C>_side` of `comp` has the field `<C>_params_<I>` for `inst`: the templates of its
/// package take the parameters ([`has_pkg_params`]), or `comp` has a game invariant and the
/// package a parameter that [`param_fields`] keeps (story 79).
pub(crate) fn has_side_params(comp: &Composition, inst: &PackageInstance) -> bool {
    has_pkg_params(&inst.pkg) || (!comp.invariants.is_empty() && has_param_fields(&inst.pkg))
}

/// The packages of `theorem` that declare `<P>_pkgparams`: each package with an instance that
/// [`has_side_params`] in a composition of the theorem.
pub(crate) fn params_record_packages(theorem: &Theorem<'_>) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for game in &theorem.instances {
        let comp = game.game();
        for inst in comp.pkgs.iter().filter(|i| has_side_params(comp, i)) {
            if !out.contains(&inst.pkg.name) {
                out.push(inst.pkg.name.clone());
            }
        }
    }
    out
}

/// Whether parameter `name` of `pkg` is a field of `<P>_pkgparams`: a function, or a value
/// that the variants keep in a module variable.
fn is_field(pkg: &Package, name: &str, ty: &Type) -> bool {
    matches!(ty.kind(), TypeKind::Fn(..)) || package::param_needs_var(pkg, name, ty)
}

/// The fields of `<P>_pkgparams` that the templates of `inst`'s package take, in declaration
/// order. Empty when the package has no package invariant or no such parameter.
pub(crate) fn pkg_param_fields(
    inst: &PackageInstance,
) -> Result<Vec<PkgParamField>, EcExportError> {
    if !has_pkg_params(&inst.pkg) {
        return Ok(Vec::new());
    }
    param_fields(inst)
}

/// The fields of `<P>_pkgparams` for `inst`'s package, in declaration order: empty when the
/// package has no such parameter. The names are mangled after the state fields, as in the
/// package's module.
pub(crate) fn param_fields(inst: &PackageInstance) -> Result<Vec<PkgParamField>, EcExportError> {
    let pkg = &inst.pkg;
    let mut names = Names::new();
    for (name, _, _) in &pkg.state {
        names.mangle(NameKind::Var, name)?;
    }
    let mut fields = Vec::new();
    for (name, ty, span) in &pkg.params {
        if !is_field(pkg, name, ty) {
            continue;
        }
        let is_fn = matches!(ty.kind(), TypeKind::Fn(..));
        let mangled = names.mangle(NameKind::Var, name)?;
        fields.push(PkgParamField {
            raw: name.clone(),
            field: format!("{}_param_{mangled}", pkg.name),
            ty: translate_type(ty, *span)?,
            var: (!is_fn).then_some(mangled),
        });
    }
    Ok(fields)
}

/// The `<P>_pkgparams` literal that the templates of `inst`'s package take, or `None` when
/// they take none ([`has_pkg_params`]). See [`params_lit`].
pub(crate) fn pkg_params_lit(
    inst: &PackageInstance,
    read_var: impl Fn(&str) -> EcExpr,
) -> Result<Option<EcExpr>, EcExportError> {
    if !has_pkg_params(&inst.pkg) {
        return Ok(None);
    }
    params_lit(inst, read_var)
}

/// The `<P>_pkgparams` literal of `inst` for the field `<C>_params_<I>` of `comp`'s side
/// record, or `None` when the record has no such field ([`has_side_params`]).
pub(crate) fn side_params_lit(
    comp: &Composition,
    inst: &PackageInstance,
    read_var: impl Fn(&str) -> EcExpr,
) -> Result<Option<EcExpr>, EcExportError> {
    if !has_side_params(comp, inst) {
        return Ok(None);
    }
    params_lit(inst, read_var)
}

/// The `<P>_pkgparams` literal of `inst`, or `None` when its package has no such parameter.
/// A value field is `read_var(<module variable>)`; a function field is `func_<c>` for the
/// theorem constant `c` that `inst` binds the parameter to. Panics when a function parameter
/// is not bound to a theorem constant: the only expressions of function type are identifiers.
fn params_lit(
    inst: &PackageInstance,
    read_var: impl Fn(&str) -> EcExpr,
) -> Result<Option<EcExpr>, EcExportError> {
    let fields = param_fields(inst)?;
    if fields.is_empty() {
        return Ok(None);
    }
    let fields = fields
        .into_iter()
        .map(|f| {
            let value = match &f.var {
                Some(var) => read_var(var),
                None => EcExpr::App {
                    head: func_op_name(&bound_theorem_const(inst, &f.raw)),
                    args: Vec::new(),
                },
            };
            (f.field, value)
        })
        .collect();
    Ok(Some(EcExpr::RecordLit { fields }))
}

fn bound_theorem_const(inst: &PackageInstance, param: &str) -> String {
    inst.params
        .iter()
        .find(|(id, _)| id.name == param)
        .and_then(|(_, expr)| theorem_const_of(expr))
        .unwrap_or_else(|| {
            panic!(
                "function parameter `{param}` of `{}` is not bound to a theorem constant",
                inst.name
            )
        })
}

/// The theorem constant that `expr` names, or `None` when it names none.
pub(crate) fn theorem_const_of(expr: &Expression) -> Option<String> {
    match expr.kind() {
        ExpressionKind::Identifier(id) => id.as_theorem_identifier().map(|id| id.ident()),
        _ => None,
    }
}

/// `template` applied to the params literal (when the package has a params record) and to
/// the state literal (when it has state), in that order.
pub(crate) fn template_app(
    template: &str,
    params: Option<EcExpr>,
    state: Option<EcExpr>,
) -> EcExpr {
    EcExpr::App {
        head: template.to_string(),
        args: params.into_iter().chain(state).collect(),
    }
}
