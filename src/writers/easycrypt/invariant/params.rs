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

use crate::package::{Package, PackageInstance};
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

/// Whether `pkg` has the record `<P>_pkgparams`: it has a package invariant and a parameter
/// that [`pkg_param_fields`] keeps.
pub(crate) fn has_pkg_params(pkg: &Package) -> bool {
    !pkg.invariants.is_empty()
        && pkg
            .params
            .iter()
            .any(|(name, ty, _)| is_field(pkg, name, ty))
}

/// Whether parameter `name` of `pkg` is a field of `<P>_pkgparams`: a function, or a value
/// that the variants keep in a module variable.
fn is_field(pkg: &Package, name: &str, ty: &Type) -> bool {
    matches!(ty.kind(), TypeKind::Fn(..)) || package::param_needs_var(pkg, name, ty)
}

/// The fields of `<P>_pkgparams` for `inst`'s package, in declaration order. Empty when the
/// package has no package invariant or no such parameter: then it has no record. The names
/// are mangled after the state fields, as in the package's module.
pub(crate) fn pkg_param_fields(
    inst: &PackageInstance,
) -> Result<Vec<PkgParamField>, EcExportError> {
    let pkg = &inst.pkg;
    if !has_pkg_params(pkg) {
        return Ok(Vec::new());
    }
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

/// The `<P>_pkgparams` literal of `inst`, or `None` when its package has no record. A value
/// field is `read_var(<module variable>)`; a function field is `func_<c>` for the theorem
/// constant `c` that `inst` binds the parameter to. Panics when a function parameter is not
/// bound to a theorem constant: the only expressions of function type are identifiers.
pub(crate) fn pkg_params_lit(
    inst: &PackageInstance,
    read_var: impl Fn(&str) -> EcExpr,
) -> Result<Option<EcExpr>, EcExportError> {
    let fields = pkg_param_fields(inst)?;
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
        .and_then(|(_, expr)| match expr.kind() {
            crate::expressions::ExpressionKind::Identifier(id) => id.as_theorem_identifier(),
            _ => None,
        })
        .map(|id| id.ident())
        .unwrap_or_else(|| {
            panic!(
                "function parameter `{param}` of `{}` is not bound to a theorem constant",
                inst.name
            )
        })
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
