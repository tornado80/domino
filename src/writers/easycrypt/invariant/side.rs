// SPDX-License-Identifier: MIT OR Apache-2.0

//! Side invariants (story 69, ADR 0014; before it story 58, ADR 0010): the package invariants
//! and the game invariant of a composition, stated one time for each composition.
//!
//! Each named invariant gets its own operator (story 73), with the names of ADR 0018:
//!
//! - A package invariant `<N>` becomes the template
//!   `PkgInv_<N>_of_<Pkg> (p : <Pkg>_pkgparams) (s : <Pkg>_pkgstate)`, in the file of the
//!   package, next to the record types of the package's parameters and state
//!   ([`package_items`]). Without parameters there is no `p` (story 78, [`super::params`]).
//! - A composition with a side invariant gets, in its own file, its side record `<C>_side`, a
//!   wrapper `PkgInv_<N>_of_<Inst>_in_<C>` for each package invariant of each instance, a
//!   `GameInv_<N>_of_<C>` for each game invariant, and `side_inv_<C>`, which joins them under
//!   `!abort` ([`composition_items`]). Each wrapper and game invariant stands for one Domino
//!   claim.
//!
//! A one-sided invariant file holds only invariant forms of the right kind.

use miette::Diagnostic;
use thiserror::Error;

use crate::package::{Composition, PackageInstance};
use crate::project::Project;
use crate::theorem::GameInstance;
use crate::types::{Type, TypeKind};
use crate::util::smtparser::SmtParser;
use crate::writers::easycrypt::ast::{EcBinop, EcExpr, EcItem, EcType, EcUnop};
use crate::writers::easycrypt::interfaces::composition_span;
use crate::writers::easycrypt::names::Names;
use crate::writers::easycrypt::types::{func_op_name, translate_type};
use crate::writers::easycrypt::EcExportError;

use super::params::{
    has_pkg_params, has_side_params, param_fields, params_field_name, pkg_param_fields,
    pkg_params_type_name, template_app, theorem_const_of, PkgParamField,
};
use super::{
    abort_field_name, field_expr, fold_and, game_inv_op_name, instance_field_name, pkg_inv_op_name,
    pkg_inv_template_name, pkg_state_fields, pkg_state_type_name, side_inv_op_name,
    side_record_type_name, InvariantError, Locals, OpRegistry, Sexp, StateLookup, TCtx,
};

/// A one-sided invariant file that does not hold exactly one invariant form of its kind.
#[derive(Debug, Clone, PartialEq, Eq, Error, Diagnostic)]
pub enum SideInvariantError {
    /// A form other than the one invariant form: a `define-fun`, `define-state-relation`,
    /// `define-lemma` or a bare top-level s-expression.
    #[error("invariant file `{file}` of {owner} may contain only one `{expected}`, but it contains `{form}`")]
    ForbiddenForm {
        file: String,
        owner: String,
        expected: &'static str,
        form: String,
    },

    /// A `define-game-invariant` in a package file, or the opposite.
    #[error("invariant file `{file}` of {owner} contains `{form}`, which is not permitted there")]
    WrongKind {
        file: String,
        owner: String,
        form: &'static str,
    },

    /// The invariant files of a package or composition hold no invariant form.
    #[error("the invariant files of {owner} ({}) contain no `{form}`", files.join(", "))]
    NoInvariant {
        files: Vec<String>,
        owner: String,
        form: &'static str,
    },

    /// A package invariant for a package without state fields: there is no `<Pkg>_pkgstate`.
    #[error(
        "invariant file `{file}` gives an invariant to package `{package}`, which has no state"
    )]
    StatelessPackageInvariant { file: String, package: String },

    /// Two operators of a composition's file with one name, for example the template of a
    /// package `H6_Prf` and the wrapper of instance `Prf` of composition `H6`.
    #[error("{a} and {b} both become the operator `{name}`")]
    OpNameCollision { name: String, a: String, b: String },

    /// A one-sided invariant form in an equivalence's invariant file. Domino rejects it there.
    #[error("invariant file `{file}` of an equivalence contains `{form}`, which is permitted only in a package or composition invariant file")]
    InEquivalenceFile { file: String, form: &'static str },
}

/// The kind of a one-sided invariant form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Kind {
    Package,
    Game,
}

impl Kind {
    pub(super) fn form(self) -> &'static str {
        match self {
            Kind::Package => "define-package-invariant",
            Kind::Game => "define-game-invariant",
        }
    }
}

/// A statement of a one-sided file: an invariant form (kept by the parser), or a bare
/// s-expression.
enum SideStmt {
    Form,
    Bare(Sexp),
}

impl From<Sexp> for SideStmt {
    fn from(s: Sexp) -> Self {
        SideStmt::Bare(s)
    }
}

/// Parses one one-sided file: keeps its invariant forms, and refuses all other forms.
struct SideFileParser {
    file: String,
    owner: String,
    expected: Kind,
    forms: Vec<(Kind, String, Sexp)>,
}

impl SideFileParser {
    fn forbidden(&self, form: String) -> InvariantError {
        SideInvariantError::ForbiddenForm {
            file: self.file.clone(),
            owner: self.owner.clone(),
            expected: self.expected.form(),
            form,
        }
        .into()
    }
}

impl SmtParser<InvariantError> for SideFileParser {
    type Expr = Sexp;
    type Stmt = SideStmt;

    fn handle_atom(&mut self, content: &str) -> Result<Sexp, InvariantError> {
        Ok(Sexp::Atom(content.to_string()))
    }

    fn handle_list(&mut self, content: Vec<Sexp>) -> Result<Sexp, InvariantError> {
        Ok(Sexp::List(content))
    }

    fn handle_sexp(&mut self, parsed: SideStmt) -> Result<(), InvariantError> {
        match parsed {
            SideStmt::Form => Ok(()),
            SideStmt::Bare(s) => Err(self.forbidden(s.to_string())),
        }
    }

    fn handle_define_package_invariant(
        &mut self,
        invname: &str,
        body: Sexp,
    ) -> Result<SideStmt, InvariantError> {
        self.forms.push((Kind::Package, invname.to_string(), body));
        Ok(SideStmt::Form)
    }

    fn handle_define_game_invariant(
        &mut self,
        invname: &str,
        body: Sexp,
    ) -> Result<SideStmt, InvariantError> {
        self.forms.push((Kind::Game, invname.to_string(), body));
        Ok(SideStmt::Form)
    }

    fn handle_definefun(
        &mut self,
        funname: &str,
        _args: Vec<Sexp>,
        _ty: &str,
        _body: Sexp,
    ) -> Result<SideStmt, InvariantError> {
        Err(self.forbidden(format!("define-fun {funname}")))
    }

    fn handle_define_state_relation(
        &mut self,
        funname: &str,
        _args: Vec<Sexp>,
        _body: Sexp,
    ) -> Result<SideStmt, InvariantError> {
        Err(self.forbidden(format!("define-state-relation {funname}")))
    }

    fn handle_define_lemma(
        &mut self,
        lemma_name: &str,
        oracle_name: &str,
        _args: Vec<Sexp>,
        _body: Sexp,
    ) -> Result<SideStmt, InvariantError> {
        Err(self.forbidden(format!("define-lemma {lemma_name} {oracle_name}")))
    }
}

/// One named invariant of an owner: its Domino name, the file that declares it, and its body.
pub(super) struct NamedInvariant {
    pub name: String,
    pub file: String,
    pub body: Sexp,
}

/// The named invariants of kind `kind` across `files`, in file and source order (story 71).
/// Each gets its own operator (story 73, ADR 0018). No invariant is
/// [`SideInvariantError::NoInvariant`].
pub(super) fn named_invariants(
    project: &impl Project,
    files: &[String],
    owner: &str,
    kind: Kind,
) -> Result<Vec<NamedInvariant>, InvariantError> {
    let mut found = Vec::new();
    for file in files {
        let contents = project
            .read_input_file(file)
            .map_err(|err| InvariantError::Io {
                file: file.clone(),
                message: err.to_string(),
            })?;
        let mut parser = SideFileParser {
            file: file.clone(),
            owner: owner.to_string(),
            expected: kind,
            forms: Vec::new(),
        };
        parser.parse_stmts(&contents)?;
        for (form_kind, name, body) in parser.forms {
            check_form(file, owner, kind, form_kind)?;
            found.push(NamedInvariant {
                name,
                file: file.clone(),
                body,
            });
        }
    }
    if found.is_empty() {
        return Err(SideInvariantError::NoInvariant {
            files: files.to_vec(),
            owner: owner.to_string(),
            form: kind.form(),
        }
        .into());
    }
    Ok(found)
}

/// The names of the package invariants of `inst`'s package.
pub(super) fn package_invariant_names(
    project: &impl Project,
    inst: &PackageInstance,
) -> Result<Vec<String>, InvariantError> {
    let owner = format!("package `{}`", inst.pkg.name);
    Ok(
        named_invariants(project, &inst.pkg.invariants, &owner, Kind::Package)?
            .into_iter()
            .map(|i| i.name)
            .collect(),
    )
}

/// The names of the game invariants of `comp`, empty when it has none.
pub(crate) fn game_invariant_names(
    project: &impl Project,
    comp: &Composition,
) -> Result<Vec<String>, InvariantError> {
    if comp.invariants.is_empty() {
        return Ok(Vec::new());
    }
    let owner = format!("composition `{}`", comp.name);
    Ok(
        named_invariants(project, &comp.invariants, &owner, Kind::Game)?
            .into_iter()
            .map(|i| i.name)
            .collect(),
    )
}

fn check_form(file: &str, owner: &str, want: Kind, got: Kind) -> Result<(), SideInvariantError> {
    if got != want {
        return Err(SideInvariantError::WrongKind {
            file: file.to_string(),
            owner: owner.to_string(),
            form: got.form(),
        });
    }
    Ok(())
}

/// What the translation of a one-sided invariant reads: the theorem's constants and the
/// project's files.
pub(crate) struct SideCtx<'a, P: Project> {
    pub theorem_consts: &'a [(String, Type)],
    pub project: &'a P,
    /// The packages that declare `<P>_pkgparams` ([`super::params::params_record_packages`]).
    pub params_records: Vec<String>,
}

/// What the file of a package declares for the side invariants (story 69, ADR 0014): the
/// record type of the package's state, `<Pkg>_pkgstate`, when it has state, the record type of
/// its parameters, `<Pkg>_pkgparams`, when it has one (story 78, [`pkg_param_fields`]), then
/// the template of each of its package invariants, `PkgInv_<N>_of_<Pkg>`. `inst` is any
/// instance of the package. A package invariant of a package with neither state nor such
/// parameters is [`SideInvariantError::StatelessPackageInvariant`]; a params field with the
/// name of a state field is [`InvariantError::FieldCollision`].
pub(crate) fn package_items<P: Project>(
    inst: &PackageInstance,
    ctx: &SideCtx<'_, P>,
) -> Result<Vec<EcItem>, EcExportError> {
    let package = inst.pkg.name.as_str();
    let fields = pkg_state_fields(inst, &mut Names::new())?;
    let mut items = Vec::new();
    if !fields.is_empty() {
        items.push(EcItem::Record {
            name: pkg_state_type_name(package),
            fields: fields
                .iter()
                .map(|(_, f, ty)| (f.clone(), ty.clone()))
                .collect(),
        });
    }
    let params = if ctx.params_records.contains(&inst.pkg.name) {
        param_fields(inst)?
    } else {
        Vec::new()
    };
    if let Some(dup) = params
        .iter()
        .find(|p| fields.iter().any(|(_, f, _)| *f == p.field))
    {
        return Err(InvariantError::FieldCollision {
            field: dup.field.clone(),
        }
        .into());
    }
    if !params.is_empty() {
        items.push(EcItem::Record {
            name: pkg_params_type_name(package),
            fields: params.into_iter().map(|p| (p.field, p.ty)).collect(),
        });
    }
    if !inst.pkg.invariants.is_empty() {
        items.extend(package_templates(inst, ctx)?);
    }
    Ok(items)
}

/// Whether `comp` has a side invariant: a package invariant of one of its packages, or a game
/// invariant of its own.
pub(crate) fn has_side_invariants(comp: &Composition) -> bool {
    !comp.invariants.is_empty() || !invariant_instances(comp).is_empty()
}

/// What the file of the composition of `game` declares for its side invariants (story 69,
/// ADR 0014), or `None` when it has none ([`has_side_invariants`]). `game` is the first game
/// instance of the composition: its function constants are the ones that `Comp_<C>` uses. `name` is the composition's name in
/// EasyCrypt (`Comp_<name>.ec`). In order:
///
/// - the side record `<name>_side`: a field `<name>_pkg_<Inst> : <Pkg>_pkgstate` for each
///   instance with state, then a field `<name>_params_<Inst> : <Pkg>_pkgparams` for each
///   instance that [`has_side_params`] (stories 78, 79), both in `ordered_pkgs_idx()`
///   order, then `<name>_abort_flag : bool`;
/// - `PkgInv_<N>_of_<Inst>_in_<name> (s : <name>_side)` for each package invariant `<N>` of
///   each instance: one Domino claim each;
/// - `GameInv_<N>_of_<name> (g : <name>_side)` for each game invariant `<N>`;
/// - `side_inv_<name> s = !s.<abort> => PkgInv_… s /\ … /\ GameInv_<name> s`;
/// - with package and game invariants both, `pkg_inv_<name>` and `game_inv_<name>`, the two
///   parts of `side_inv_<name>` alone (story 77).
///
/// The `<Pkg>_pkgstate` types and `PkgInv_<N>_of_<Pkg>` templates come from the package files
/// ([`package_items`]), which the composition file imports. An operator of the composition
/// with the name of a template is [`SideInvariantError::OpNameCollision`]; a field of the side
/// record with the name of a package state field is [`InvariantError::FieldCollision`].
pub(crate) fn composition_items<P: Project>(
    game: &GameInstance,
    name: &str,
    ctx: &SideCtx<'_, P>,
) -> Result<Option<Vec<EcItem>>, EcExportError> {
    let comp = game.game();
    if !has_side_invariants(comp) {
        return Ok(None);
    }
    let prefix = format!("{name}_");
    let record_ty = EcType::Named(side_record_type_name(name));
    let mut ops = OpRegistry::default();
    let (fields, abort) = side_record_fields(comp, &prefix)?;
    let mut items = vec![EcItem::Record {
        name: side_record_type_name(name),
        fields,
    }];
    let mut pkg_conjuncts = Vec::new();
    for inst in invariant_instances(comp) {
        for invariant in package_invariant_names(ctx.project, inst)? {
            let template = pkg_inv_template_name(&invariant, &inst.pkg.name);
            ops.define_named(
                &template,
                &format!("the package invariant `{invariant}` of `{}`", inst.pkg.name),
            )?;
            let op = pkg_inv_op_name(&invariant, name, inst.name());
            ops.define_named(
                &op,
                &format!(
                    "the package invariant `{invariant}` of instance `{}`",
                    inst.name()
                ),
            )?;
            let body = wrapper_body(inst, &prefix, &template);
            items.push(op_def(&op, "s", record_ty.clone(), body));
            pkg_conjuncts.push(apply(&op, "s"));
        }
    }
    let mut game_conjuncts = Vec::new();
    if !comp.invariants.is_empty() {
        let owner = format!("composition `{}`", comp.name);
        let lookup = game_lookup(game, &prefix)?;
        for invariant in named_invariants(ctx.project, &comp.invariants, &owner, Kind::Game)? {
            let op = game_inv_op_name(&invariant.name, name);
            ops.define_named(
                &op,
                &format!("the game invariant `{}` of `{}`", invariant.name, comp.name),
            )?;
            let body = translate(ctx, &invariant.file, &lookup, &invariant.body)?;
            items.push(op_def(&op, "g", record_ty.clone(), body));
            game_conjuncts.push(apply(&op, "s"));
        }
    }
    let guarded = |conjuncts: Vec<EcExpr>| EcExpr::Binop {
        op: EcBinop::Implies,
        lhs: Box::new(EcExpr::Unop {
            op: EcUnop::Not,
            arg: Box::new(field_expr("s", &abort)),
        }),
        rhs: Box::new(fold_and(conjuncts)),
    };
    let op = side_inv_op_name(name);
    ops.define_named(&op, &format!("the side invariant of `{}`", comp.name))?;
    let all = pkg_conjuncts
        .iter()
        .chain(&game_conjuncts)
        .cloned()
        .collect();
    items.push(op_def(&op, "s", record_ty.clone(), guarded(all)));
    // story 77: `SideInv_<C>_<O>` proves the two parts apart, the package invariants from the
    // package lemmas and the game invariants along the side tree
    if !pkg_conjuncts.is_empty() && !game_conjuncts.is_empty() {
        for (op, part, conjuncts) in [
            (pkg_side_inv_op_name(name), "package", pkg_conjuncts),
            (game_side_inv_op_name(name), "game", game_conjuncts),
        ] {
            ops.define_named(&op, &format!("the {part} invariants of `{}`", comp.name))?;
            items.push(op_def(&op, "s", record_ty.clone(), guarded(conjuncts)));
        }
    }
    Ok(Some(items))
}

/// The fields of the side record `<C>_side` (see [`composition_items`]) and the name of its
/// abort field. A field with the name of a field of a package's state or params record is
/// [`InvariantError::FieldCollision`].
fn side_record_fields(
    comp: &Composition,
    prefix: &str,
) -> Result<(Vec<(String, EcType)>, String), EcExportError> {
    let mut fields = Vec::new();
    let mut seen_fields: Vec<String> = Vec::new();
    for &idx in &comp.ordered_pkgs_idx() {
        let inst = &comp.pkgs[idx];
        let state = pkg_state_fields(inst, &mut Names::new())?;
        if state.is_empty() {
            continue;
        }
        seen_fields.extend(state.into_iter().map(|(_, f, _)| f));
        fields.push((
            instance_field_name(prefix, inst.name()),
            EcType::Named(pkg_state_type_name(&inst.pkg.name)),
        ));
    }
    for &idx in &comp.ordered_pkgs_idx() {
        let inst = &comp.pkgs[idx];
        if has_side_params(comp, inst) {
            seen_fields.extend(param_fields(inst)?.into_iter().map(|p| p.field));
            fields.push((
                params_field_name(prefix, inst.name()),
                EcType::Named(pkg_params_type_name(&inst.pkg.name)),
            ));
        }
    }
    let abort = abort_field_name(prefix);
    fields.push((abort.clone(), EcType::Bool));
    for (field, _) in &fields {
        if seen_fields.contains(field) {
            return Err(InvariantError::FieldCollision {
                field: field.clone(),
            }
            .into());
        }
        seen_fields.push(field.clone());
    }
    Ok((fields, abort))
}

/// The body of a wrapper: the template applied to the instance's fields of the side record,
/// ``s.`<C>_params_<I>`` when its package has parameters and ``s.`<C>_pkg_<I>`` when it has
/// state.
fn wrapper_body(inst: &PackageInstance, prefix: &str, template: &str) -> EcExpr {
    let params =
        has_pkg_params(&inst.pkg).then(|| field_expr("s", &params_field_name(prefix, inst.name())));
    let state = (!inst.pkg.state.is_empty())
        .then(|| field_expr("s", &instance_field_name(prefix, inst.name())));
    template_app(template, params, state)
}

/// `pkg_inv_<C>`: the package invariants of the instances of composition `<C>`, under
/// `!abort`, when it also has game invariants (story 77).
pub(crate) fn pkg_side_inv_op_name(comp: &str) -> String {
    format!("pkg_inv_{comp}")
}

/// `game_inv_<C>`: the game invariants of composition `<C>`, under `!abort`, when it also has
/// package invariants (story 77). The side tree checks these only.
pub(crate) fn game_side_inv_op_name(comp: &str) -> String {
    format!("game_inv_{comp}")
}

/// The package instances of `comp` that have a package invariant, in `ordered_pkgs_idx()`
/// order.
pub(crate) fn invariant_instances(comp: &Composition) -> Vec<&PackageInstance> {
    comp.ordered_pkgs_idx()
        .into_iter()
        .map(|idx| &comp.pkgs[idx])
        .filter(|inst| !inst.pkg.invariants.is_empty())
        .collect()
}

fn apply(op: &str, arg: &str) -> EcExpr {
    EcExpr::App {
        head: op.to_string(),
        args: vec![EcExpr::Var(arg.to_string())],
    }
}

/// `op PkgInv_<N>_of_<Pkg> (p : <Pkg>_pkgparams) (s : <Pkg>_pkgstate) : bool = <body>.`, one
/// for each named package invariant `<N>` of the package; without a params record no `p`,
/// without state no `s` ([`template_args`]). Two names that become one operator are
/// [`SideInvariantError::OpNameCollision`].
fn package_templates<P: Project>(
    inst: &PackageInstance,
    ctx: &SideCtx<'_, P>,
) -> Result<Vec<EcItem>, EcExportError> {
    let package = inst.pkg.name.as_str();
    let owner = format!("package `{package}`");
    let invariants = named_invariants(ctx.project, &inst.pkg.invariants, &owner, Kind::Package)?;
    let fields = pkg_state_fields(inst, &mut Names::new())?;
    let params = pkg_param_fields(inst)?;
    if fields.is_empty() && params.is_empty() {
        return Err(
            InvariantError::from(SideInvariantError::StatelessPackageInvariant {
                file: invariants[0].file.clone(),
                package: package.to_string(),
            })
            .into(),
        );
    }
    let args = template_args(package, &params, &fields);
    let mut lookup = StateLookup::default();
    for (raw, field, ty) in fields {
        let projection = field_expr("s", &field);
        lookup.fields.insert(format!("pkg.{raw}"), (projection, ty));
    }
    for PkgParamField { raw, field, ty, .. } in params {
        let projection = field_expr("p", &field);
        lookup.fields.insert(format!("pkg.{raw}"), (projection, ty));
    }
    let mut ops = OpRegistry::default();
    let mut items = Vec::new();
    for invariant in invariants {
        let op = pkg_inv_template_name(&invariant.name, package);
        ops.define_named(
            &op,
            &format!("the package invariant `{}` of `{package}`", invariant.name),
        )?;
        let body = translate(ctx, &invariant.file, &lookup, &invariant.body)?;
        items.push(EcItem::OpDef {
            name: op,
            args: args.clone(),
            ret: Some(EcType::Bool),
            body,
        });
    }
    Ok(items)
}

/// The arguments of a template: `(p : <Pkg>_pkgparams)` when `params` is not empty, then
/// `(s : <Pkg>_pkgstate)` when `state` is not empty.
fn template_args(
    package: &str,
    params: &[PkgParamField],
    state: &[(String, String, EcType)],
) -> Vec<(String, EcType)> {
    let p = (!params.is_empty()).then(|| {
        (
            "p".to_string(),
            EcType::Named(pkg_params_type_name(package)),
        )
    });
    let s =
        (!state.is_empty()).then(|| ("s".to_string(), EcType::Named(pkg_state_type_name(package))));
    p.into_iter().chain(s).collect()
}

/// The atoms of a game invariant of the composition of `game`:
///
/// - `game.<Inst>.<field>` -> ``g.`<prefix>pkg_<Inst>.`<Pkg>_<field>``, for every state field;
/// - `game.<Inst>.<param>` -> ``g.`<prefix>params_<Inst>.`<Pkg>_param_<param>``, for every
///   field of `<Pkg>_pkgparams` (story 79);
/// - `game.<f>` -> `func_<c>`, for every function constant `f` that `game` binds to the theorem
///   constant `c` (story 79). A value constant is not here.
fn game_lookup(game: &GameInstance, prefix: &str) -> Result<StateLookup, EcExportError> {
    let comp = game.game();
    let mut lookup = state_lookup(comp, prefix)?;
    for inst in comp.pkgs.iter().filter(|i| has_side_params(comp, i)) {
        let params = field_expr("g", &params_field_name(prefix, inst.name()));
        for PkgParamField { raw, field, ty, .. } in param_fields(inst)? {
            let projection = EcExpr::Field {
                expr: Box::new(params.clone()),
                field,
            };
            lookup
                .fields
                .insert(format!("game.{}.{raw}", inst.name()), (projection, ty));
        }
    }
    for (ident, expr) in &game.consts {
        if !matches!(ident.ty.kind(), TypeKind::Fn(..)) {
            continue;
        }
        let constant =
            theorem_const_of(expr).expect("the only expressions of function type are identifiers");
        let op = EcExpr::App {
            head: func_op_name(&constant),
            args: Vec::new(),
        };
        let ty = translate_type(&ident.ty, composition_span(comp))?;
        lookup
            .fields
            .insert(format!("game.{}", ident.name), (op, ty));
    }
    Ok(lookup)
}

/// `game.<Inst>.<field>` -> ``g.`<prefix>pkg_<Inst>.`<Pkg>_<field>``, for every state field.
fn state_lookup(comp: &Composition, prefix: &str) -> Result<StateLookup, EcExportError> {
    let mut lookup = StateLookup::default();
    for inst in &comp.pkgs {
        let inst_field = instance_field_name(prefix, inst.name());
        for (raw, field, ty) in pkg_state_fields(inst, &mut Names::new())? {
            let projection = EcExpr::Field {
                expr: Box::new(field_expr("g", &inst_field)),
                field,
            };
            lookup
                .fields
                .insert(format!("game.{}.{raw}", inst.name()), (projection, ty));
        }
    }
    Ok(lookup)
}

fn translate<P: Project>(
    ctx: &SideCtx<'_, P>,
    file: &str,
    lookup: &StateLookup,
    body: &Sexp,
) -> Result<EcExpr, InvariantError> {
    let no_ops = OpRegistry::default();
    let mut tctx = TCtx {
        file: file.to_string(),
        lookup,
        // a one-sided body names no `left`/`right` state
        left_record_ty: EcType::Bool,
        right_record_ty: EcType::Bool,
        theorem_consts: ctx.theorem_consts,
        ops: &no_ops,
        local_names: Names::new(),
    };
    Ok(tctx.translate(body, &Locals::new())?.0)
}

fn op_def(name: &str, param: &str, ty: EcType, body: EcExpr) -> EcItem {
    EcItem::OpDef {
        name: name.to_string(),
        args: vec![(param.to_string(), ty)],
        ret: Some(EcType::Bool),
        body,
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::super::tests::{find_equivalence, item_text, load_project};
    use super::super::{
        build_invariant_file, invariant_ops, leaf_part_ops, side_invariant_ops, OpRegistry,
    };
    use super::*;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::writers::easycrypt::export::{export_theorem, ExportedTheorem};

    const STORY58: &str = "testdata/easycrypt/story58";
    const STORY69: &str = "testdata/easycrypt/story69";
    const PARAMS: &str = "test-projects/test-package-invariant-params";
    const GAME_PARAMS: &str = "test-projects/test-game-invariant-params";

    fn export(dir: &str, theorem: &str) -> Result<ExportedTheorem, EcExportError> {
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let theorem = project.get_theorem(theorem).unwrap();
        export_theorem(theorem, &project)
    }

    fn file<'a>(exported: &'a ExportedTheorem, name: &str) -> &'a str {
        exported
            .files
            .get(Path::new(name))
            .unwrap_or_else(|| panic!("no `{name}` in the export"))
    }

    fn error_of(theorem: &str) -> String {
        match export(STORY58, theorem) {
            Ok(_) => panic!("the theorem exports"),
            Err(e) => e.to_string(),
        }
    }

    fn count(text: &str, needle: &str) -> usize {
        text.matches(needle).count()
    }

    fn golden(rendered: &str, path: &str) {
        let path = format!("{}/{path}", env!("CARGO_MANIFEST_DIR"));
        let expected = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read golden file {path}: {e}"));
        assert_eq!(rendered, expected, "rendered != {path}");
    }

    /// Symbolic-execution story 21: the tactics run takes its state relations from the
    /// invariant file, and the unfold list still holds `StateRelation_invariant`.
    #[test]
    fn the_unfold_list_from_the_invariant_files_relations_holds_state_relation_invariant() {
        let (theorem, project) = load_project("example-projects/4WHS", "Simple4WHS");
        let equivalence = find_equivalence(&theorem, "Hybrid1", "Hybrid2");
        let file = build_invariant_file(&theorem, equivalence, project).unwrap();
        assert!(
            file.state_relations.iter().any(|r| r == "invariant"),
            "{:?}",
            file.state_relations
        );
        let left = theorem.find_game_instance("Hybrid1").unwrap();
        let right = theorem.find_game_instance("Hybrid2").unwrap();
        let ops: Vec<String> =
            invariant_ops(project, left, right, &file.state_relations, &file.helpers)
                .unwrap()
                .into_iter()
                .map(|op| op.name)
                .collect();
        assert!(
            ops.iter().any(|op| op == "StateRelation_invariant"),
            "{ops:?}"
        );
    }

    /// Story 69: the package file declares the state type and the template, the composition
    /// file the side record, the wrapper, the game invariant and `side_inv`; the invariant file
    /// of the equivalence none of them.
    #[test]
    fn hybrid1_hybrid2_side_invariants_are_in_the_package_and_composition_files() {
        let exported = export("example-projects/4WHS", "Simple4WHS").unwrap();
        let pkg = file(&exported, "Pkg_PRF.ec");
        for item in ["type PRF_pkgstate = {", "op PkgInv_main_of_PRF "] {
            assert_eq!(count(pkg, item), 1, "{item} in:\n{pkg}");
        }
        let comp = file(&exported, "Comp_Hybrid2.ec");
        for item in [
            "type Hybrid2_side = {",
            "op PkgInv_main_of_Prf_in_Hybrid2 ",
            "op GameInv_main_of_Hybrid2 ",
            "op side_inv_Hybrid2 ",
        ] {
            assert_eq!(count(comp, item), 1, "{item} in:\n{comp}");
        }
        // story 79: the game invariant can read the parameters of `Prot` too
        assert!(
            comp.contains("\nrequire import Pkg_PRF Pkg_Prot_NoPrf Pkg_KX_NoPrf.\n"),
            "{comp}"
        );
        assert_eq!(
            item_text(comp, "op side_inv_Hybrid2"),
            concat!(
                "op side_inv_Hybrid2 (s : Hybrid2_side) : bool =\n",
                "     !s.`Hybrid2_abort_flag\n",
                "  =>    PkgInv_main_of_Prf_in_Hybrid2 s\n",
                "     /\\ GameInv_main_of_Hybrid2 s."
            )
        );
        // Hybrid1 has no side invariant
        assert!(!file(&exported, "Comp_Hybrid1.ec").contains("side_inv"));
        let inv = file(&exported, "Eq_Hybrid1_Hybrid2_Invariants.ec");
        for gone in ["PkgInv_", "GameInv_", "type PRF_pkgstate"] {
            assert_eq!(count(inv, gone), 0, "{gone} in:\n{inv}");
        }
        assert!(
            item_text(inv, "op inv").ends_with("=> StateRelation_invariant l r)."),
            "{inv}"
        );
        golden(
            inv,
            &format!("{STORY58}/4WHS/Eq_Hybrid1_Hybrid2_Invariants.ec"),
        );
    }

    #[test]
    fn the_prf_body_is_in_the_package_file_only() {
        let exported = export("example-projects/4WHS", "Simple4WHS").unwrap();
        let with_body: Vec<&PathBuf> = exported
            .files
            .iter()
            .filter(|(_, text)| text.contains("kid <= 0"))
            .map(|(name, _)| name)
            .collect();
        assert_eq!(with_body, [Path::new("Pkg_PRF.ec")]);
        golden(
            file(&exported, "Eq_Real_Hybrid3_Ideal_Hybrid3_Invariants.ec"),
            &format!("{STORY58}/4WHS/Eq_Real_Hybrid3_Ideal_Hybrid3_Invariants.ec"),
        );
    }

    /// The side-invariant lemma files of `OneSided`, the oracle lemma and the glue.
    #[test]
    fn the_one_sided_theorem_gets_side_invariant_lemmas_assumed_by_the_oracle_lemma() {
        let exported = export(STORY58, "OneSided").unwrap();
        for name in [
            "Comp_Game.ec",
            "SideInv_Game_Inc.ec",
            "SideInv_Game.ec",
            "Eq_L_R_Inc.ec",
            "Eq_L_R.ec",
            "Eq_L_R_Invariants.ec",
        ] {
            golden(file(&exported, name), &format!("{STORY69}/OneSided/{name}"));
        }
        let side = &exported.side_invariants;
        assert_eq!(side.len(), 1);
        assert_eq!(side[0].composition, "Game");
        assert_eq!(side[0].join_file, "SideInv_Game.ec");
        assert_eq!(
            side[0].oracle_files,
            [("Inc".to_string(), "SideInv_Game_Inc.ec".to_string())]
        );
        assert_eq!(exported.equivalences[0].side_compositions, ["Game"]);
    }

    #[test]
    fn a_helper_define_fun_is_a_hard_error_naming_the_file() {
        let e = error_of("HelperFun");
        assert!(
            e.contains("`./packages/Helper.smt2`") && e.contains("define-fun nonneg"),
            "{e}"
        );
    }

    /// Story 73: each named invariant of an owner has its own template and wrapper, and
    /// `side_inv` joins both wrappers.
    #[test]
    fn two_named_invariants_of_a_package_are_two_templates_and_two_wrappers() {
        let exported = export(STORY58, "TwoForms").unwrap();
        let pkg = file(&exported, "Pkg_Two.ec");
        for op in ["op PkgInv_main_of_Two ", "op PkgInv_nonneg_of_Two "] {
            assert_eq!(count(pkg, op), 1, "{op} in:\n{pkg}");
        }
        let comp = file(&exported, "Comp_TwoGame.ec");
        for op in [
            "op PkgInv_main_of_T_in_TwoGame ",
            "op PkgInv_nonneg_of_T_in_TwoGame ",
        ] {
            assert_eq!(count(comp, op), 1, "{op} in:\n{comp}");
        }
        let side = item_text(comp, "op side_inv_TwoGame");
        assert!(
            side.contains("PkgInv_main_of_T_in_TwoGame s")
                && side.contains("PkgInv_nonneg_of_T_in_TwoGame s"),
            "{side}"
        );
    }

    /// Story 73: each wrapper stands for the claim of its own name.
    #[test]
    fn each_wrapper_stands_for_the_claim_of_its_name() {
        let (theorem, project) = load_project(STORY58, "TwoForms");
        let comp = theorem.find_game_instance("L").unwrap().game();
        let claims: Vec<(String, String)> = side_invariant_ops(project, comp)
            .unwrap()
            .into_iter()
            .filter_map(|o| Some((o.name, o.claim?)))
            .collect();
        assert_eq!(
            claims,
            [
                (
                    "Comp_TwoGame.PkgInv_main_of_T_in_TwoGame".to_string(),
                    "package-invariant!main!TwoGame-T!".to_string()
                ),
                (
                    "Comp_TwoGame.PkgInv_nonneg_of_T_in_TwoGame".to_string(),
                    "package-invariant!nonneg!TwoGame-T!".to_string()
                ),
            ]
        );
    }

    /// Story 73, ADR 0018: package `A_B` with invariant `c` and package `A` with invariant
    /// `B_c` give two templates and two wrappers, and translation succeeds.
    #[test]
    fn a_b_with_c_and_a_with_b_c_give_different_operators() {
        let exported = export(STORY58, "Clash").unwrap();
        assert_eq!(
            count(file(&exported, "Pkg_A_B.ec"), "op PkgInv_c_of_A__B "),
            1
        );
        assert_eq!(
            count(file(&exported, "Pkg_A.ec"), "op PkgInv_B__c_of_A "),
            1
        );
        let comp = file(&exported, "Comp_ClashGame.ec");
        for op in [
            "op PkgInv_c_of_A__B_in_ClashGame ",
            "op PkgInv_B__c_of_A_in_ClashGame ",
        ] {
            assert_eq!(count(comp, op), 1, "{op} in:\n{comp}");
        }
    }

    #[test]
    fn a_form_of_the_wrong_kind_is_a_hard_error_naming_the_file() {
        let e = error_of("WrongKind");
        assert!(
            e.contains("`./packages/Wrong.smt2`") && e.contains("define-game-invariant"),
            "{e}"
        );
    }

    #[test]
    fn a_package_invariant_of_a_stateless_package_is_a_hard_error_naming_the_file() {
        let e = error_of("Stateless");
        assert!(
            e.contains("`./packages/NoState.smt2`") && e.contains("no state"),
            "{e}"
        );
    }

    #[test]
    fn a_package_invariant_in_an_equivalence_file_is_a_hard_error_naming_the_file() {
        let e = error_of("InEquivalence");
        assert!(
            e.contains("`./theorem/invariant-with-package-invariant.smt2`")
                && e.contains("define-package-invariant"),
            "{e}"
        );
    }

    #[test]
    fn a_wrapper_with_the_name_of_a_template_is_a_hard_error() {
        let mut ops = OpRegistry::default();
        ops.define_named("PkgInv_H6_Prf", "the package invariant of `H6_Prf`")
            .unwrap();
        // the same operator again is not a collision
        ops.define_named("PkgInv_H6_Prf", "the package invariant of `H6_Prf`")
            .unwrap();
        let err = ops
            .define_named("PkgInv_H6_Prf", "the package invariant of instance `Prf`")
            .unwrap_err();
        assert!(
            matches!(
                &err,
                InvariantError::Side(SideInvariantError::OpNameCollision { name, .. })
                    if name == "PkgInv_H6_Prf"
            ),
            "{err:?}"
        );
    }

    /// Story 69: the name rule rejects two side-invariant lemma files with one name, and names
    /// both owners.
    #[test]
    fn the_name_rule_rejects_composition_a_oracle_b_x_against_composition_a_b_oracle_x() {
        let e = export(STORY69, "Collide").unwrap_err();
        assert!(
            matches!(&e, EcExportError::LemmaFileCollision { file, .. } if file == "SideInv_A_B_x.ec"),
            "{e:?}"
        );
        let text = e.to_string();
        assert!(
            text.contains("oracle `x` of composition `A_B`")
                && text.contains("oracle `B_x` of composition `A`"),
            "{text}"
        );
    }

    /// Story 62: `relations` and `helpers` come in call order (the invariant file gives them
    /// so); `invariant_ops` keeps that order. Story 69: the side invariant operators of the
    /// one composition of both sides follow, once, as premises only (no claim).
    #[test]
    fn invariant_ops_name_the_operators_in_unfold_order() {
        let (theorem, project) = load_project("example-projects/4WHS", "Simple4WHS");
        let left = theorem.find_game_instance("Real_Hybrid3").unwrap();
        let right = theorem.find_game_instance("Ideal_Hybrid3").unwrap();
        let ops = invariant_ops(
            project,
            left,
            right,
            &[
                "invariant".to_string(),
                "relation-a-b".to_string(),
                "state=".to_string(),
            ],
            &["eq-prf".to_string()],
        )
        .unwrap();
        let rows: Vec<(&str, Option<&str>, Option<&str>)> = ops
            .iter()
            .map(|o| (o.name.as_str(), o.claim.as_deref(), o.relation.as_deref()))
            .collect();
        assert_eq!(
            rows,
            [
                ("inv", None, None),
                ("params_inv", None, None),
                ("StateRelation_invariant", None, Some("invariant")),
                ("StateRelation_relation_a_b", None, Some("relation-a-b")),
                ("StateRelation_state_eq", None, Some("state=")),
                ("Helper_eq_prf", None, None),
                ("Comp_Hybrid2.side_inv_Hybrid2", None, None),
                ("Comp_Hybrid2.PkgInv_main_of_Prf_in_Hybrid2", None, None),
                ("PkgInv_main_of_PRF", None, None),
                ("Comp_Hybrid2.GameInv_main_of_Hybrid2", None, None),
            ]
        );
        assert_eq!(
            leaf_part_ops(project, left, right, &[], &[]).unwrap().len(),
            4
        );
    }

    /// Story 69: in the side-invariant job, a wrapper and `GameInv_<N>_of_<C>` stand for the claims
    /// of one-sided execution of the composition (symbolic-execution story 25).
    #[test]
    fn the_side_invariant_ops_of_a_composition_name_its_claims() {
        let (theorem, project) = load_project("example-projects/4WHS", "Simple4WHS");
        let comp = theorem.find_game_instance("Hybrid2").unwrap().game();
        let rows: Vec<(String, Option<String>)> = side_invariant_ops(project, comp)
            .unwrap()
            .into_iter()
            .map(|o| (o.name, o.claim))
            .collect();
        assert_eq!(
            rows,
            [
                ("Comp_Hybrid2.side_inv_Hybrid2".to_string(), None),
                (
                    "Comp_Hybrid2.PkgInv_main_of_Prf_in_Hybrid2".to_string(),
                    Some("package-invariant!main!Hybrid2-Prf!".to_string())
                ),
                ("PkgInv_main_of_PRF".to_string(), None),
                (
                    "Comp_Hybrid2.GameInv_main_of_Hybrid2".to_string(),
                    Some("game-invariant!main!Hybrid2!".to_string())
                ),
            ]
        );
        let none = theorem.find_game_instance("Hybrid1").unwrap().game();
        assert!(side_invariant_ops(project, none).unwrap().is_empty());
    }

    /// Story 78, ADR 0019: package `P` has the parameters `b`, `k` (a value) and `f`; its owner
    /// declares `P_pkgparams` and the template takes it. `Q` has no parameter and keeps one
    /// argument.
    #[test]
    fn a_package_with_parameters_gets_a_params_record_and_its_template_takes_it() {
        let exported = export(PARAMS, "Proof").unwrap();
        let owner = file(&exported, "Pkg_P_v1.ec");
        assert_eq!(
            item_text(owner, "type P_pkgparams"),
            concat!(
                "type P_pkgparams = {\n",
                "  P_param_b : bool;\n",
                "  P_param_k : int;\n",
                "  P_param_f : int -> int\n",
                "}."
            )
        );
        let template = item_text(owner, "op PkgInv_main_of_P");
        assert!(
            template.starts_with("op PkgInv_main_of_P (p : P_pkgparams) (s : P_pkgstate) : bool ="),
            "{template}"
        );
        for read in ["p.`P_param_k", "p.`P_param_b", "p.`P_param_f s.`P_ctr"] {
            assert!(template.contains(read), "{read} in:\n{template}");
        }
        let with_record: Vec<&PathBuf> = exported
            .files
            .iter()
            .filter(|(_, text)| text.contains("type P_pkgparams"))
            .map(|(name, _)| name)
            .collect();
        assert_eq!(with_record, [Path::new("Pkg_P_v1.ec")]);
        let q = file(&exported, "Pkg_Q.ec");
        assert_eq!(
            count(q, "op PkgInv_nonneg_of_Q (s : Q_pkgstate) : bool ="),
            1,
            "{q}"
        );
        assert!(!q.contains("pkgparams"), "{q}");
    }

    /// Story 78: each variant's package lemma fills the function field with its own operator.
    #[test]
    fn each_variants_package_lemma_applies_the_template_to_its_own_function() {
        let exported = export(PARAMS, "Proof").unwrap();
        for (variant, own, other) in [
            ("P_v1", "func_f1", "func_f2"),
            ("P_v2", "func_f2", "func_f1"),
        ] {
            let lemma = file(&exported, &format!("PkgInv_{variant}_Inc.ec"));
            for read in [
                format!("P_param_b = {variant}.b"),
                format!("P_param_k = {variant}.k"),
                format!("P_param_f = {own}"),
            ] {
                assert!(lemma.contains(&read), "{read} in:\n{lemma}");
            }
            assert!(!lemma.contains(other), "{other} in:\n{lemma}");
        }
    }

    /// Story 78: the side record holds the parameters of `P`, the wrapper passes them, and the
    /// side lemma reads them from the instance's module variables.
    #[test]
    fn the_side_record_holds_the_parameters_and_the_wrapper_passes_them() {
        let exported = export(PARAMS, "Proof").unwrap();
        let comp = file(&exported, "Comp_G.ec");
        let side = item_text(comp, "type G_side");
        assert!(side.contains("G_params_P : P_pkgparams;"), "{side}");
        assert!(!side.contains("G_params_q"), "{side}");
        assert_eq!(
            item_text(comp, "op PkgInv_main_of_P_in_G"),
            "op PkgInv_main_of_P_in_G (s : G_side) : bool =\n  PkgInv_main_of_P s.`G_params_P s.`G_pkg_P."
        );
        assert_eq!(
            item_text(comp, "op PkgInv_nonneg_of_q_in_G"),
            "op PkgInv_nonneg_of_q_in_G (s : G_side) : bool =\n  PkgInv_nonneg_of_Q s.`G_pkg_q."
        );
        let lemma = file(&exported, "SideInv_G_Inc.ec");
        for read in ["Comp_G.Pkg_Inst_P.b", "Comp_G.Pkg_Inst_P.k", "func_f1"] {
            assert!(lemma.contains(read), "{read} in:\n{lemma}");
        }
        assert!(file(&exported, "SideInv_H_Inc.ec").contains("func_f2"));
    }

    /// Story 78: package `R` has a parameter and no state; its template takes `p` only.
    #[test]
    fn a_package_without_state_with_parameters_has_a_template_over_its_parameters() {
        let exported = export(PARAMS, "Proof").unwrap();
        let owner = file(&exported, "Pkg_R.ec");
        assert!(
            item_text(owner, "op PkgInv_either_of_R")
                .starts_with("op PkgInv_either_of_R (p : R_pkgparams) : bool ="),
            "{owner}"
        );
        assert_eq!(
            item_text(file(&exported, "Comp_G.ec"), "op PkgInv_either_of_r_in_G"),
            "op PkgInv_either_of_r_in_G (s : G_side) : bool =\n  PkgInv_either_of_R s.`G_params_r."
        );
        assert!(
            file(&exported, "SideInv_G_Read.ec").contains("require import Pkg_P_v1 Pkg_Q Pkg_R.")
        );
    }

    /// Story 78: the whole tree compiles (skips without `easycrypt`).
    #[test]
    fn the_tree_of_the_params_project_compiles() {
        let exported = export(PARAMS, "Proof").unwrap();
        let out = tempfile::tempdir().unwrap();
        crate::writers::easycrypt::export::write_files(out.path(), &exported.files).unwrap();
        let base = out.path().to_str().unwrap().to_string();
        for side in &exported.side_invariants {
            crate::writers::easycrypt::test_support::assert_compiles(
                &base,
                &format!("{base}/{}", side.join_file),
            );
        }
        crate::writers::easycrypt::test_support::assert_compiles(
            &base,
            &format!("{base}/Eq_left_right.ec"),
        );
    }

    /// Story 79: `P` has no package invariant, but the game invariant of `C` reads its
    /// parameters. `P_pkgparams` is declared, `C_side` holds it, and the game invariant reads
    /// `game.P.b`, `(game.P.f …)` and `(game.f …)`, the operator of the bound constant `g`.
    #[test]
    fn a_game_invariant_reads_package_parameters_and_function_constants() {
        let exported = export(GAME_PARAMS, "Proof").unwrap();
        assert!(
            item_text(file(&exported, "Pkg_P.ec"), "type P_pkgparams")
                .contains("P_param_f : int -> int"),
            "{}",
            file(&exported, "Pkg_P.ec")
        );
        let comp = file(&exported, "Comp_C.ec");
        assert!(
            item_text(comp, "type C_side").contains("C_params_P : P_pkgparams;"),
            "{comp}"
        );
        let inv = item_text(comp, "op GameInv_main_of_C");
        for read in [
            "g.`C_params_P.`P_param_b",
            "g.`C_params_P.`P_param_f g.`C_pkg_P.`P_ctr",
            "func_g g.`C_pkg_P.`P_ctr",
        ] {
            assert!(inv.contains(read), "{read} in:\n{inv}");
        }
        assert!(file(&exported, "SideInv_C_Inc.ec").contains("Comp_C.Pkg_Inst_P.b"));
    }

    /// Story 79: the tree of the game-invariant project compiles (skips without `easycrypt`).
    #[test]
    fn the_tree_of_the_game_params_project_compiles() {
        let exported = export(GAME_PARAMS, "Proof").unwrap();
        let out = tempfile::tempdir().unwrap();
        crate::writers::easycrypt::export::write_files(out.path(), &exported.files).unwrap();
        let base = out.path().to_str().unwrap().to_string();
        for side in &exported.side_invariants {
            crate::writers::easycrypt::test_support::assert_compiles(
                &base,
                &format!("{base}/{}", side.join_file),
            );
        }
        crate::writers::easycrypt::test_support::assert_compiles(
            &base,
            &format!("{base}/Eq_left_right.ec"),
        );
    }
}
