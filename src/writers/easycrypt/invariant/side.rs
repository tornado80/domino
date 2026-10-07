// SPDX-License-Identifier: MIT OR Apache-2.0

//! One-sided invariants (story 58, ADR 0010): the package invariants and the game invariants of
//! the two sides of an equivalence become conjuncts of `inv`, under the `!abort` guard.
//!
//! - A package invariant becomes one template `PkgInv_<Pkg> (s : <Pkg>_pkgstate)` for each
//!   package, and one wrapper `PkgInv_<l|r>_<Inst> (l : <GameInst>_state)` for each instance on
//!   each side. Each wrapper stands for one Domino claim.
//! - A game invariant becomes `GameInv_<GameInst> (g : <GameInst>_state)` for each side whose
//!   composition has one.
//!
//! A one-sided invariant file holds exactly one invariant form of the right kind, and nothing
//! else: that is all that works in Domino for every project.

use std::collections::HashMap;

use miette::Diagnostic;
use thiserror::Error;

use crate::package::{Composition, PackageInstance};
use crate::project::Project;
use crate::theorem::GameInstance;
use crate::types::Type;
use crate::util::smtparser::SmtParser;
use crate::writers::easycrypt::ast::{EcExpr, EcItem, EcType};
use crate::writers::easycrypt::names::Names;
use crate::writers::easycrypt::EcExportError;

use super::{
    field_expr, game_inv_op_name, instance_field_name, pkg_inv_op_name, pkg_inv_template_name,
    pkg_state_fields, pkg_state_type_name, InvariantError, Locals, OpRegistry, Sexp,
    StateLookup, TCtx,
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

    /// A second invariant form for the same package or composition.
    #[error("{owner} has a second `{form}` in invariant file `{file}`; only one is permitted")]
    SecondInvariant {
        file: String,
        owner: String,
        form: &'static str,
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
    #[error("invariant file `{file}` gives an invariant to package `{package}`, which has no state")]
    StatelessPackageInvariant { file: String, package: String },

    /// Two operators of the invariant file with one name, for example the template of a
    /// package `l_Prf` and the wrapper of instance `Prf` on the left.
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
    forms: Vec<(Kind, Sexp)>,
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

    fn handle_define_package_invariant(&mut self, body: Sexp) -> Result<SideStmt, InvariantError> {
        self.forms.push((Kind::Package, body));
        Ok(SideStmt::Form)
    }

    fn handle_define_game_invariant(&mut self, body: Sexp) -> Result<SideStmt, InvariantError> {
        self.forms.push((Kind::Game, body));
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
        funname: &str,
        _args: Vec<Sexp>,
        _body: Sexp,
    ) -> Result<SideStmt, InvariantError> {
        Err(self.forbidden(format!("define-lemma {funname}")))
    }
}

/// The one invariant form of kind `kind` across `files`, with the file it is in.
fn the_one_form(
    project: &impl Project,
    files: &[String],
    owner: &str,
    kind: Kind,
) -> Result<(String, Sexp), InvariantError> {
    let mut found: Option<(String, Sexp)> = None;
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
        for (form_kind, body) in parser.forms {
            check_form(file, owner, kind, form_kind, found.is_some())?;
            found = Some((file.clone(), body));
        }
    }
    found.ok_or_else(|| {
        SideInvariantError::NoInvariant {
            files: files.to_vec(),
            owner: owner.to_string(),
            form: kind.form(),
        }
        .into()
    })
}

fn check_form(
    file: &str,
    owner: &str,
    want: Kind,
    got: Kind,
    have_one: bool,
) -> Result<(), SideInvariantError> {
    if got != want {
        return Err(SideInvariantError::WrongKind {
            file: file.to_string(),
            owner: owner.to_string(),
            form: got.form(),
        });
    }
    if have_one {
        return Err(SideInvariantError::SecondInvariant {
            file: file.to_string(),
            owner: owner.to_string(),
            form: got.form(),
        });
    }
    Ok(())
}

/// What the one-sided invariant operators need from the equivalence.
pub(super) struct SideInput<'a, P: Project> {
    pub left: &'a GameInstance,
    pub right: &'a GameInstance,
    pub left_record_ty: EcType,
    pub right_record_ty: EcType,
    pub theorem_consts: &'a [(String, Type)],
    pub project: &'a P,
}

/// The one-sided invariant operators, and the conjuncts of `inv` they give each side.
#[derive(Default)]
pub(super) struct SideOps {
    /// The `PkgInv_<Pkg>` templates, then the wrappers, then the `GameInv_` operators.
    pub items: Vec<EcItem>,
    /// `PkgInv_l_<Inst> l`…, then `GameInv_<L> l`.
    pub left: Vec<EcExpr>,
    /// `PkgInv_r_<Inst> r`…, then `GameInv_<R> r`.
    pub right: Vec<EcExpr>,
}

/// One side of the equivalence.
struct Side<'a> {
    game_inst: &'a GameInstance,
    /// `l` or `r`: the wrapper's side letter and its record parameter.
    letter: &'static str,
    record_ty: EcType,
}

impl Side<'_> {
    fn field_prefix(&self) -> String {
        format!("{}_", self.letter)
    }
}

/// Builds the one-sided invariant operators of the equivalence, and registers their names in
/// `ops`, so a name collision is a hard error.
pub(super) fn build<P: Project>(
    input: &SideInput<'_, P>,
    ops: &mut OpRegistry,
) -> Result<SideOps, EcExportError> {
    let sides = [
        Side {
            game_inst: input.left,
            letter: "l",
            record_ty: input.left_record_ty.clone(),
        },
        Side {
            game_inst: input.right,
            letter: "r",
            record_ty: input.right_record_ty.clone(),
        },
    ];
    let mut out = SideOps::default();
    let mut templates: HashMap<String, ()> = HashMap::new();
    let mut wrappers = Vec::new();
    let mut games = Vec::new();
    for side in &sides {
        let mut conjuncts = Vec::new();
        for inst in invariant_instances(side.game_inst) {
            let package = inst.pkg.name.clone();
            if templates.insert(package.clone(), ()).is_none() {
                out.items.push(package_template(input, inst, ops)?);
            }
            let name = pkg_inv_op_name(side.letter, inst.name());
            ops.define_named(&name, &format!("the wrapper of instance `{}`", inst.name()))?;
            wrappers.push(wrapper(side, inst, &name));
            conjuncts.push(apply(&name, side.letter));
        }
        if !side.game_inst.game().invariants.is_empty() {
            let name = game_inv_op_name(side.game_inst.name());
            ops.define_named(&name, &format!("the game invariant of `{}`", side.game_inst.name()))?;
            games.push(game_operator(input, side, &name)?);
            conjuncts.push(apply(&name, side.letter));
        }
        if side.letter == "l" {
            out.left = conjuncts;
        } else {
            out.right = conjuncts;
        }
    }
    out.items.extend(wrappers);
    out.items.extend(games);
    Ok(out)
}

/// The package instances of `game_inst` that have a package invariant, in
/// `ordered_pkgs_idx()` order.
pub(super) fn invariant_instances(game_inst: &GameInstance) -> Vec<&PackageInstance> {
    let game = game_inst.game();
    game.ordered_pkgs_idx()
        .into_iter()
        .map(|idx| &game.pkgs[idx])
        .filter(|inst| !inst.pkg.invariants.is_empty())
        .collect()
}

fn apply(op: &str, arg: &str) -> EcExpr {
    EcExpr::App {
        head: op.to_string(),
        args: vec![EcExpr::Var(arg.to_string())],
    }
}

/// `op PkgInv_<Pkg> (s : <Pkg>_pkgstate) : bool = <body>.`
fn package_template<P: Project>(
    input: &SideInput<'_, P>,
    inst: &PackageInstance,
    ops: &mut OpRegistry,
) -> Result<EcItem, EcExportError> {
    let package = inst.pkg.name.as_str();
    let owner = format!("package `{package}`");
    let (file, body) = the_one_form(input.project, &inst.pkg.invariants, &owner, Kind::Package)?;
    let fields = pkg_state_fields(inst, &mut Names::new())?;
    if fields.is_empty() {
        return Err(InvariantError::from(SideInvariantError::StatelessPackageInvariant {
            file,
            package: package.to_string(),
        })
        .into());
    }
    let mut lookup = StateLookup::default();
    for (raw, field, ty) in fields {
        let projection = field_expr("s", &field);
        lookup.fields.insert(format!("pkg.{raw}"), (projection, ty));
    }
    let name = pkg_inv_template_name(package);
    ops.define_named(&name, &format!("the package invariant of `{package}`"))?;
    let body = translate(input, &file, &lookup, &body)?;
    Ok(op_def(&name, "s", EcType::Named(pkg_state_type_name(package)), body))
}

/// `op PkgInv_<l|r>_<Inst> (l : <GameInst>_state) : bool = PkgInv_<Pkg> l.`l_pkg_<Inst>.`
fn wrapper(side: &Side<'_>, inst: &PackageInstance, name: &str) -> EcItem {
    let field = instance_field_name(&side.field_prefix(), inst.name());
    let body = EcExpr::App {
        head: pkg_inv_template_name(&inst.pkg.name),
        args: vec![field_expr(side.letter, &field)],
    };
    op_def(name, side.letter, side.record_ty.clone(), body)
}

/// `op GameInv_<GameInst> (g : <GameInst>_state) : bool = <body>.`
fn game_operator<P: Project>(
    input: &SideInput<'_, P>,
    side: &Side<'_>,
    name: &str,
) -> Result<EcItem, EcExportError> {
    let composition: &Composition = side.game_inst.game();
    let owner = format!("composition `{}`", composition.name);
    let (file, body) = the_one_form(input.project, &composition.invariants, &owner, Kind::Game)?;
    let lookup = game_lookup(side)?;
    let body = translate(input, &file, &lookup, &body)?;
    Ok(op_def(name, "g", side.record_ty.clone(), body))
}

/// `game.<Inst>.<field>` -> ``g.`{l_|r_}pkg_<Inst>.`<Pkg>_<field>``, for every state field.
fn game_lookup(side: &Side<'_>) -> Result<StateLookup, EcExportError> {
    let mut lookup = StateLookup::default();
    let game = side.game_inst.game();
    for inst in &game.pkgs {
        let inst_field = instance_field_name(&side.field_prefix(), inst.name());
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
    input: &SideInput<'_, P>,
    file: &str,
    lookup: &StateLookup,
    body: &Sexp,
) -> Result<EcExpr, InvariantError> {
    let no_ops = OpRegistry::default();
    let mut tctx = TCtx {
        file: file.to_string(),
        lookup,
        left_record_ty: input.left_record_ty.clone(),
        right_record_ty: input.right_record_ty.clone(),
        theorem_consts: input.theorem_consts,
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
    use super::super::tests::{find_equivalence, item_text, load_project};
    use super::super::{build_invariant_file, invariant_ops, OpRegistry};
    use super::*;
    use crate::writers::easycrypt::render::render_file;

    const STORY58: &str = "testdata/easycrypt/story58";

    fn rendered(dir: &str, theorem: &str, left: &str, right: &str) -> String {
        let (theorem, project) = load_project(dir, theorem);
        let equivalence = find_equivalence(&theorem, left, right);
        render_file(&build_invariant_file(&theorem, equivalence, project).unwrap().file)
    }

    fn error_of(theorem: &str) -> String {
        let (theorem, project) = load_project(STORY58, theorem);
        let equivalence = find_equivalence(&theorem, "L", "R");
        match build_invariant_file(&theorem, equivalence, project) {
            Ok(_) => panic!("the invariant file builds"),
            Err(e) => e.to_string(),
        }
    }

    fn count(text: &str, needle: &str) -> usize {
        text.matches(needle).count()
    }

    fn golden(rendered: &str, name: &str) {
        let path = format!("{}/{STORY58}/4WHS/{name}", env!("CARGO_MANIFEST_DIR"));
        let expected = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read golden file {path}: {e}"));
        assert_eq!(rendered, expected, "rendered != {path}");
    }

    fn assert_compiles(rendered: &str, name: &str) {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join(name);
        std::fs::write(&file, rendered).unwrap();
        let types_dir = format!("{}/testdata/easycrypt/story02/4WHS", env!("CARGO_MANIFEST_DIR"));
        crate::writers::easycrypt::test_support::assert_compiles_with_paths(
            &[dir.path().to_str().unwrap(), &types_dir],
            file.to_str().unwrap(),
        );
    }

    #[test]
    fn hybrid1_hybrid2_gets_the_right_sides_package_and_game_invariant() {
        let text = rendered("example-projects/4WHS", "Simple4WHS", "Hybrid1", "Hybrid2");
        for op in ["op PkgInv_PRF ", "op PkgInv_r_Prf ", "op GameInv_Hybrid2 "] {
            assert_eq!(count(&text, op), 1, "{op} in:\n{text}");
        }
        assert_eq!(count(&text, "op PkgInv_l_"), 0, "{text}");
        let inv = item_text(&text, "op inv");
        assert!(
            inv.contains("=>    Domino_invariant l r\n         /\\ PkgInv_r_Prf r\n         /\\ GameInv_Hybrid2 r)."),
            "{inv}"
        );
        golden(&text, "Eq_Hybrid1_Hybrid2_Invariants.ec");
        assert_compiles(&text, "Eq_Hybrid1_Hybrid2_Invariants.ec");
    }

    #[test]
    fn real_ideal_hybrid3_has_the_prf_body_one_time_and_one_wrapper_for_each_side() {
        let text = rendered(
            "example-projects/4WHS",
            "Simple4WHS",
            "Real_Hybrid3",
            "Ideal_Hybrid3",
        );
        for op in [
            "op PkgInv_PRF ",
            "op PkgInv_l_Prf ",
            "op PkgInv_r_Prf ",
            "op GameInv_Real_Hybrid3 ",
            "op GameInv_Ideal_Hybrid3 ",
        ] {
            assert_eq!(count(&text, op), 1, "{op} in:\n{text}");
        }
        // the body of the PRF invariant is in the template only
        assert_eq!(count(&text, "kid <= 0"), 1, "{text}");
        assert!(item_text(&text, "op PkgInv_PRF").contains("kid <= 0"), "{text}");
        // templates, then wrappers, then the game invariants, then `params_inv`
        let order: Vec<usize> = [
            "op Domino_invariant ",
            "op PkgInv_PRF ",
            "op PkgInv_l_Prf ",
            "op PkgInv_r_Prf ",
            "op GameInv_Real_Hybrid3 ",
            "op GameInv_Ideal_Hybrid3 ",
            "op params_inv ",
        ]
        .iter()
        .map(|h| text.find(h).unwrap())
        .collect();
        assert!(order.windows(2).all(|w| w[0] < w[1]), "{text}");
        golden(&text, "Eq_Real_Hybrid3_Ideal_Hybrid3_Invariants.ec");
        assert_compiles(&text, "Eq_Real_Hybrid3_Ideal_Hybrid3_Invariants.ec");
    }

    #[test]
    fn the_one_sided_theorem_gets_both_kinds_on_both_sides() {
        let text = rendered(STORY58, "OneSided", "L", "R");
        assert_eq!(
            item_text(&text, "op inv"),
            concat!(
                "op inv (l : L_state) (r : R_state) : bool =\n",
                "     params_inv l r\n",
                "  /\\ l.`l_abort_flag = r.`r_abort_flag\n",
                "  /\\ (   !l.`l_abort_flag\n",
                "      =>    Domino_invariant l r\n",
                "         /\\ PkgInv_l_C l\n",
                "         /\\ GameInv_L l\n",
                "         /\\ PkgInv_r_C r\n",
                "         /\\ GameInv_R r)."
            )
        );
        assert_eq!(
            item_text(&text, "op PkgInv_l_C"),
            "op PkgInv_l_C (l : L_state) : bool =\n  PkgInv_Ctr l.`l_pkg_C."
        );
        assert_eq!(
            item_text(&text, "op GameInv_R"),
            "op GameInv_R (g : R_state) : bool =\n  0 <= g.`r_pkg_C.`Ctr_ctr."
        );
    }

    #[test]
    fn a_helper_define_fun_is_a_hard_error_naming_the_file() {
        let e = error_of("HelperFun");
        assert!(e.contains("`./packages/Helper.smt2`") && e.contains("define-fun nonneg"), "{e}");
    }

    #[test]
    fn a_second_invariant_form_is_a_hard_error_naming_the_file() {
        let e = error_of("TwoForms");
        assert!(e.contains("`./packages/Two-b.smt2`") && e.contains("second"), "{e}");
    }

    #[test]
    fn a_form_of_the_wrong_kind_is_a_hard_error_naming_the_file() {
        let e = error_of("WrongKind");
        assert!(e.contains("`./packages/Wrong.smt2`") && e.contains("define-game-invariant"), "{e}");
    }

    #[test]
    fn a_package_invariant_of_a_stateless_package_is_a_hard_error_naming_the_file() {
        let e = error_of("Stateless");
        assert!(e.contains("`./packages/NoState.smt2`") && e.contains("no state"), "{e}");
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
    fn a_wrapper_with_the_name_of_another_pkg_inv_operator_is_a_hard_error() {
        let mut ops = OpRegistry::default();
        ops.define_named("PkgInv_l_Prf", "the package invariant of `l_Prf`")
            .unwrap();
        // the same operator again is not a collision
        ops.define_named("PkgInv_l_Prf", "the package invariant of `l_Prf`")
            .unwrap();
        let err = ops
            .define_named("PkgInv_l_Prf", "the wrapper of instance `Prf`")
            .unwrap_err();
        assert!(
            matches!(
                &err,
                InvariantError::Side(SideInvariantError::OpNameCollision { name, .. })
                    if name == "PkgInv_l_Prf"
            ),
            "{err:?}"
        );
    }

    #[test]
    fn invariant_ops_name_the_operators_in_unfold_order_with_their_claims() {
        let (theorem, _) = load_project("example-projects/4WHS", "Simple4WHS");
        let left = theorem.find_game_instance("Real_Hybrid3").unwrap();
        let right = theorem.find_game_instance("Ideal_Hybrid3").unwrap();
        let ops = invariant_ops(left, right, &["relation-a-b".to_string(), "state=".to_string()]);
        let pairs: Vec<(&str, Option<&str>)> = ops
            .iter()
            .map(|o| (o.name.as_str(), o.claim.as_deref()))
            .collect();
        assert_eq!(
            pairs,
            [
                ("inv", None),
                ("params_inv", None),
                ("Domino_relation_a_b", None),
                ("Domino_state_eq", None),
                ("PkgInv_l_Prf", Some("package-invariant!Real_Hybrid3-Prf!")),
                ("PkgInv_r_Prf", Some("package-invariant!Ideal_Hybrid3-Prf!")),
                ("PkgInv_PRF", None),
                ("GameInv_Real_Hybrid3", Some("game-invariant!Real_Hybrid3!")),
                ("GameInv_Ideal_Hybrid3", Some("game-invariant!Ideal_Hybrid3!")),
            ]
        );
    }
}
