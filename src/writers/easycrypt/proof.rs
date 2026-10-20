// SPDX-License-Identifier: MIT OR Apache-2.0

//! Building `Eq_<Left>_<Right>.ec`
//! (`docs/stories/easycrypt/07-proof-skeleton.md`): the equivalence-proof
//! skeleton — lemma, adversary declaration, the invariant `call`, the
//! induction start, and one `admit` per oracle, in the game interface's own
//! export order. Deriving the per-oracle tactics is explicitly out of scope
//! for v1 (the story's own §1): every oracle bullet is exactly `proc;
//! inline. admit.`.
//!
//! [`compute_equivalence_files`] is the entry point story 05's
//! `export::export_theorem` calls: it also drives story 06's
//! `invariant::build_invariant_file`, since both files share one
//! `GameHop::Equivalence` loop and this story owns the orchestration
//! (`docs/stories/easycrypt/06-invariant-translation-IMPLEMENTATION-REPORT.md`
//! §10).

use std::collections::{HashMap, HashSet};

use crate::expressions::{Expression, ExpressionKind};
use crate::gamehops::equivalence::Equivalence;
use crate::identifier::game_ident::GameIdentifier;
use crate::identifier::theorem_ident::TheoremIdentifier;
use crate::identifier::Identifier;
use crate::package::Composition;
use crate::project::Project;
use crate::theorem::{GameInstance, Theorem};

use super::ast::{
    DeclareModule, EcExpr, EcFile, EcItem, EcLemma, EcSection, LemmaBinder, ProofLine, Require,
};
use super::game::composition_const_needs_arg;
use super::interfaces::{self, InterfacesOutput};
use super::invariant::{self, InvariantError, InvariantFile};
use super::names::{NameKind, Names};
use super::package;
use super::types::translate_type;
use super::EcExportError;

/// One equivalence hop's rendered proof skeleton, ready for
/// `Eq_<Left>_<Right>.ec`.
pub struct EquivalenceProofFile {
    /// Index of the hop in `theorem.game_hops` (`domino proofsteps`' numbering).
    pub proofstep: usize,
    pub file_name: String,
    pub file: EcFile,
    pub left_name: String,
    pub right_name: String,
    /// Exported oracles this equivalence's game interface covers — one
    /// `admit` bullet each. `admit_count == oracle_count` always in v1.
    pub oracle_count: usize,
    pub admit_count: usize,
    /// Set when `equivalence.trees()` names an oracle set different from
    /// the game interface's own export list (§3: "warn if that set differs
    /// from the game interface's export list") — human-readable, for the
    /// CLI's stdout report. The bullets themselves always follow the
    /// interface's export list regardless, so an oracle is never silently
    /// dropped.
    pub oracle_set_mismatch: Option<String>,
    /// One oracle lemma file per exported oracle, in the game interface's order. The glue
    /// (`file`) closes each oracle's goal with `+ by conseq <lemma> <left> <right> => /#.`: the
    /// side-invariant lemmas of the oracle for each side whose composition has one (story 69;
    /// `_` for a left side without one, nothing for a right side without one). The `call` names
    /// the oracle's parameters where the lemma says `={arg}`, and `/#` closes the difference.
    pub oracle_files: Vec<OracleProofFile>,
}

/// One oracle's lemma file, `Eq_<L>_<R>_<O>.ec` (story 68, ADR 0013): the goal the glue's
/// `call (: inv …)` leaves for the oracle, as a lemma outside any section. Since story 69
/// (ADR 0014) it assumes the side invariants of both sides in its precondition and proves
/// only `={res} /\ inv`. Translation writes `+ proc; inline. admit.` as its proof; the proof
/// job of the oracle owns the file after that.
pub struct OracleProofFile {
    /// The exported oracle's name, the `<O>` of the file name.
    pub oracle: String,
    pub file_name: String,
    pub file: EcFile,
}

/// One equivalence hop's paired output: story 06's invariant file and this
/// story's own proof skeleton.
pub struct EquivalenceFiles {
    pub invariants: InvariantFile,
    pub proof: EquivalenceProofFile,
}

/// Computes every `GameHop::Equivalence`'s paired output for `theorem`, in
/// `theorem.game_hops` order (`GameHop::as_equivalence()` — v1 does not
/// descend into a `GameHop::Hybrid`'s own nested equivalence, matching
/// `export::compute_skipped`'s existing "hybrid game hops are not
/// translated" note). `interfaces` is story 04's already-built
/// `Interfaces.ec` data.
pub fn compute_equivalence_files(
    theorem: &Theorem<'_>,
    project: &impl Project,
    interfaces: &InterfacesOutput,
) -> Result<Vec<EquivalenceFiles>, EcExportError> {
    compute_equivalence_files_observed(
        theorem,
        project,
        interfaces,
        &mut super::progress::NopExportObserver,
    )
}

/// [`compute_equivalence_files`] reporting the `invariants` phase (every
/// equivalence's invariant file) and then the `proofs` phase (every proof
/// skeleton) — story 21. The output is identical to a single interleaved pass:
/// the two builders share no state but `lemma_names`, which only the proof
/// builder touches.
pub fn compute_equivalence_files_observed(
    theorem: &Theorem<'_>,
    project: &impl Project,
    interfaces: &InterfacesOutput,
    observer: &mut dyn super::progress::ExportObserver,
) -> Result<Vec<EquivalenceFiles>, EcExportError> {
    use super::progress::{ExportPhase, PhaseScope};

    let hops: Vec<(usize, &crate::gamehops::equivalence::Equivalence, String)> = theorem
        .game_hops
        .iter()
        .enumerate()
        .filter_map(|(proofstep, hop)| {
            let eq = hop.as_equivalence()?;
            let stem = format!(
                "Eq_{}_{}",
                hop.left_game_instance_name(),
                hop.right_game_instance_name()
            );
            Some((proofstep, eq, stem))
        })
        .collect();

    let mut scope = PhaseScope::start(observer, ExportPhase::Invariants, hops.len());
    let mut invariant_files = Vec::with_capacity(hops.len());
    for (_, equivalence, stem) in &hops {
        scope.item(&format!("{stem}_Invariants"));
        invariant_files.push(invariant::build_invariant_file(
            theorem,
            equivalence,
            project,
        )?);
    }
    scope.finish();

    let owners = invariant::StateOwners::of(theorem)?;
    let mut lemma_names = Names::new();
    let mut scope = PhaseScope::start(observer, ExportPhase::Proofs, hops.len());
    let mut out = Vec::with_capacity(hops.len());
    for ((proofstep, equivalence, stem), invariants) in hops.iter().zip(invariant_files) {
        scope.item(stem);
        let proof = build_equivalence_file(
            theorem,
            *proofstep,
            equivalence,
            interfaces,
            &owners,
            &mut lemma_names,
        )?;
        out.push(EquivalenceFiles { invariants, proof });
    }
    scope.finish();
    Ok(out)
}

/// One side's naming layout inside its own `Comp_<mangled>.ec` file (story
/// 10): the composition's own mangled base (`Game_<mangled>`/`Exp_<mangled>`
/// module names derive from this, unprefixed), the *theory* qualifier a
/// `require`r must use to reach into that file (`comp_theory`, `Comp_
/// <mangled>` — story 10 §3.1: only the file/theory name gets the `Comp_`
/// prefix, every module name keeps its old spelling), and — in `comp.pkgs`
/// declaration order — each instance's mangled name. Story 14 §3.4 dropped
/// the variant-name component from every instance path (every instance is
/// addressable as `Pkg_Inst_<InstMangled>`, no matter which variant it
/// clones), so this no longer needs a `variant_name_map` at all. Recomputed
/// independently per side from `interfaces` rather than threaded out of
/// `game.rs` (which never exposes these internals) — a pure function of
/// `comp`, matching story 04's own "recomputed, not threaded through"
/// precedent (its report §3).
pub(super) struct CompLayout {
    pub(super) comp_mangled: String,
    pub(super) comp_theory: String,
    inst_mangled: Vec<String>,
}

pub(super) fn compute_layout(
    comp: &Composition,
    interfaces: &InterfacesOutput,
) -> Result<CompLayout, EcExportError> {
    let comp_mangled = interfaces.comp_mangled[&comp.name].clone();
    let comp_theory = format!("Comp_{comp_mangled}");

    // Same registry/order `game.rs::render_game_file` uses for its own
    // `Pkg_Inst_<InstMangled>` aliases — `comp.pkgs` declaration order, not
    // `ordered_pkgs_idx()` — so restriction/record-literal paths agree with
    // what the actual game file names.
    let mut inst_names = Names::new();
    let mut inst_mangled = Vec::with_capacity(comp.pkgs.len());
    for inst in &comp.pkgs {
        inst_mangled.push(inst_names.mangle(NameKind::Module, inst.name())?);
    }

    Ok(CompLayout {
        comp_mangled,
        comp_theory,
        inst_mangled,
    })
}

/// `Comp_<mangled>.Game_<mangled>` then `Comp_<mangled>.Pkg_Inst_<InstMangled>`
/// per instance, `comp.pkgs` order — every router and every instance name
/// story 04/14 gave this composition's own game file (§3, amended by story
/// 14 §3.6: restrictions must name `Pkg_Inst_<InstMangled>`, with no variant
/// component — an alias and a functor application both denote the same
/// memory cells as the clone they come from, §2.1). The qualifier is
/// `comp_theory` (story 10's `Comp_` prefix, since that's the theory a
/// `require`r must use to reach into that file); the module name after it
/// keeps its own, unprefixed spelling.
fn restrictions_for(layout: &CompLayout) -> Vec<String> {
    let mut out = vec![format!(
        "{}.Game_{}",
        layout.comp_theory, layout.comp_mangled
    )];
    for inst_mangled in &layout.inst_mangled {
        out.push(format!("{}.Pkg_Inst_{inst_mangled}", layout.comp_theory));
    }
    out
}

/// Builds one side's game-state record literal at the `call` site, in the
/// shape `invariant.rs::build_side_record` gives the record *type*
/// (story 42 §3.2, ADR 0007): one field `{field_ns_prefix}pkg_<Inst>` per
/// instance with state, holding a nested `<Pkg>_pkgstate` literal, then one
/// field per qualifying package parameter ([`package::param_needs_var`]),
/// both in `ordered_pkgs_idx()` order, then `abort_flag`. Field names come
/// from `invariant.rs`'s naming helpers, and state fields and parameters
/// are mangled through one per-instance [`Names`], as there. Each leaf
/// *value* is a memory-tagged module-state read
/// (`Comp_Hybrid0.Pkg_Inst_KX.d_LTK{1}`), not a record projection.
fn build_side_record_lit(
    comp: &Composition,
    layout: &CompLayout,
    field_ns_prefix: &str,
    mem: u8,
) -> Result<EcExpr, EcExportError> {
    let mut instance_fields: Vec<(String, EcExpr)> = Vec::new();
    let mut param_fields: Vec<(String, EcExpr)> = Vec::new();

    for &idx in &comp.ordered_pkgs_idx() {
        let inst = &comp.pkgs[idx];
        let mut names = Names::new();
        if let Some(state) = instance_state_lit(inst, layout, idx, Some(mem), &mut names)? {
            instance_fields.push((
                invariant::instance_field_name(field_ns_prefix, inst.name()),
                state,
            ));
        }

        for (name, ty, _span) in &inst.pkg.params {
            if !package::param_needs_var(&inst.pkg, name, ty) {
                continue;
            }
            let mangled = names.mangle(NameKind::Var, name)?;
            param_fields.push((
                invariant::param_field_name(field_ns_prefix, inst.name(), &mangled),
                module_var(layout, idx, mangled, Some(mem)),
            ));
        }
    }

    let mut fields = instance_fields;
    fields.extend(param_fields);
    fields.push((
        invariant::abort_field_name(field_ns_prefix),
        EcExpr::Qualified {
            path: vec![
                layout.comp_theory.clone(),
                format!("Game_{}", layout.comp_mangled),
                "abort_flag".to_string(),
            ],
            mem: Some(mem),
        },
    ));

    Ok(EcExpr::RecordLit { fields })
}

/// `Comp_<C>.Pkg_Inst_<Inst>.<var>` of instance `idx`, at memory `mem` (none in a one-memory
/// judgement).
fn module_var(layout: &CompLayout, idx: usize, var: String, mem: Option<u8>) -> EcExpr {
    EcExpr::Qualified {
        path: vec![
            layout.comp_theory.clone(),
            format!("Pkg_Inst_{}", layout.inst_mangled[idx]),
            var,
        ],
        mem,
    }
}

/// The `<Pkg>_pkgstate` literal of instance `idx` of the composition, its fields read from the
/// module variables at `mem`, or `None` for an instance without state. The state fields are
/// mangled through `names` (the instance's own registry, as in the package's module).
fn instance_state_lit(
    inst: &crate::package::PackageInstance,
    layout: &CompLayout,
    idx: usize,
    mem: Option<u8>,
    names: &mut Names,
) -> Result<Option<EcExpr>, EcExportError> {
    let package = inst.pkg.name.as_str();
    let mut fields = Vec::with_capacity(inst.pkg.state.len());
    for (name, _ty, _span) in &inst.pkg.state {
        let mangled = names.mangle(NameKind::Var, name)?;
        fields.push((
            invariant::pkg_state_field_name(package, &mangled),
            module_var(layout, idx, mangled, mem),
        ));
    }
    Ok((!fields.is_empty()).then_some(EcExpr::RecordLit { fields }))
}

/// `Comp_<C>.side_inv_<C>` applied to the composition's side record (story 69), its fields
/// read from the module variables at `mem` (none for the side-invariant lemma's one memory),
/// or `None` when the composition has no side invariant. The side record's fields are
/// qualified with the composition's theory, so a file that uses it need not import that
/// theory; the `<Pkg>_pkgstate` fields need the package files imported.
pub(super) fn side_inv_app(
    comp: &Composition,
    layout: &CompLayout,
    mem: Option<u8>,
) -> Result<Option<EcExpr>, EcExportError> {
    if !invariant::has_side_invariants(comp) {
        return Ok(None);
    }
    let theory = &layout.comp_theory;
    let prefix = format!("{}_", layout.comp_mangled);
    let mut fields = Vec::new();
    for &idx in &comp.ordered_pkgs_idx() {
        let inst = &comp.pkgs[idx];
        if let Some(state) = instance_state_lit(inst, layout, idx, mem, &mut Names::new())? {
            let field = invariant::instance_field_name(&prefix, inst.name());
            fields.push((format!("{theory}.{field}"), state));
        }
    }
    // story 78: the parameters of each instance whose package has a params record
    for &idx in &comp.ordered_pkgs_idx() {
        let inst = &comp.pkgs[idx];
        let read = |var: &str| module_var(layout, idx, var.to_string(), mem);
        if let Some(params) = invariant::pkg_params_lit(inst, read)? {
            let field = invariant::params_field_name(&prefix, inst.name());
            fields.push((format!("{theory}.{field}"), params));
        }
    }
    fields.push((
        format!("{theory}.{}", invariant::abort_field_name(&prefix)),
        EcExpr::Qualified {
            path: vec![
                theory.clone(),
                format!("Game_{}", layout.comp_mangled),
                "abort_flag".to_string(),
            ],
            mem,
        },
    ));
    Ok(Some(EcExpr::App {
        head: format!(
            "{theory}.{}",
            invariant::side_inv_op_name(&layout.comp_mangled)
        ),
        args: vec![EcExpr::RecordLit { fields }],
    }))
}

/// A composition-level `run` argument's resolved value: a literal (rendered
/// verbatim) or a reference to a theorem constant (rendered as that
/// constant's lemma binder). Mirrors `invariant.rs::ParamValue`, one level
/// up — a *composition's* own const binding rather than a *package
/// instance's* param binding — so it is re-derived rather than shared (same
/// rationale as [`build_side_record_lit`]).
enum RunArgValue {
    Literal(String),
    TheoremConst(String),
}

/// A game instance's composition-const binding is always either a literal
/// or a bare reference to the theorem's own const
/// (`example-projects/4WHS/theorem/Simple4WHS.ssp`'s `params { b: b, ... }`
/// / `params { b: false, ... }`) — never a compound expression, the same
/// invariant `game.rs::references_game_const` relies on one level down.
/// Mirrors `invariant.rs::resolve_expr_value`'s chase.
fn resolve_run_arg(expr: &Expression) -> Option<RunArgValue> {
    match expr.kind() {
        ExpressionKind::BooleanLiteral(s) => Some(RunArgValue::Literal(s.clone())),
        ExpressionKind::IntegerLiteral(i) => Some(RunArgValue::Literal(i.to_string())),
        ExpressionKind::Identifier(Identifier::TheoremIdentifier(TheoremIdentifier::Const(c))) => {
            Some(RunArgValue::TheoremConst(c.name.clone()))
        }
        ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(c))) => {
            c.assigned_value.as_deref().and_then(resolve_run_arg)
        }
        _ => None,
    }
}

fn literal_text_to_expr(text: &str) -> EcExpr {
    match text {
        "true" => EcExpr::Bool(true),
        "false" => EcExpr::Bool(false),
        other => EcExpr::Int(other.parse().unwrap_or(0)),
    }
}

/// One side's `run` argument list: `comp.consts`, filtered by the exact
/// rule `game.rs`'s own router `init` uses
/// ([`composition_const_needs_arg`]), in `comp.consts` declaration order —
/// so this always matches that composition's `Exp_<mangled>.run`'s real
/// argument list.
fn side_run_args(comp: &Composition, game_inst: &GameInstance) -> Vec<RunArgValue> {
    let mut out = Vec::new();
    for (name, ty) in &comp.consts {
        if !composition_const_needs_arg(comp, name, ty) {
            continue;
        }
        let assigned = game_inst
            .consts
            .iter()
            .find(|(id, _)| &id.name == name)
            .map(|(_, expr)| expr)
            .expect("a game instance binds every one of its composition's declared consts");
        let value = resolve_run_arg(assigned).unwrap_or_else(|| {
            unreachable!(
                "a game instance's composition-const binding must be a literal or a bare \
                 theorem-const reference, found {assigned:?}"
            )
        });
        out.push(value);
    }
    out
}

fn args_to_exprs(values: &[RunArgValue], binder_mangled: &HashMap<String, String>) -> Vec<EcExpr> {
    values
        .iter()
        .map(|v| match v {
            RunArgValue::Literal(text) => literal_text_to_expr(text),
            RunArgValue::TheoremConst(name) => EcExpr::Var(binder_mangled[name].clone()),
        })
        .collect()
}

fn plain_line(text: impl Into<String>) -> ProofLine {
    ProofLine::Tactic {
        indent: 0,
        bullet: None,
        text: text.into(),
    }
}

fn blank_line() -> ProofLine {
    plain_line(String::new())
}

fn bullet_line(text: impl Into<String>) -> ProofLine {
    ProofLine::Tactic {
        indent: 0,
        bullet: Some('+'),
        text: text.into(),
    }
}

/// One side's conjunct for the `byequiv` precondition (story 15 §3.1):
/// `arg{side} = <value>` for a one-argument `run`, `arg{side} = (<v1>, …,
/// <vn>)` for more, and none at all for a zero-argument one. `arg` is
/// EasyCrypt's name for the tuple of the procedure's arguments — a *program*
/// identifier, so a lemma binder spelled like a `run` parameter cannot shadow
/// it the way it voids `<param>{side} = <value>` (story 15 §1). A single
/// argument is the bare value, not a one-tuple.
fn side_precondition_conjunct(
    args: &[RunArgValue],
    side: u8,
    binder_mangled: &HashMap<String, String>,
) -> Option<EcExpr> {
    let mut values = args_to_exprs(args, binder_mangled);
    let rhs = match values.len() {
        0 => return None,
        1 => values.remove(0),
        _ => EcExpr::Tuple(values),
    };
    Some(EcExpr::Binop {
        op: super::ast::EcBinop::Eq,
        lhs: Box::new(EcExpr::Qualified {
            path: vec!["arg".to_string()],
            mem: Some(side),
        }),
        rhs: Box::new(rhs),
    })
}

/// The full `byequiv` induction-start precondition (story 15 §3.1):
/// `={glob A}`, then side 1's `arg` conjunct, then side 2's, each in
/// [`side_run_args`]'s own composition-const order and each omitted when that
/// side's `run` takes no arguments. Both sides are always listed separately,
/// never collapsed into `arg{1} = arg{2}`: their arities can differ.
fn build_byequiv_precondition(
    left_args: &[RunArgValue],
    right_args: &[RunArgValue],
    binder_mangled: &HashMap<String, String>,
) -> Vec<EcExpr> {
    let mut conjuncts = vec![EcExpr::GlobEq("A".to_string())];
    conjuncts.extend(side_precondition_conjunct(left_args, 1, binder_mangled));
    conjuncts.extend(side_precondition_conjunct(right_args, 2, binder_mangled));
    conjuncts
}

fn build_equivalence_file(
    theorem: &Theorem<'_>,
    proofstep: usize,
    equivalence: &Equivalence,
    interfaces: &InterfacesOutput,
    owners: &invariant::StateOwners,
    lemma_names: &mut Names,
) -> Result<EquivalenceProofFile, EcExportError> {
    let left_game_inst = theorem
        .find_game_instance(equivalence.left_name())
        .ok_or_else(|| InvariantError::MissingGameInstance {
            name: equivalence.left_name().to_string(),
        })?;
    let right_game_inst = theorem
        .find_game_instance(equivalence.right_name())
        .ok_or_else(|| InvariantError::MissingGameInstance {
            name: equivalence.right_name().to_string(),
        })?;

    let left_comp = left_game_inst.game();
    let right_comp = right_game_inst.game();
    let span = interfaces::composition_span(left_comp);
    let same_composition = left_comp.name == right_comp.name;

    let left_layout = compute_layout(left_comp, interfaces)?;
    let right_layout = compute_layout(right_comp, interfaces)?;

    // --- binders: `&m` then one typed binder per theorem constant either
    // side's run() binds to a constant rather than a literal, in theorem
    // declaration order (§3) -----------------------------------------------
    let left_args = side_run_args(left_comp, left_game_inst);
    let right_args = side_run_args(right_comp, right_game_inst);

    let mut referenced: HashSet<&str> = HashSet::new();
    for v in left_args.iter().chain(right_args.iter()) {
        if let RunArgValue::TheoremConst(name) = v {
            referenced.insert(name.as_str());
        }
    }

    let mut binders = vec![LemmaBinder::Memory("m".to_string())];
    let mut binder_mangled: HashMap<String, String> = HashMap::new();
    let mut binder_names = Names::new();
    for (name, ty) in &theorem.consts {
        if !referenced.contains(name.as_str()) {
            continue;
        }
        let mangled = binder_names.mangle(NameKind::Var, name)?;
        binders.push(LemmaBinder::Typed {
            name: mangled.clone(),
            ty: translate_type(ty, span)?,
        });
        binder_mangled.insert(name.clone(), mangled);
    }

    let left_run_args = args_to_exprs(&left_args, &binder_mangled);
    let right_run_args = args_to_exprs(&right_args, &binder_mangled);

    // --- the lemma statement: Pr[...] = Pr[...] -----------------------
    let left_pr = EcExpr::Pr {
        module: format!(
            "{}.Exp_{}(A)",
            left_layout.comp_theory, left_layout.comp_mangled
        ),
        proc: "run".to_string(),
        args: left_run_args,
        memory: "m".to_string(),
        event: Box::new(EcExpr::Var("res".to_string())),
    };
    let right_pr = EcExpr::Pr {
        module: format!(
            "{}.Exp_{}(A)",
            right_layout.comp_theory, right_layout.comp_mangled
        ),
        proc: "run".to_string(),
        args: right_run_args,
        memory: "m".to_string(),
        event: Box::new(EcExpr::Var("res".to_string())),
    };
    let statement = EcExpr::Binop {
        op: super::ast::EcBinop::Eq,
        lhs: Box::new(left_pr),
        rhs: Box::new(right_pr),
    };

    let lemma_name = lemma_names.mangle(
        NameKind::Lemma,
        &format!("{}_{}_equiv", left_game_inst.name(), right_game_inst.name()),
    )?;

    // --- restrictions: every router and every instance clone of both
    // sides, shared composition listed once (§3) ------------------------
    let mut restrictions = restrictions_for(&left_layout);
    if !same_composition {
        restrictions.extend(restrictions_for(&right_layout));
    }
    let adv_type = format!("Interfaces.{}", interfaces.adv_name[&left_comp.name]);
    let declare = DeclareModule {
        name: "A".to_string(),
        module_type: adv_type,
        restrictions,
    };

    // --- the invariant `call` --------------------------------------------
    let left_record = build_side_record_lit(left_comp, &left_layout, "l_", 1)?;
    let right_record = build_side_record_lit(right_comp, &right_layout, "r_", 2)?;
    let inv_app = EcExpr::App {
        head: "inv".to_string(),
        args: vec![left_record, right_record],
    };
    // story 69: the side invariants of both sides, assumed by each oracle lemma and joined in
    // by the glue
    let left_side = side_inv_app(left_comp, &left_layout, Some(1))?;
    let right_side = side_inv_app(right_comp, &right_layout, Some(2))?;
    let assumed: Vec<EcExpr> = left_side.iter().chain(&right_side).cloned().collect();

    // --- the byequiv induction start's own relational precondition
    // (story 15 §3.1): `={glob A}` then one `arg{side} = …` per side,
    // (a side whose run() takes no arguments contributes none), even when
    // both sides bind the same theorem constant ------------------------
    let precondition = build_byequiv_precondition(&left_args, &right_args, &binder_mangled);

    // --- oracle bullets: the game interface's own export order (§3;
    // load-bearing per story 04's own note) -----------------------------
    let mut proc_names = Names::new();
    let mut proof = vec![
        ProofLine::ByequivPrecondition {
            conjuncts: precondition,
        },
        plain_line("proc; inline."),
        ProofLine::InvariantCall {
            inv: inv_app.clone(),
            also: assumed.clone(),
        },
        blank_line(),
        // Story 19: one line. `t1; t2` runs `t2` on every goal `t1` leaves and
        // on none when `t1` closes the base case, so the `smt` can never fall
        // through onto the first oracle's goal.
        plain_line("auto => />; smt(emptyE map_empty)."),
    ];

    let stem = format!("Eq_{}_{}", left_game_inst.name(), right_game_inst.name());
    let theory_requires = theory_requires(
        &left_layout,
        &right_layout,
        same_composition,
        &stem,
        &state_files(owners, [left_comp, right_comp]),
    );
    // the side-invariant lemmas of an oracle, as `conseq` takes them: the left side's, then the
    // right side's; `_` for a left side without one when the right side has one
    let side_lemmas = |oracle: &str| -> Vec<String> {
        let lemma = |side: &Option<EcExpr>, layout: &CompLayout| {
            side.as_ref().map(|_| {
                let lemma = side_inv_oracle_stem(&layout.comp_mangled, oracle);
                format!("{lemma}.{lemma}")
            })
        };
        match (
            lemma(&left_side, &left_layout),
            lemma(&right_side, &right_layout),
        ) {
            (None, None) => vec![],
            (Some(l), None) => vec![l],
            (l, Some(r)) => vec![l.unwrap_or_else(|| "_".to_string()), r],
        }
    };
    let mut oracle_files = Vec::with_capacity(left_comp.exports.len());
    for export in &left_comp.exports {
        let proc_name = proc_names.mangle(NameKind::Proc, export.name())?;
        let oracle_stem = format!("{stem}_{}", export.name());
        let lemma_name = lemma_names.mangle(NameKind::Lemma, &oracle_stem)?;
        proof.push(blank_line());
        proof.push(plain_line(format!("(* {proc_name} *)")));
        let joined: String = side_lemmas(export.name())
            .iter()
            .map(|l| format!(" {l}"))
            .collect();
        proof.push(bullet_line(format!(
            "by conseq {lemma_name}{joined} => /#."
        )));
        let statement = EcExpr::OracleEquiv {
            left: format!(
                "{}.Game_{}.{proc_name}",
                left_layout.comp_theory, left_layout.comp_mangled
            ),
            right: format!(
                "{}.Game_{}.{proc_name}",
                right_layout.comp_theory, right_layout.comp_mangled
            ),
            inv: Box::new(inv_app.clone()),
            assumed: assumed.clone(),
        };
        oracle_files.push(OracleProofFile {
            oracle: export.name().to_string(),
            file_name: format!("{oracle_stem}.ec"),
            file: EcFile {
                header: vec![format!(
                    "{oracle_stem}.ec for theorem `{}`: the oracle lemma of `{}` — generated by \
                     `domino easycrypt`.",
                    theorem.name,
                    export.name()
                )],
                requires: theory_requires.clone(),
                items: vec![EcItem::Lemma(EcLemma {
                    name: lemma_name,
                    binders: vec![],
                    statement,
                    proof: vec![
                        plain_line(format!("(* {proc_name} *)")),
                        bullet_line("proc; inline. admit."),
                    ],
                })],
            },
        });
    }
    // `render_lemma` (`render.rs`) is the sole owner of the closing `qed.`
    // — story 13 §3.3: this used to push a second one here, rendering two
    // `qed.` per lemma.

    let oracle_count = left_comp.exports.len();

    // §3: warn (don't silently drop) if the proof trees cover a different
    // oracle set than the interface actually exports. The bullets above
    // always follow the interface's own export list regardless.
    let tree_oracle_names: HashSet<&str> = equivalence
        .trees()
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    let export_oracle_names: HashSet<&str> = left_comp.exports.iter().map(|e| e.name()).collect();
    let oracle_set_mismatch = if tree_oracle_names == export_oracle_names {
        None
    } else {
        let mut only_trees: Vec<&str> = tree_oracle_names
            .difference(&export_oracle_names)
            .copied()
            .collect();
        only_trees.sort_unstable();
        let mut only_exports: Vec<&str> = export_oracle_names
            .difference(&tree_oracle_names)
            .copied()
            .collect();
        only_exports.sort_unstable();
        Some(format!(
            "{} ~ {}: proof-tree oracle set differs from the game interface's exports \
             (only in proof trees: {}; only in exports: {})",
            left_game_inst.name(),
            right_game_inst.name(),
            if only_trees.is_empty() {
                "none".to_string()
            } else {
                only_trees.join(", ")
            },
            if only_exports.is_empty() {
                "none".to_string()
            } else {
                only_exports.join(", ")
            },
        ))
    };

    let mut items = Vec::new();
    if let Some(warning) = &oracle_set_mismatch {
        items.push(EcItem::Comment(format!(
            "warning: oracle set mismatch — {warning}"
        )));
    }
    items.push(EcItem::Section(EcSection {
        declares: vec![declare],
        assumptions: vec![],
        items: vec![],
        lemmas: vec![EcLemma {
            name: lemma_name,
            binders,
            statement,
            proof,
        }],
    }));

    let mut requires = theory_requires;
    let mut side_files: Vec<String> = Vec::new();
    for (side, layout) in [(&left_side, &left_layout), (&right_side, &right_layout)] {
        let file = side_inv_stem(&layout.comp_mangled);
        if side.is_some() && !side_files.contains(&file) {
            side_files.push(file);
        }
    }
    if !side_files.is_empty() {
        requires.push(Require {
            import: false,
            names: side_files,
        });
    }
    requires.push(Require {
        import: true,
        names: oracle_files
            .iter()
            .map(|o| o.file_name.trim_end_matches(".ec").to_string())
            .collect(),
    });
    let file = EcFile {
        header: vec![format!(
            "{stem}.ec for theorem `{}` — generated by `domino easycrypt`.",
            theorem.name
        )],
        requires,
        items,
    };

    Ok(EquivalenceProofFile {
        proofstep,
        file_name: format!("{stem}.ec"),
        file,
        oracle_files,
        left_name: left_game_inst.name().to_string(),
        right_name: right_game_inst.name().to_string(),
        oracle_count,
        admit_count: oracle_count,
        oracle_set_mismatch,
    })
}

/// What the glue and every oracle file of the equivalence `stem` require: the libraries, the
/// two compositions (one when both sides share it), the package files that declare the state
/// types of the record literals (`state_files`, story 69), and the invariant file.
fn theory_requires(
    left: &CompLayout,
    right: &CompLayout,
    same_composition: bool,
    stem: &str,
    state_files: &[String],
) -> Vec<Require> {
    let mut comp_requires = vec![left.comp_theory.clone()];
    if !same_composition {
        comp_requires.push(right.comp_theory.clone());
    }
    let mut requires = vec![
        Require {
            import: true,
            names: [
                "AllCore",
                "Distr",
                "FMap",
                "Int",
                "IntDiv",
                "Types",
                "Interfaces",
            ]
            .map(String::from)
            .to_vec(),
        },
        Require {
            import: false,
            names: comp_requires,
        },
    ];
    if !state_files.is_empty() {
        requires.push(Require {
            import: true,
            names: state_files.to_vec(),
        });
    }
    requires.push(Require {
        import: true,
        names: vec![format!("{stem}_Invariants")],
    });
    requires
}

/// The package files (`Pkg_<V>`, without `.ec`) that declare the `<Pkg>_pkgstate` of every
/// package with state in `comps`, or its `<Pkg>_pkgparams` (story 78), each one time, in order
/// (story 69).
pub(super) fn state_files<'c>(
    owners: &invariant::StateOwners,
    comps: impl IntoIterator<Item = &'c Composition>,
) -> Vec<String> {
    let mut files: Vec<String> = Vec::new();
    for comp in comps {
        let declares = |i: &&crate::package::PackageInstance| {
            !i.pkg.state.is_empty() || invariant::has_pkg_params(&i.pkg)
        };
        for inst in comp.pkgs.iter().filter(declares) {
            let file = owners.file_of(&inst.pkg.name);
            if !files.contains(&file) {
                files.push(file);
            }
        }
    }
    files
}

/// The file of composition `comp`'s side-invariant lemmas that joins them, without `.ec`:
/// `SideInv_<C>` (story 69). `comp` is the composition's EasyCrypt name.
pub(super) fn side_inv_stem(comp: &str) -> String {
    format!("SideInv_{comp}")
}

/// The side-invariant lemma of `oracle` of composition `comp`, and its file without `.ec`:
/// `SideInv_<C>_<O>` (story 69).
pub(super) fn side_inv_oracle_stem(comp: &str, oracle: &str) -> String {
    format!("SideInv_{comp}_{oracle}")
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::project::{DirectoryFiles, DirectoryProject, Project};
    use crate::transforms::theorem_transforms::EasyCryptTransform;
    use crate::transforms::TheoremTransform;

    use super::super::interfaces::build_interfaces_file;
    use super::super::render::{render_expr, render_file};
    use super::*;

    fn load(dir: &str, theorem_name: &str) -> Vec<EquivalenceFiles> {
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject = Box::leak(Box::new(
            DirectoryProject::load(PathBuf::from(dir), files).unwrap(),
        ));
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, _auxs) = EasyCryptTransform.transform_theorem(theorem).unwrap();
        let interfaces = build_interfaces_file(&theorem).unwrap();
        compute_equivalence_files(&theorem, project, &interfaces).unwrap()
    }

    #[test]
    fn simple_4whs_produces_the_three_translated_equivalence_hops() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let names: Vec<&str> = files.iter().map(|f| f.proof.file_name.as_str()).collect();
        assert_eq!(
            names,
            vec![
                "Eq_Hybrid0_Hybrid1.ec",
                "Eq_Hybrid1_Hybrid2.ec",
                "Eq_Real_Hybrid3_Ideal_Hybrid3.ec",
            ]
        );
    }

    #[test]
    fn hybrid0_hybrid1_bullet_order_matches_export_order() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let f = &files[0];
        assert_eq!(f.proof.oracle_count, 9);
        assert_eq!(f.proof.admit_count, 9);
        let comments: Vec<&str> = f
            .proof
            .file
            .items
            .iter()
            .find_map(|item| match item {
                EcItem::Section(s) => Some(&s.lemmas[0].proof),
                _ => None,
            })
            .unwrap()
            .iter()
            .filter_map(|l| match l {
                ProofLine::Tactic { text, .. } => {
                    text.strip_prefix("(* ").and_then(|s| s.strip_suffix(" *)"))
                }
                ProofLine::ByequivPrecondition { .. } | ProofLine::InvariantCall { .. } => None,
            })
            .collect();
        assert_eq!(
            comments,
            vec![
                "d_NewKey",
                "d_NewSession",
                "d_Send1",
                "d_Send2",
                "d_Send3",
                "d_Send4",
                "d_Send5",
                "d_Reveal",
                "d_Test",
            ]
        );
    }

    #[test]
    fn real_hybrid3_ideal_hybrid3_shares_one_composition_in_restrictions_and_requires() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let f = files
            .iter()
            .find(|f| f.proof.file_name == "Eq_Real_Hybrid3_Ideal_Hybrid3.ec")
            .unwrap();
        let section = f
            .proof
            .file
            .items
            .iter()
            .find_map(|item| match item {
                EcItem::Section(s) => Some(s),
                _ => None,
            })
            .unwrap();
        // Only one `-Comp_Hybrid2.Game_Hybrid2` restriction, not two.
        let router_restrictions = section.declares[0]
            .restrictions
            .iter()
            .filter(|r| r.ends_with(".Game_Hybrid2"))
            .count();
        assert_eq!(router_restrictions, 1);

        // `require Comp_Hybrid2.` once, not `require Comp_Hybrid2 Comp_Hybrid2.`.
        let comp_require = f
            .proof
            .file
            .requires
            .iter()
            .find(|r| !r.import && r.names.contains(&"Comp_Hybrid2".to_string()))
            .unwrap();
        assert_eq!(comp_require.names, vec!["Comp_Hybrid2".to_string()]);
    }

    #[test]
    fn real_hybrid3_ideal_hybrid3_run_args_are_different_literals() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let f = files
            .iter()
            .find(|f| f.proof.file_name == "Eq_Real_Hybrid3_Ideal_Hybrid3.ec")
            .unwrap();
        let section = f
            .proof
            .file
            .items
            .iter()
            .find_map(|item| match item {
                EcItem::Section(s) => Some(s),
                _ => None,
            })
            .unwrap();
        let statement = &section.lemmas[0].statement;
        let rendered = render_expr(statement);
        assert!(rendered.contains("run(false, true)"), "{rendered}");
        assert!(rendered.contains("run(true, true)"), "{rendered}");
    }

    /// The `byequiv` precondition's own conjuncts (story 13 §3.1), rendered
    /// individually — always `f.proof.file`'s one lemma's first proof line.
    fn precondition_conjuncts(f: &EquivalenceProofFile) -> Vec<String> {
        let section = f
            .file
            .items
            .iter()
            .find_map(|item| match item {
                EcItem::Section(s) => Some(s),
                _ => None,
            })
            .unwrap();
        match &section.lemmas[0].proof[0] {
            ProofLine::ByequivPrecondition { conjuncts } => {
                conjuncts.iter().map(render_expr).collect()
            }
            other => panic!(
                "expected the first proof line to be the byequiv precondition, got {other:?}"
            ),
        }
    }

    #[test]
    fn real_hybrid3_ideal_hybrid3_precondition_is_one_arg_tuple_per_side() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let f = &files
            .iter()
            .find(|f| f.proof.file_name == "Eq_Real_Hybrid3_Ideal_Hybrid3.ec")
            .unwrap()
            .proof;
        assert_eq!(
            precondition_conjuncts(f),
            vec![
                "={glob A}".to_string(),
                "arg{1} = (false, true)".to_string(),
                "arg{2} = (true, true)".to_string(),
            ]
        );
    }

    #[test]
    fn hybrid0_hybrid1_precondition_lists_both_sides_of_the_shared_binder() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let f = &files
            .iter()
            .find(|f| f.proof.file_name == "Eq_Hybrid0_Hybrid1.ec")
            .unwrap()
            .proof;
        // Both sides bind the *same* theorem constant `b` — both sides are
        // still listed (`arg{1} = b /\ arg{2} = b`), never collapsed into
        // `={b}` or `arg{1} = arg{2}`. One argument per side renders as the
        // bare value, not a one-tuple (story 15 §3.1).
        assert_eq!(
            precondition_conjuncts(f),
            vec![
                "={glob A}".to_string(),
                "arg{1} = b".to_string(),
                "arg{2} = b".to_string(),
            ]
        );
    }

    #[test]
    fn hybrid1_hybrid2_precondition_has_a_tuple_on_the_side_with_two_arguments() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let f = &files
            .iter()
            .find(|f| f.proof.file_name == "Eq_Hybrid1_Hybrid2.ec")
            .unwrap()
            .proof;
        assert_eq!(
            precondition_conjuncts(f),
            vec![
                "={glob A}".to_string(),
                "arg{1} = b".to_string(),
                "arg{2} = (b, false)".to_string(),
            ]
        );
    }

    #[test]
    fn full_4whs_h0_h1_0_precondition_has_different_arities_per_side() {
        let files = load("example-projects/4WHS", "Full4WHS");
        let f = &files
            .iter()
            .find(|f| f.proof.file_name == "Eq_H0_H1_0.ec")
            .unwrap()
            .proof;
        // H0 takes one argument, H1 takes two — the reason the two sides are
        // never collapsed into `arg{1} = arg{2}`.
        assert_eq!(
            precondition_conjuncts(f),
            vec![
                "={glob A}".to_string(),
                "arg{1} = b".to_string(),
                "arg{2} = (b, false)".to_string(),
            ]
        );
    }

    #[test]
    fn no_precondition_names_a_run_parameter_directly() {
        // Story 15 §1: `<param>{side} = <value>` is voided by a lemma binder
        // spelled like the parameter. Every conjunct must go through `arg`.
        for (root, theorem) in [
            ("example-projects/4WHS", "Simple4WHS"),
            ("example-projects/4WHS", "Full4WHS"),
        ] {
            for f in &load(root, theorem) {
                for c in precondition_conjuncts(&f.proof).iter().skip(1) {
                    assert!(
                        c.starts_with("arg{1} = ") || c.starts_with("arg{2} = "),
                        "{}: {c}",
                        f.proof.file_name
                    );
                }
            }
        }
    }

    #[test]
    fn a_side_with_no_run_arguments_contributes_no_conjunct() {
        let binders = HashMap::new();
        let rendered = |args: &[RunArgValue], other: &[RunArgValue]| -> Vec<String> {
            build_byequiv_precondition(args, other, &binders)
                .iter()
                .map(render_expr)
                .collect()
        };
        let lit = |t: &str| RunArgValue::Literal(t.to_string());
        assert_eq!(rendered(&[], &[]), vec!["={glob A}"]);
        assert_eq!(
            rendered(&[], &[lit("true")]),
            vec!["={glob A}", "arg{2} = true"]
        );
        assert_eq!(
            rendered(&[lit("true"), lit("3")], &[]),
            vec!["={glob A}", "arg{1} = (true, 3)"]
        );
    }

    #[test]
    fn every_generated_lemma_has_exactly_one_qed() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        for f in &files {
            let rendered = render_file(&f.proof.file);
            assert_eq!(
                rendered.matches("qed.").count(),
                1,
                "{}:\n{rendered}",
                f.proof.file_name
            );
        }
    }

    #[test]
    fn the_invariant_call_puts_each_record_on_its_own_line_and_one_field_per_line() {
        // Story 43 §3.3.
        let files = load("example-projects/hello-world", "Proof");
        let rendered = render_file(&files[0].proof.file);
        let expected = concat!(
            "call (: inv\n",
            "          {| l_pkg_rand = {| Rand_ctr = Comp_MediumComposition.Pkg_Inst_Rand.ctr{1} |};\n",
            "             l_pkg_fwd = {| Fwd_ctr = Comp_MediumComposition.Pkg_Inst_Fwd.ctr{1} |};\n",
            "             l_abort_flag = Comp_MediumComposition.Game_MediumComposition.abort_flag{1} |}\n",
            "          {| r_pkg_rand = {| Rand_ctr = Comp_SmallComposition.Pkg_Inst_Rand.ctr{2} |};\n",
            "             r_abort_flag = Comp_SmallComposition.Game_SmallComposition.abort_flag{2} |}); last first.\n",
        );
        assert!(rendered.contains(expected), "{rendered}");
        // the readers of the skeleton still find it as one sentence
        let sentences = crate::easycrypt::session::split_sentences(&rendered);
        assert!(sentences.iter().any(|s| s.starts_with("call")
            && s.ends_with("last first.")
            && s.contains("r_abort_flag")));
    }

    #[test]
    fn the_invariant_call_nests_one_package_record_per_instance_with_state_then_the_parameters() {
        // Story 42 §3.5, on `testdata/easycrypt/story42/params`.
        let files = load("testdata/easycrypt/story42/params", "Params");
        let rendered = render_file(&files[0].proof.file);
        let expected = concat!(
            "call (: inv\n",
            "          {| l_pkg_Store = {| Ctr_ctr = Comp_Left.Pkg_Inst_Store.ctr{1} |};\n",
            "             l_pkg_OnlyL = {| Ctr_ctr = Comp_Left.Pkg_Inst_OnlyL.ctr{1} |};\n",
            "             l_pkg_T = {| Twin_n = Comp_Left.Pkg_Inst_T.n{1} |};\n",
            "             l_pkg_Store_b = Comp_Left.Pkg_Inst_Store.b{1};\n",
            "             l_pkg_OnlyL_b = Comp_Left.Pkg_Inst_OnlyL.b{1};\n",
            "             l_pkg_Front_b = Comp_Left.Pkg_Inst_Front.b{1};\n",
            "             l_pkg_T_b1 = Comp_Left.Pkg_Inst_T.b1{1};\n",
            "             l_pkg_T_b2 = Comp_Left.Pkg_Inst_T.b2{1};\n",
            "             l_abort_flag = Comp_Left.Game_Left.abort_flag{1} |}\n",
        );
        assert!(rendered.contains(expected), "{rendered}");
    }

    #[test]
    fn rendering_is_deterministic() {
        let a = load("example-projects/4WHS", "Simple4WHS");
        let b = load("example-projects/4WHS", "Simple4WHS");
        for (fa, fb) in a.iter().zip(b.iter()) {
            assert_eq!(render_file(&fa.proof.file), render_file(&fb.proof.file));
        }
    }
}
