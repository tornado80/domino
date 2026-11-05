// SPDX-License-Identifier: MIT OR Apache-2.0

//! Building `Red_<L>_<R>.ec` for each reduction hop (story 98, ADR 0022 decisions 1–3 and 8):
//! the **reduction router** `Red_<hop>(O)`, the **reduction adversary** `B_<hop>(A)(O)` and
//! the **reduction experiment(s)** `RedExp_<hop>(A)` (or `RedExp_<hop>_L`/`_R` when the two
//! assumption games are different compositions). Story 99 adds the lemmas to the same file
//! (`reduction_lemmas`).
//!
//! The router is built from the **left** game instance's reduction packages, with their
//! instance names (story 97). A call that reaches a mapped package goes to `O`, under the name
//! of the assumption game's export that reaches the same oracle of the paired assumption
//! package. The experiment calls `B_<hop>(A, Game_<Assm>).setup(..)`: EasyCrypt needs every
//! functor argument to call a procedure (story 97's deviation from ADR 0022).

use std::collections::HashMap;

use miette::SourceSpan;

use crate::gamehops::reduction::Reduction;
use crate::gamehops::GameHop;
use crate::identifier::Identifier;
use crate::package::{Composition, Edge};
use crate::parser::ast::Identifier as _;
use crate::parser::reduction::ReductionMapping;
use crate::theorem::{GameInstance, Theorem};

use super::ast::Require;
use super::ast::{EcBlock, EcExpr, EcFile, EcItem, EcLvalue, EcModule, EcProc, EcStmt, EcType};
use super::game::{
    composition_const_needs_arg, guarded_export_proc, import_adapter, instance_wirings,
    param_assignment, references_game_const, resolve_composition_const, InstanceWiring,
};
use super::interfaces::{composition_span, InterfacesOutput};
use super::names::{NameKind, Names};
use super::package::{param_needs_var, pkg_needs_init};
use super::reduction_lemmas::{reduction_lemmas, LemmaInput, ReductionLemmas};
use super::proof::{literal_text_to_expr, side_run_args, RunArgValue};
use super::types::{translate_expr, translate_type};
use super::EcExportError;

/// One reduction hop's file, `Red_<L>_<R>.ec`.
pub struct ReductionFile {
    /// Index of the hop in `theorem.game_hops`.
    pub proofstep: usize,
    pub left_name: String,
    pub right_name: String,
    pub assumption_name: String,
    pub file_name: String,
    pub file: EcFile,
    /// The reduction packages, `(left instance, right instance)`, as the parser pairs them.
    pub package_pairs: Vec<(String, String)>,
    /// The hop's left side, then its right side.
    pub sides: [ReductionSide; 2],
    /// The names of the two reduction equivalences and the bound lemma (story 99).
    pub lemmas: ReductionLemmas,
}

/// What the lemmas of one side of a reduction hop need (story 99).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReductionSide {
    /// The assumption game instance that the map of this side names.
    pub assumption_game: String,
    /// The reduction experiment of this side, `RedExp_<hop>` or `RedExp_<hop>_<L|R>`.
    pub experiment: String,
    /// The values of the assumption experiment's `run` arguments for this side: a literal, or
    /// the name of a theorem constant.
    pub assumption_args: Vec<String>,
}

/// One `Red_<L>_<R>.ec` for each reduction hop of `theorem`, in `theorem.game_hops` order.
/// Reductions inside a hybrid hop are not translated (ADR 0022, decision 7).
pub fn compute_reduction_files(
    theorem: &Theorem<'_>,
    interfaces: &InterfacesOutput,
) -> Result<Vec<ReductionFile>, EcExportError> {
    let mut out = Vec::new();
    for (proofstep, hop) in theorem.game_hops.iter().enumerate() {
        if let GameHop::Reduction(red) = hop {
            out.push(build_reduction_file(theorem, interfaces, proofstep, red)?);
        }
    }
    Ok(out)
}

fn instance<'t>(theorem: &'t Theorem<'_>, name: &str) -> &'t GameInstance {
    theorem
        .find_game_instance(name)
        .expect("the parser resolved every game instance a reduction names")
}

/// The left game's composition, seen against the assumption game of its map.
struct RouterCtx<'t> {
    comp: &'t Composition,
    assm: &'t Composition,
    /// Index into `comp.pkgs` of a mapped package -> index into `assm.pkgs` of its partner.
    mapped: HashMap<usize, usize>,
    wiring: Vec<InstanceWiring>,
    /// `Interfaces.Iface_<Assm>`.
    assm_iface: String,
}

impl RouterCtx<'_> {
    /// `O.d_<e>`'s proc name, where `e` is the assumption game's export that reaches `oracle`
    /// of the partner of the mapped package `idx`; `None` when `idx` is a reduction package.
    fn mapped_proc(&self, idx: usize, oracle: &str) -> Result<Option<String>, EcExportError> {
        let Some(&a_idx) = self.mapped.get(&idx) else {
            return Ok(None);
        };
        let export = self
            .assm
            .exports
            .iter()
            .find(|e| e.to() == a_idx && e.sig().name == oracle)
            .expect("the parser checks that the assumption exports every oracle the map uses");
        Ok(Some(Names::new().mangle(NameKind::Proc, export.name())?))
    }

    /// The module of reduction package `idx`: `Pkg_Inst_<m>`, applied to `O` when the package
    /// has imports (its import adapter is a functor over the assumption interface).
    fn module(&self, idx: usize) -> String {
        let name = format!("Pkg_Inst_{}", self.wiring[idx].mangled);
        if self.comp.pkgs[idx].pkg.imports.is_empty() {
            name
        } else {
            format!("{name}(O)")
        }
    }

    fn o_param(&self) -> Vec<(String, String)> {
        vec![("O".to_string(), self.assm_iface.clone())]
    }

    fn reduction_order(&self) -> Vec<usize> {
        self.comp
            .ordered_pkgs_idx()
            .into_iter()
            .filter(|idx| !self.mapped.contains_key(idx))
            .collect()
    }
}

fn router_ctx<'t>(
    theorem: &'t Theorem<'_>,
    interfaces: &InterfacesOutput,
    mapping: &ReductionMapping<'_>,
) -> Result<RouterCtx<'t>, EcExportError> {
    let comp = instance(theorem, mapping.construction_game_instance_name().as_str()).game();
    let assm = instance(theorem, mapping.assumption_game_instance_name().as_str()).game();
    let index = |c: &Composition, name: &str| {
        c.pkgs
            .iter()
            .position(|p| p.name == name)
            .expect("the parser resolved every package instance of a map")
    };
    let mapped = mapping
        .entries()
        .iter()
        .map(|e| {
            (
                index(comp, e.construction().as_str()),
                index(assm, e.assumption().as_str()),
            )
        })
        .collect();
    Ok(RouterCtx {
        comp,
        assm,
        mapped,
        wiring: instance_wirings(theorem, comp)?,
        assm_iface: format!("Interfaces.{}", interfaces.iface_name[&assm.name]),
    })
}

/// The clones, import adapters and `Pkg_Inst_<m>` aliases of the reduction packages.
fn reduction_package_items(ctx: &RouterCtx<'_>) -> Result<Vec<EcItem>, EcExportError> {
    let order = ctx.reduction_order();
    let mut items: Vec<EcItem> = order
        .iter()
        .map(|&idx| EcItem::Clone {
            base: format!("Pkg_{}", ctx.wiring[idx].variant),
            as_name: format!("Cloned_Pkg_{}", ctx.wiring[idx].mangled),
            overrides: vec![],
        })
        .collect();
    for &idx in &order {
        let w = &ctx.wiring[idx];
        let functor = format!("Cloned_Pkg_{}.{}", w.mangled, w.variant);
        let name = format!("Pkg_Inst_{}", w.mangled);
        if ctx.comp.pkgs[idx].pkg.imports.is_empty() {
            items.push(EcItem::ModuleAlias {
                name,
                params: vec![],
                functor,
                args: vec![],
            });
            continue;
        }
        let adapter_name = format!("Pkg_Imports_{}", w.mangled);
        let target = |edge: &Edge| -> Result<(String, String), EcExportError> {
            let oracle = &edge.sig().name;
            Ok(match ctx.mapped_proc(edge.to(), oracle)? {
                Some(proc) => ("O".to_string(), proc),
                None => (
                    ctx.module(edge.to()),
                    Names::new().mangle(NameKind::Proc, oracle)?,
                ),
            })
        };
        let adapter = import_adapter(
            ctx.comp,
            idx,
            &adapter_name,
            ctx.o_param(),
            &w.variant,
            &target,
        )?;
        items.push(EcItem::Module(adapter));
        items.push(EcItem::ModuleAlias {
            name,
            params: ctx.o_param(),
            functor,
            args: vec![format!("{adapter_name}(O)")],
        });
    }
    Ok(items)
}

/// The composition constants that the router's `init` takes: those that a reduction package's
/// parameter reads and that are not width-only, in `comp.consts` order.
fn router_init_consts(ctx: &RouterCtx<'_>) -> Vec<(String, crate::types::Type)> {
    let order = ctx.reduction_order();
    ctx.comp
        .consts
        .iter()
        .filter(|(name, ty)| {
            composition_const_needs_arg(ctx.comp, name, ty)
                && order.iter().any(|&idx| {
                    let inst = &ctx.comp.pkgs[idx];
                    inst.pkg.params.iter().any(|(p, pty, _)| {
                        param_needs_var(&inst.pkg, p, pty)
                            && references_game_const(param_assignment(inst, p), name)
                    })
                })
        })
        .cloned()
        .collect()
}

/// `Red_<hop> (O : Iface_<Assm>) : Iface_<G>`.
fn router_module(
    ctx: &RouterCtx<'_>,
    name: &str,
    iface: &str,
    span: SourceSpan,
) -> Result<EcModule, EcExportError> {
    let mut names = Names::new();
    let abort_flag = names.mangle(NameKind::Var, "abort_flag")?;
    let mut init_args = Vec::new();
    for (c, ty) in router_init_consts(ctx) {
        init_args.push((names.mangle(NameKind::Var, &c)?, translate_type(&ty, span)?));
    }
    let mut init_body = vec![EcStmt::Assign {
        lhs: EcLvalue::Var(abort_flag.clone()),
        rhs: EcExpr::Bool(false),
    }];
    for idx in ctx.reduction_order() {
        let inst = &ctx.comp.pkgs[idx];
        if !pkg_needs_init(&inst.pkg) {
            continue;
        }
        let mut args = Vec::new();
        for (p, pty, pspan) in &inst.pkg.params {
            if !param_needs_var(&inst.pkg, p, pty) {
                continue;
            }
            let mut resolver =
                |id: &Identifier, s: SourceSpan| resolve_composition_const(id, s, &mut names);
            args.push(translate_expr(
                param_assignment(inst, p),
                *pspan,
                &mut resolver,
            )?);
        }
        init_body.push(EcStmt::Call {
            lhs: None,
            module: ctx.module(idx),
            proc: "init".to_string(),
            args,
        });
    }
    let mut procs = vec![EcProc {
        name: "init".to_string(),
        args: init_args,
        ret: EcType::Unit,
        locals: vec![],
        body: EcBlock(init_body),
        ret_expr: None,
    }];
    for export in &ctx.comp.exports {
        let oracle = &export.sig().name;
        let (module, proc) = match ctx.mapped_proc(export.to(), oracle)? {
            Some(proc) => ("O".to_string(), proc),
            None => (
                ctx.module(export.to()),
                Names::new().mangle(NameKind::Proc, oracle)?,
            ),
        };
        procs.push(guarded_export_proc(
            &mut names,
            export,
            span,
            &abort_flag,
            &module,
            proc,
        )?);
    }
    Ok(EcModule {
        name: name.to_string(),
        params: ctx.o_param(),
        implements: Some(format!("Interfaces.{iface}")),
        vars: vec![(abort_flag, EcType::Bool)],
        procs,
    })
}

/// A constant `B_<hop>` stores, one for each theorem constant that a router `init` argument
/// reads, first-use order.
pub(super) struct StoredConst {
    /// The variable of `B_<hop>`, also the name of `RedExp`'s `run` argument.
    pub var: String,
    /// The argument of `setup`.
    pub arg: String,
    pub ty: EcType,
    /// The theorem constant.
    pub theorem_const: String,
}

/// The adversary's stored constants and the arguments of its router `init` call.
fn adversary_init(
    theorem: &Theorem<'_>,
    ctx: &RouterCtx<'_>,
    left: &GameInstance,
    span: SourceSpan,
) -> Result<(Vec<StoredConst>, Vec<EcExpr>), EcExportError> {
    let mut stored: Vec<StoredConst> = Vec::new();
    let mut args = Vec::new();
    let mut names = Names::new();
    for (c, _) in router_init_consts(ctx) {
        let assigned = left
            .consts
            .iter()
            .find(|(id, _)| id.name == c)
            .map(|(_, e)| e)
            .expect("a game instance binds every one of its composition's consts");
        match super::proof::resolve_run_arg(assigned) {
            Some(RunArgValue::Literal(text)) => args.push(literal_text_to_expr(&text)),
            Some(RunArgValue::TheoremConst(t)) => {
                let var = names.mangle(NameKind::Var, &t)?;
                if !stored.iter().any(|s| s.var == var) {
                    let ty = theorem
                        .consts
                        .iter()
                        .find(|(n, _)| n == &t)
                        .map(|(_, ty)| ty)
                        .expect("the parser resolved every theorem constant");
                    stored.push(StoredConst {
                        var: var.clone(),
                        arg: format!("{var}0"),
                        ty: translate_type(ty, span)?,
                        theorem_const: t.clone(),
                    });
                }
                args.push(EcExpr::Var(var));
            }
            None => unreachable!(
                "a game instance's composition-const binding is a literal or a theorem constant"
            ),
        }
    }
    Ok((stored, args))
}

fn b_module(
    name: &str,
    router: &str,
    adv: &str,
    assm_iface: &str,
    stored: &[StoredConst],
    init_args: Vec<EcExpr>,
) -> EcModule {
    let setup = EcProc {
        name: "setup".to_string(),
        args: stored
            .iter()
            .map(|s| (s.arg.clone(), s.ty.clone()))
            .collect(),
        ret: EcType::Unit,
        locals: vec![],
        body: EcBlock(
            stored
                .iter()
                .map(|s| EcStmt::Assign {
                    lhs: EcLvalue::Var(s.var.clone()),
                    rhs: EcExpr::Var(s.arg.clone()),
                })
                .collect(),
        ),
        ret_expr: None,
    };
    let run = EcProc {
        name: "run".to_string(),
        args: vec![],
        ret: EcType::Bool,
        locals: vec![("b'".to_string(), EcType::Bool, None)],
        body: EcBlock(vec![
            EcStmt::Call {
                lhs: None,
                module: format!("{router}(O)"),
                proc: "init".to_string(),
                args: init_args,
            },
            EcStmt::Call {
                lhs: Some(EcLvalue::Var("b'".to_string())),
                module: format!("A({router}(O))"),
                proc: "run".to_string(),
                args: vec![],
            },
        ]),
        ret_expr: Some(EcExpr::Var("b'".to_string())),
    };
    EcModule {
        name: name.to_string(),
        params: vec![
            ("A".to_string(), format!("Interfaces.{adv}")),
            ("O".to_string(), assm_iface.to_string()),
        ],
        implements: None,
        vars: stored
            .iter()
            .map(|s| (s.var.clone(), s.ty.clone()))
            .collect(),
        procs: vec![setup, run],
    }
}

/// `RedExp_<hop>[_<L|R>] (A : Adv_<G>)`, whose `run` takes `B`'s constants, then the `run`
/// arguments of the assumption composition `assm`'s experiment.
fn red_exp_module(
    name: &str,
    b: &str,
    adv: &str,
    stored: &[StoredConst],
    assm: &Composition,
    assm_mangled: &str,
    span: SourceSpan,
) -> Result<EcModule, EcExportError> {
    let mut args: Vec<(String, EcType)> = stored
        .iter()
        .map(|s| (s.var.clone(), s.ty.clone()))
        .collect();
    let mut exp_args = Vec::new();
    for (c, ty) in &assm.consts {
        if !composition_const_needs_arg(assm, c, ty) {
            continue;
        }
        let mut arg = Names::new().mangle(NameKind::Var, c)?;
        while args.iter().any(|(a, _)| a == &arg) {
            arg.push_str("_a");
        }
        args.push((arg.clone(), translate_type(ty, span)?));
        exp_args.push(EcExpr::Var(arg));
    }
    let game = format!("Comp_{assm_mangled}.Game_{assm_mangled}");
    let run = EcProc {
        name: "run".to_string(),
        args,
        ret: EcType::Bool,
        locals: vec![("b'".to_string(), EcType::Bool, None)],
        body: EcBlock(vec![
            EcStmt::Call {
                lhs: None,
                module: format!("{b}(A, {game})"),
                proc: "setup".to_string(),
                args: stored
                    .iter()
                    .map(|s| EcExpr::Var(s.var.clone()))
                    .collect(),
            },
            EcStmt::Call {
                lhs: Some(EcLvalue::Var("b'".to_string())),
                module: format!("Comp_{assm_mangled}.Exp_{assm_mangled}({b}(A))"),
                proc: "run".to_string(),
                args: exp_args,
            },
        ]),
        ret_expr: Some(EcExpr::Var("b'".to_string())),
    };
    Ok(EcModule {
        name: name.to_string(),
        params: vec![("A".to_string(), format!("Interfaces.{adv}"))],
        implements: None,
        vars: vec![],
        procs: vec![run],
    })
}

fn render_run_arg(v: &RunArgValue) -> String {
    match v {
        RunArgValue::Literal(text) | RunArgValue::TheoremConst(text) => text.clone(),
    }
}

pub(super) fn push_unique(list: &mut Vec<String>, item: String) {
    if !list.contains(&item) {
        list.push(item);
    }
}

fn build_reduction_file(
    theorem: &Theorem<'_>,
    interfaces: &InterfacesOutput,
    proofstep: usize,
    red: &Reduction<'_>,
) -> Result<ReductionFile, EcExportError> {
    let left = instance(
        theorem,
        red.left().construction_game_instance_name().as_str(),
    );
    let right = instance(
        theorem,
        red.right().construction_game_instance_name().as_str(),
    );
    let stem = format!("{}_{}", left.name(), right.name());
    let ctx = router_ctx(theorem, interfaces, red.left())?;
    let span = composition_span(ctx.comp);
    let iface = &interfaces.iface_name[&ctx.comp.name];
    let adv = &interfaces.adv_name[&ctx.comp.name];

    let router_name = format!("Red_{stem}");
    let b_name = format!("B_{stem}");
    let mut items = reduction_package_items(&ctx)?;
    items.push(EcItem::Module(router_module(
        &ctx,
        &router_name,
        iface,
        span,
    )?));
    let (stored, init_args) = adversary_init(theorem, &ctx, left, span)?;
    items.push(EcItem::Module(b_module(
        &b_name,
        &router_name,
        adv,
        &ctx.assm_iface,
        &stored,
        init_args,
    )));

    let assm_insts = [red.left(), red.right()]
        .map(|m| instance(theorem, m.assumption_game_instance_name().as_str()));
    let same = assm_insts[0].game().name == assm_insts[1].game().name;
    let mut experiments = Vec::new();
    for (inst, suffix) in assm_insts.iter().zip(["_L", "_R"]) {
        let name = if same {
            format!("RedExp_{stem}")
        } else {
            format!("RedExp_{stem}{suffix}")
        };
        if !experiments.contains(&name) {
            let assm = inst.game();
            let module = red_exp_module(
                &name,
                &b_name,
                adv,
                &stored,
                assm,
                &interfaces.comp_mangled[&assm.name],
                span,
            )?;
            items.push(EcItem::Module(module));
        }
        experiments.push(name);
    }
    let sides = [0, 1].map(|i| ReductionSide {
        assumption_game: assm_insts[i].name().to_string(),
        experiment: experiments[i].clone(),
        assumption_args: side_run_args(assm_insts[i].game(), assm_insts[i])
            .iter()
            .map(render_run_arg)
            .collect(),
    });

    let reduction_order = ctx.reduction_order();
    let lemmas = reduction_lemmas(
        theorem,
        interfaces,
        red,
        &LemmaInput {
            stem: &stem,
            router: &router_name,
            adversary: &b_name,
            adv,
            router_comp: ctx.comp,
            router_wiring: &ctx.wiring,
            reduction_order: &reduction_order,
            stored: &stored,
            experiments: [&sides[0].experiment, &sides[1].experiment],
        },
        &mut items,
    )?;

    let mut plain = vec!["Interfaces".to_string()];
    for idx in ctx.reduction_order() {
        push_unique(&mut plain, format!("Pkg_{}", ctx.wiring[idx].variant));
    }
    for comp in [
        left.game(),
        right.game(),
        assm_insts[0].game(),
        assm_insts[1].game(),
    ] {
        push_unique(
            &mut plain,
            format!("Comp_{}", interfaces.comp_mangled[&comp.name]),
        );
    }

    let mut header = vec![format!(
        "Red_{stem}.ec for theorem `{}`, the reduction `{} ~ {}` to assumption `{}` — \
         generated by `domino easycrypt`.",
        theorem.name,
        left.name(),
        right.name(),
        red.assumption_name()
    )];
    for (side, label) in sides.iter().zip(["Left", "Right"]) {
        header.push(format!(
            "{label} side: assumption game `{}`, `{}.run` with the assumption arguments ({}).",
            side.assumption_game,
            side.experiment,
            side.assumption_args.join(", ")
        ));
    }
    let pairs: Vec<String> = red
        .package_pairs()
        .iter()
        .map(|(l, r)| format!("{l} ~ {r}"))
        .collect();
    header.push(format!(
        "Reduction packages (left ~ right): {}. The router uses the left names.",
        if pairs.is_empty() {
            "none".to_string()
        } else {
            pairs.join(", ")
        }
    ));

    Ok(ReductionFile {
        proofstep,
        left_name: left.name().to_string(),
        right_name: right.name().to_string(),
        assumption_name: red.assumption_name().to_string(),
        file_name: format!("Red_{stem}.ec"),
        file: EcFile {
            header,
            requires: vec![
                Require {
                    import: true,
                    names: ["AllCore", "Distr", "FMap", "Int", "IntDiv", "Types"]
                        .map(String::from)
                        .to_vec(),
                },
                Require {
                    import: false,
                    names: plain,
                },
            ],
            items,
        },
        package_pairs: red.package_pairs().to_vec(),
        sides,
        lemmas,
    })
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::project::{DirectoryFiles, DirectoryProject, Project};
    use crate::transforms::theorem_transforms::EasyCryptTransform;
    use crate::transforms::TheoremTransform;

    use super::super::interfaces::build_interfaces_file;
    use super::super::render::render_file;
    use super::*;

    fn load(dir: &str, theorem_name: &str) -> Vec<ReductionFile> {
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject = Box::leak(Box::new(
            DirectoryProject::load(PathBuf::from(dir), files).unwrap(),
        ));
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, _auxs) = EasyCryptTransform.transform_theorem(theorem).unwrap();
        let interfaces = build_interfaces_file(&theorem).unwrap();
        compute_reduction_files(&theorem, &interfaces).unwrap()
    }

    fn module<'f>(f: &'f ReductionFile, name: &str) -> &'f EcModule {
        f.file
            .items
            .iter()
            .find_map(|i| match i {
                EcItem::Module(m) if m.name == name => Some(m),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no module {name} in {}", render_file(&f.file)))
    }

    fn proc<'m>(m: &'m EcModule, name: &str) -> &'m EcProc {
        m.procs.iter().find(|p| p.name == name).unwrap()
    }

    #[test]
    fn hello_world_reduction_has_two_experiments_and_uses_the_left_names() {
        let files = load("example-projects/hello-world", "Proof");
        assert_eq!(files.len(), 1);
        let f = &files[0];
        assert_eq!(
            f.file_name,
            "Red_big_composition_medium_composition_more_oracles.ec"
        );
        assert_eq!(
            f.package_pairs,
            vec![("fwd2".to_string(), "fwd".to_string())]
        );
        let text = render_file(&f.file);
        assert!(text.contains("clone Pkg_Fwd as Cloned_Pkg_Fwd2."), "{text}");
        assert!(
            text.contains(
                "module Pkg_Inst_Fwd2 (O : Interfaces.Iface_SmallComposition) = \
                 Cloned_Pkg_Fwd2.Fwd(Pkg_Imports_Fwd2(O))."
            ),
            "{text}"
        );
        let stem = "big_composition_medium_composition_more_oracles";
        let router = module(f, &format!("Red_{stem}"));
        assert_eq!(
            router.implements.as_deref(),
            Some("Interfaces.Iface_MediumCompositionMoreOracles")
        );
        let adapter = module(f, "Pkg_Imports_Fwd2");
        let EcStmt::Call {
            module: m, proc: p, ..
        } = &adapter.procs[0].body.0[0]
        else {
            panic!()
        };
        assert_eq!((m.as_str(), p.as_str()), ("O", "d_UsefulOracle"));
        let l = module(f, &format!("RedExp_{stem}_L"));
        let r = module(f, &format!("RedExp_{stem}_R"));
        let callee = |m: &EcModule| match &proc(m, "run").body.0[1] {
            EcStmt::Call { module, .. } => module.clone(),
            _ => panic!(),
        };
        assert_eq!(
            callee(l),
            format!("Comp_MediumComposition.Exp_MediumComposition(B_{stem}(A))")
        );
        assert_eq!(
            callee(r),
            format!("Comp_SmallComposition.Exp_SmallComposition(B_{stem}(A))")
        );
    }

    #[test]
    fn kem_dem_exports_three_reductions_with_one_experiment_each() {
        let files = load(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        );
        assert_eq!(files.len(), 3);
        for f in &files {
            let stem = f
                .file_name
                .trim_start_matches("Red_")
                .trim_end_matches(".ec");
            let exps: Vec<&str> = f
                .file
                .items
                .iter()
                .filter_map(|i| match i {
                    EcItem::Module(m) if m.name.starts_with("RedExp_") => Some(m.name.as_str()),
                    _ => None,
                })
                .collect();
            assert_eq!(exps, vec![format!("RedExp_{stem}")]);
        }
        let first = &files[0];
        let stem = "Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM";
        let adapter = module(first, "Pkg_Imports_DEM");
        let get = proc(adapter, "d_GET");
        let EcStmt::Call {
            module: m, proc: p, ..
        } = &get.body.0[0]
        else {
            panic!()
        };
        assert_eq!((m.as_str(), p.as_str()), ("O", "d_GET"));
        let b = module(first, &format!("B_{stem}"));
        assert!(b.vars.is_empty());
        let EcStmt::Call { args, .. } = &proc(b, "run").body.0[0] else {
            panic!()
        };
        assert_eq!(args, &vec![EcExpr::Bool(false)]);
    }

    #[test]
    fn the_third_kem_dem_reduction_takes_the_assumption_arguments_of_its_own_sides() {
        let files = load(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        );
        let third = &files[2];
        assert_eq!(third.sides[0].assumption_game, "Game_CCA_KEM_Ideal");
        assert_eq!(third.sides[0].assumption_args, vec!["true".to_string()]);
        assert_eq!(third.sides[1].assumption_game, "Game_CCA_KEM_Real");
        assert_eq!(third.sides[1].assumption_args, vec!["false".to_string()]);
        assert_eq!(third.sides[0].experiment, third.sides[1].experiment);
    }

    #[test]
    fn reduction_consts_adversary_stores_the_theorem_constant() {
        let files = load("testdata/easycrypt/reduction-consts", "RedConsts");
        assert_eq!(files.len(), 1);
        let f = &files[0];
        let b = module(f, "B_mod_real_mod_ideal");
        assert_eq!(b.vars, vec![("b".to_string(), EcType::Bool)]);
        assert_eq!(
            proc(b, "setup").args,
            vec![("b0".to_string(), EcType::Bool)]
        );
        let exp = module(f, "RedExp_mod_real_mod_ideal");
        let run = proc(exp, "run");
        assert_eq!(
            run.args,
            vec![
                ("b".to_string(), EcType::Bool),
                ("ideal".to_string(), EcType::Bool)
            ]
        );
        let router = module(f, "Red_mod_real_mod_ideal");
        assert_eq!(
            proc(router, "init").args,
            vec![("flip".to_string(), EcType::Bool)]
        );
    }

    /// The text of lemma `name` from `lemma` to its `proof.`, with whitespace normalized.
    fn statement(text: &str, name: &str) -> String {
        let start = text
            .find(&format!("lemma {name} "))
            .unwrap_or_else(|| panic!("no lemma {name} in {text}"));
        let end = start + text[start..].find("\nproof.").unwrap();
        text[start..end].split_whitespace().collect::<Vec<_>>().join(" ")
    }

    fn lemma_names(f: &ReductionFile) -> Vec<String> {
        f.file
            .items
            .iter()
            .find_map(|i| match i {
                EcItem::Section(s) => Some(s.lemmas.iter().map(|l| l.name.clone()).collect()),
                _ => None,
            })
            .expect("a reduction file has a section")
    }

    fn op_names(f: &ReductionFile) -> Vec<String> {
        f.file
            .items
            .iter()
            .filter_map(|i| match i {
                EcItem::OpDef { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn hello_world_lemma_statements_are_the_prototypes() {
        let files = load("example-projects/hello-world", "Proof");
        let f = &files[0];
        let text = render_file(&f.file);
        assert!(!text.contains("admit"), "{text}");
        let stem = "big_composition_medium_composition_more_oracles";
        let proto = std::fs::read_to_string(format!(
            "testdata/easycrypt/reduction-prototype/hello-world/Red_{stem}.ec"
        ))
        .unwrap();
        let names = [
            format!("{stem}_equiv_L"),
            format!("{stem}_equiv_R"),
            format!("{stem}_bound"),
        ];
        for name in &names {
            assert_eq!(statement(&text, name), statement(&proto, name));
        }
        assert_eq!(f.lemmas.equivs, [names[0].clone(), names[1].clone()]);
        assert_eq!(f.lemmas.bound, names[2]);
        assert!(f.lemmas.consts.is_empty());
    }

    #[test]
    fn hello_world_has_an_invariant_for_each_side() {
        let files = load("example-projects/hello-world", "Proof");
        let stem = "big_composition_medium_composition_more_oracles";
        assert_eq!(
            op_names(&files[0]),
            vec![format!("inv_{stem}_L"), format!("inv_{stem}_R")]
        );
    }

    #[test]
    fn the_first_kem_dem_reduction_shares_its_oracle_lemmas() {
        let files = load(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        );
        let first = &files[0];
        let stem = "Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM";
        assert_eq!(op_names(first), vec![format!("inv_{stem}")]);
        assert_eq!(
            lemma_names(first),
            vec![
                format!("{stem}_d_PKGEN"),
                format!("{stem}_d_PKENC"),
                format!("{stem}_d_PKDEC"),
                format!("{stem}_equiv_L"),
                format!("{stem}_equiv_R"),
                format!("{stem}_bound"),
            ]
        );
    }

    #[test]
    fn reduction_consts_quantifies_the_constant_and_relates_the_stored_copy() {
        let files = load("testdata/easycrypt/reduction-consts", "RedConsts");
        let f = &files[0];
        let text = render_file(&f.file);
        let stem = "mod_real_mod_ideal";
        for name in [
            format!("{stem}_equiv_L"),
            format!("{stem}_equiv_R"),
            format!("{stem}_bound"),
        ] {
            assert!(
                statement(&text, &name).starts_with(&format!("lemma {name} &m (b : bool) :")),
                "{text}"
            );
        }
        assert!(
            text.contains(&format!(
                "Comp_ModGame.Cloned_Pkg_Mod.Mod.flip{{1}} B_{stem}.b{{2}}"
            )),
            "{text}"
        );
        assert_eq!(f.lemmas.consts, vec!["b".to_string()]);
    }

    #[test]
    fn the_third_kem_dem_bound_lemma_follows_the_hop_direction() {
        let files = load(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        );
        let third = &files[2];
        let text = render_file(&third.file);
        let stmt = statement(&text, &third.lemmas.bound);
        let rhs = stmt.split(" = ").nth(1).unwrap();
        let exp = &third.sides[0].experiment;
        assert!(
            rhs.starts_with(&format!("`|Pr[{exp}(A).run(true) @ &m : res] - Pr[{exp}(A).run(false)")),
            "{stmt}"
        );
    }

    /// Story 98's open review note: a reduction inside a hybrid hop gets no `Red_*.ec`
    /// (ADR 0022, decision 7).
    #[test]
    fn a_reduction_inside_a_hybrid_hop_is_not_translated() {
        assert!(load("example-projects/hello-world-hybrid", "Hybrid").is_empty());
    }
}
