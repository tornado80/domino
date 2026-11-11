// SPDX-License-Identifier: MIT OR Apache-2.0

//! Building the files of each reduction hop (story 98, story 102, ADR 0023 decisions 2 and 6):
//! `Red_<L>_<R>_Router.ec` with the **reduction router** `Red_<hop>(O)` and the invariant,
//! `Red_<L>_<R>_<O>.ec` with the oracle lemmas, and `Red_<L>_<R>.ec` with the **run lemma**
//! (`reduction_lemmas`). The reduction adversaries are in the proposition files (story 102).
//!
//! The router is built from the **left** game instance's reduction packages, with their
//! instance names (story 97). A call that reaches a mapped package goes to `O`, under the name
//! of the assumption game's export that reaches the same oracle of the paired assumption
//! package.

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
use super::proof::{side_run_args, RunArgValue};
use super::reduction_lemmas::{reduction_lemmas, LemmaInput};
pub use super::reduction_lemmas::ReductionOracleFile;
use super::types::{translate_expr, translate_type};
use super::EcExportError;

/// One reduction hop's files: `Red_<L>_<R>_Router.ec`, one `Red_<L>_<R>_<O>.ec` for each
/// oracle, and `Red_<L>_<R>.ec`, which joins them in the run lemma (ADR 0023 decision 6).
pub struct ReductionFile {
    /// Index of the hop in `theorem.game_hops`.
    pub proofstep: usize,
    pub left_name: String,
    pub right_name: String,
    pub assumption_name: String,
    /// The joining file, `Red_<L>_<R>.ec`, with the run lemma(s).
    pub file_name: String,
    pub file: EcFile,
    /// `Red_<L>_<R>_Router.ec`: the clones, the router and the invariant(s).
    pub router_file_name: String,
    pub router_file: EcFile,
    /// One file for each exported oracle, in the export order.
    pub oracle_files: Vec<ReductionOracleFile>,
    /// The reduction packages, `(left instance, right instance)`, as the parser pairs them.
    pub package_pairs: Vec<(String, String)>,
    /// The hop's left side, then its right side.
    pub sides: [ReductionSide; 2],
    /// The run lemma of each side: the same name twice when the sides share it.
    pub run_lemmas: [String; 2],
    /// What a proposition needs to write a reduction adversary (story 102).
    pub router: RouterUse,
}

/// The router as a reduction adversary uses it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RouterUse {
    /// `Red_<L>_<R>`, a module of `Red_<L>_<R>_Router.ec`.
    pub module: String,
    /// `Interfaces.Adv_<G>`.
    pub adv: String,
    /// `Interfaces.Iface_<Assm>`.
    pub assm_iface: String,
    /// The value of each argument of the router's `init`, as the left game instance binds it.
    pub init_values: Vec<RunArgValue>,
}

/// One side of a reduction hop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReductionSide {
    /// The assumption game instance that the map of this side names.
    pub assumption_game: String,
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

/// The value of each argument of the router's `init`, as the left game instance binds it: a
/// literal, or a theorem constant that a proposition step fixes (story 102).
fn router_init_values(ctx: &RouterCtx<'_>, left: &GameInstance) -> Vec<RunArgValue> {
    router_init_consts(ctx)
        .iter()
        .map(|(c, _)| {
            let assigned = left
                .consts
                .iter()
                .find(|(id, _)| &id.name == c)
                .map(|(_, e)| e)
                .expect("a game instance binds every one of its composition's consts");
            super::proof::resolve_run_arg(assigned).expect(
                "a game instance's composition-const binding is a literal or a theorem constant",
            )
        })
        .collect()
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

fn std_requires(plain: Vec<String>) -> Vec<Require> {
    vec![
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
    ]
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
    let mut router_items = reduction_package_items(&ctx)?;
    router_items.push(EcItem::Module(router_module(
        &ctx,
        &router_name,
        iface,
        span,
    )?));

    let assm_insts = [red.left(), red.right()]
        .map(|m| instance(theorem, m.assumption_game_instance_name().as_str()));
    let sides = [0, 1].map(|i| ReductionSide {
        assumption_game: assm_insts[i].name().to_string(),
        assumption_args: side_run_args(assm_insts[i].game(), assm_insts[i])
            .iter()
            .map(render_run_arg)
            .collect(),
    });

    let mut comps = vec!["Interfaces".to_string()];
    for comp in [
        left.game(),
        right.game(),
        assm_insts[0].game(),
        assm_insts[1].game(),
    ] {
        push_unique(
            &mut comps,
            format!("Comp_{}", interfaces.comp_mangled[&comp.name]),
        );
    }
    let lemma_requires = std_requires(comps.clone());

    let reduction_order = ctx.reduction_order();
    let lemmas = reduction_lemmas(
        theorem,
        interfaces,
        red,
        &LemmaInput {
            stem: &stem,
            router: &router_name,
            adv,
            router_comp: ctx.comp,
            router_wiring: &ctx.wiring,
            reduction_order: &reduction_order,
            theorem: &theorem.name,
            requires: &lemma_requires,
        },
        &mut router_items,
    )?;

    let mut plain = vec!["Interfaces".to_string()];
    for idx in ctx.reduction_order() {
        push_unique(&mut plain, format!("Pkg_{}", ctx.wiring[idx].variant));
    }
    for c in &comps[1..] {
        push_unique(&mut plain, c.clone());
    }

    let what = format!(
        "the reduction `{} ~ {}` to assumption `{}`",
        left.name(),
        right.name(),
        red.assumption_name()
    );
    let mut router_header = vec![format!(
        "Red_{stem}_Router.ec for theorem `{}`, {what}: the router and the invariant — \
         generated by `domino easycrypt`.",
        theorem.name,
    )];
    for (side, label) in sides.iter().zip(["Left", "Right"]) {
        router_header.push(format!(
            "{label} side: assumption game `{}`, with the assumption arguments ({}).",
            side.assumption_game,
            side.assumption_args.join(", ")
        ));
    }
    let pairs: Vec<String> = red
        .package_pairs()
        .iter()
        .map(|(l, r)| format!("{l} ~ {r}"))
        .collect();
    router_header.push(format!(
        "Reduction packages (left ~ right): {}. The router uses the left names.",
        if pairs.is_empty() {
            "none".to_string()
        } else {
            pairs.join(", ")
        }
    ));

    let mut join_requires = lemma_requires;
    join_requires.push(Require {
        import: true,
        names: vec![format!("Red_{stem}_Router")],
    });
    join_requires.push(Require {
        import: true,
        names: lemmas
            .oracle_files
            .iter()
            .map(|o| o.file_name.trim_end_matches(".ec").to_string())
            .collect(),
    });

    Ok(ReductionFile {
        proofstep,
        left_name: left.name().to_string(),
        right_name: right.name().to_string(),
        assumption_name: red.assumption_name().to_string(),
        file_name: format!("Red_{stem}.ec"),
        file: EcFile {
            header: vec![format!(
                "Red_{stem}.ec for theorem `{}`, {what}: the run lemma — generated by \
                 `domino easycrypt`.",
                theorem.name,
            )],
            requires: join_requires,
            items: vec![EcItem::Section(lemmas.section)],
        },
        router_file_name: format!("Red_{stem}_Router.ec"),
        router_file: EcFile {
            header: router_header,
            requires: std_requires(plain),
            items: router_items,
        },
        oracle_files: lemmas.oracle_files,
        package_pairs: red.package_pairs().to_vec(),
        sides,
        run_lemmas: lemmas.run_lemmas,
        router: RouterUse {
            module: router_name,
            adv: format!("Interfaces.{adv}"),
            assm_iface: ctx.assm_iface.clone(),
            init_values: router_init_values(&ctx, left),
        },
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

    const LAYOUT: &str = "testdata/easycrypt/reduction-prototype/layout";
    const KEM_DEM: &str = "example-projects/kem-dem/kem-dem-cca-ssp";

    fn module<'f>(f: &'f EcFile, name: &str) -> &'f EcModule {
        f.items
            .iter()
            .find_map(|i| match i {
                EcItem::Module(m) if m.name == name => Some(m),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no module {name} in {}", render_file(f)))
    }

    fn proc<'m>(m: &'m EcModule, name: &str) -> &'m EcProc {
        m.procs.iter().find(|p| p.name == name).unwrap()
    }

    /// Every file of a reduction, rendered: `(file name, text)`.
    fn texts(f: &ReductionFile) -> Vec<(String, String)> {
        let mut out = vec![
            (f.router_file_name.clone(), render_file(&f.router_file)),
            (f.file_name.clone(), render_file(&f.file)),
        ];
        out.extend(
            f.oracle_files
                .iter()
                .map(|o| (o.file_name.clone(), render_file(&o.file))),
        );
        out
    }

    /// The text from `<keyword> <name> ` to the next `proof.` or `.\n`, whitespace normalized.
    fn statement(text: &str, keyword: &str, name: &str) -> String {
        let start = text
            .find(&format!("{keyword} {name} "))
            .unwrap_or_else(|| panic!("no {keyword} {name} in {text}"));
        let rest = &text[start..];
        let end = rest
            .find("\nproof.")
            .or_else(|| rest.find(".\n\n"))
            .unwrap_or(rest.len());
        rest[..end].split_whitespace().collect::<Vec<_>>().join(" ")
    }

    fn prototype(case: &str, file: &str) -> String {
        std::fs::read_to_string(format!("{LAYOUT}/{case}/{file}")).unwrap()
    }

    fn op_names(f: &EcFile) -> Vec<String> {
        f.items
            .iter()
            .filter_map(|i| match i {
                EcItem::OpDef { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn kem_dem_writes_a_router_an_oracle_file_for_each_oracle_and_a_joining_file() {
        let files = load(KEM_DEM, "kem_dem_cca_ssp");
        assert_eq!(files.len(), 3);
        for f in &files {
            let stem = f.file_name.trim_end_matches(".ec");
            assert_eq!(f.router_file_name, format!("{stem}_Router.ec"));
            let oracles: Vec<&str> = f.oracle_files.iter().map(|o| o.file_name.as_str()).collect();
            assert_eq!(
                oracles,
                ["PKGEN", "PKENC", "PKDEC"].map(|o| format!("{stem}_{o}.ec"))
            );
            for (name, text) in texts(f) {
                assert!(!text.contains("RedExp"), "{name}: {text}");
                assert!(!text.contains("setup"), "{name}: {text}");
                assert!(!text.contains("admit"), "{name}: {text}");
            }
        }
    }

    #[test]
    fn the_first_kem_dem_reduction_matches_the_prototype() {
        let files = load(KEM_DEM, "kem_dem_cca_ssp");
        let f = &files[0];
        let stem = "Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM";
        assert_eq!(f.run_lemmas, [format!("run_{stem}"), format!("run_{stem}")]);
        let join = render_file(&f.file);
        let proto = prototype("kem-dem", &format!("Red_{stem}.ec"));
        let run = format!("run_{stem}");
        assert_eq!(statement(&join, "lemma", &run), statement(&proto, "lemma", &run));
        assert!(
            join.contains(&format!("+ by conseq Red_{stem}_PKDEC => /#.")),
            "{join}"
        );
        let router = render_file(&f.router_file);
        let proto = prototype("kem-dem", &format!("Red_{stem}_Router.ec"));
        let inv = format!("inv_{stem}");
        assert_eq!(statement(&router, "op", &inv), statement(&proto, "op", &inv));
        let oracle = render_file(&f.oracle_files[2].file);
        let proto = prototype("kem-dem", &format!("Red_{stem}_PKDEC.ec"));
        let lemma = format!("Red_{stem}_PKDEC");
        assert_eq!(
            statement(&oracle, "lemma", &lemma),
            statement(&proto, "lemma", &lemma)
        );
        let adapter = module(&f.router_file, "Pkg_Imports_DEM");
        let EcStmt::Call {
            module: m, proc: p, ..
        } = &proc(adapter, "d_GET").body.0[0]
        else {
            panic!()
        };
        assert_eq!((m.as_str(), p.as_str()), ("O", "d_GET"));
        assert_eq!(
            f.router.init_values,
            vec![RunArgValue::Literal("false".to_string())]
        );
    }

    #[test]
    fn the_third_kem_dem_reduction_takes_the_assumption_arguments_of_its_own_sides() {
        let files = load(KEM_DEM, "kem_dem_cca_ssp");
        let third = &files[2];
        assert_eq!(third.sides[0].assumption_game, "Game_CCA_KEM_Ideal");
        assert_eq!(third.sides[0].assumption_args, vec!["true".to_string()]);
        assert_eq!(third.sides[1].assumption_game, "Game_CCA_KEM_Real");
        assert_eq!(third.sides[1].assumption_args, vec!["false".to_string()]);
    }

    #[test]
    fn hello_world_has_a_run_lemma_and_an_invariant_for_each_side() {
        let files = load("example-projects/hello-world", "Proof");
        assert_eq!(files.len(), 1);
        let f = &files[0];
        let stem = "big_composition_medium_composition_more_oracles";
        assert_eq!(f.package_pairs, vec![("fwd2".to_string(), "fwd".to_string())]);
        assert_eq!(
            f.run_lemmas,
            [format!("run_{stem}_L"), format!("run_{stem}_R")]
        );
        assert_eq!(
            op_names(&f.router_file),
            vec![format!("inv_{stem}_L"), format!("inv_{stem}_R")]
        );
        let router = render_file(&f.router_file);
        assert!(router.contains("clone Pkg_Fwd as Cloned_Pkg_Fwd2."), "{router}");
        assert_eq!(
            module(&f.router_file, &format!("Red_{stem}"))
                .implements
                .as_deref(),
            Some("Interfaces.Iface_MediumCompositionMoreOracles")
        );
        let join = render_file(&f.file);
        let proto = prototype("hello-world", &format!("Red_{stem}.ec"));
        for run in &f.run_lemmas {
            assert_eq!(statement(&join, "lemma", run), statement(&proto, "lemma", run));
        }
        // each oracle file holds the lemmas of both sides
        let oracle = render_file(&f.oracle_files[0].file);
        assert_eq!(
            f.oracle_files[0].file_name,
            format!("Red_{stem}_UsefulOracle.ec")
        );
        assert!(oracle.contains(&format!("lemma Red_{stem}_UsefulOracle_L :")), "{oracle}");
        assert!(oracle.contains(&format!("lemma Red_{stem}_UsefulOracle_R :")), "{oracle}");
        for (name, text) in texts(f) {
            assert!(!text.contains("RedExp") && !text.contains("setup"), "{name}");
        }
    }

    #[test]
    fn reduction_consts_invariant_relates_no_stored_constant() {
        let files = load("testdata/easycrypt/reduction-consts", "RedConsts");
        assert_eq!(files.len(), 1);
        let f = &files[0];
        let router = render_file(&f.router_file);
        let proto = prototype("reduction-consts", "Red_mod_real_mod_ideal_Router.ec");
        let inv = "inv_mod_real_mod_ideal";
        assert_eq!(statement(&router, "op", inv), statement(&proto, "op", inv));
        assert!(!router.contains("flip{1}"), "{router}");
        assert!(!router.contains("B_"), "{router}");
        assert_eq!(
            proc(module(&f.router_file, "Red_mod_real_mod_ideal"), "init").args,
            vec![("flip".to_string(), EcType::Bool)]
        );
        assert_eq!(
            f.router.init_values,
            vec![RunArgValue::TheoremConst("b".to_string())]
        );
        let oracle = render_file(&f.oracle_files[0].file);
        let proto = prototype("reduction-consts", "Red_mod_real_mod_ideal_Query.ec");
        let lemma = "Red_mod_real_mod_ideal_Query";
        assert_eq!(
            statement(&oracle, "lemma", lemma),
            statement(&proto, "lemma", lemma)
        );
    }

    /// Story 98's open review note: a reduction inside a hybrid hop gets no `Red_*.ec`
    /// (ADR 0022, decision 7).
    #[test]
    fn a_reduction_inside_a_hybrid_hop_is_not_translated() {
        assert!(load("example-projects/hello-world-hybrid", "Hybrid").is_empty());
    }
}
