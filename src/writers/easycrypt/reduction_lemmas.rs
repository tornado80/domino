// SPDX-License-Identifier: MIT OR Apache-2.0

//! The lemmas of `Red_<L>_<R>.ec` (story 99, ADR 0022 decisions 4–6): the invariant of each
//! reduction equivalence, one oracle lemma for each exported oracle, the two reduction
//! equivalences and the bound lemma, each with the proof script of story 97
//! (`docs/research/reduction-proof-script.md`).
//!
//! The oracle-lemma proof is the same text for every oracle of every reduction. Only the
//! exclusion list of its `inline` (the mapped instances, each by both of its names) and `MEQ`
//! (the equal states of the mapped packages) change, and both come from the map. The two sides
//! share the invariant and the oracle lemmas when everything the lemmas name is the same on
//! both sides (ADR 0022, decision 5).

use std::collections::HashMap;

use crate::gamehops::reduction::Reduction;
use crate::package::Composition;
use crate::parser::ast::Identifier as _;
use crate::parser::reduction::ReductionMapping;
use crate::theorem::{GameInstance, Theorem};

use super::ast::{
    DeclareModule, EcBinop, EcExpr, EcItem, EcLemma, EcSection, EcType, LemmaBinder, ProofLine,
};
use super::game::{instance_wirings, param_assignment, references_game_const, InstanceWiring};
use super::interfaces::InterfacesOutput;
use super::names::{NameKind, Names};
use super::package::{module_vars, param_needs_var};
use super::proof::{literal_text_to_expr, resolve_run_arg, side_run_args, RunArgValue};
use super::reduction::StoredConst;
use super::render::render_expr;
use super::types::translate_type;
use super::EcExportError;

/// The names of the lemmas a reduction exports, for the report (story 100 uses them).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReductionLemmas {
    /// `<hop>_equiv_L`, `<hop>_equiv_R`.
    pub equivs: [String; 2],
    /// `<hop>_bound`.
    pub bound: String,
    /// The theorem constants that the three lemmas take after `&m`, in theorem order.
    pub consts: Vec<String>,
}

/// Number of `alias`/`seq` rungs in the oracle-lemma walk: one is needed for each mapped call
/// or sampling on one path of an oracle (story 97 §4.3). A rung that is not needed costs one
/// type error.
const LADDER_RUNGS: usize = 8;

/// What the lemmas of the reduction need from `build_reduction_file`.
pub(super) struct LemmaInput<'a> {
    pub stem: &'a str,
    pub router: &'a str,
    pub b: &'a str,
    pub adv: &'a str,
    /// The left game's composition, whose instances the router clones.
    pub router_comp: &'a Composition,
    pub router_wiring: &'a [InstanceWiring],
    /// Indices into `router_comp.pkgs` of the reduction packages, the router's order.
    pub reduction_order: &'a [usize],
    pub stored: &'a [StoredConst],
    /// The reduction experiment of each side.
    pub experiments: [&'a str; 2],
}

/// The modules of one composition as the lemmas name them.
struct CompNames {
    theory: String,
    mangled: String,
    wiring: Vec<InstanceWiring>,
}

impl CompNames {
    fn new(
        theorem: &Theorem<'_>,
        interfaces: &InterfacesOutput,
        comp: &Composition,
    ) -> Result<Self, EcExportError> {
        let mangled = interfaces.comp_mangled[&comp.name].clone();
        Ok(Self {
            theory: format!("Comp_{mangled}"),
            mangled,
            wiring: instance_wirings(theorem, comp)?,
        })
    }

    fn game(&self) -> String {
        format!("{}.Game_{}", self.theory, self.mangled)
    }

    /// `Comp_<C>.Cloned_Pkg_<m>.<V>`: the unapplied clone, whose `glob` is the package's own
    /// state (story 97 §4.1).
    fn clone_module(&self, idx: usize) -> String {
        let w = &self.wiring[idx];
        format!("{}.Cloned_Pkg_{}.{}", self.theory, w.mangled, w.variant)
    }

    fn inst_module(&self, idx: usize) -> String {
        format!("{}.Pkg_Inst_{}", self.theory, self.wiring[idx].mangled)
    }

    fn restrictions(&self) -> Vec<String> {
        let mut out = vec![self.game()];
        out.extend((0..self.wiring.len()).map(|i| self.clone_module(i)));
        out
    }
}

/// The invariant, the exclusion list and `MEQ` of one side: everything an oracle lemma names.
#[derive(PartialEq)]
struct SideSpec {
    game: String,
    assm_game: String,
    /// The value arguments of the invariant op: `(name, type, applied value)`.
    args: Vec<(String, EcType, EcExpr)>,
    /// The equality conjuncts after C1 and C2: `(left arg, right arg)` names.
    eqs: Vec<(String, String)>,
    exclusions: Vec<String>,
    meq: Vec<EcExpr>,
}

fn qualified(path: &str, field: &str, mem: u8) -> EcExpr {
    let mut p: Vec<String> = path.split('.').map(String::from).collect();
    p.push(field.to_string());
    EcExpr::Qualified {
        path: p,
        mem: Some(mem),
    }
}

fn glob_at(module: String, mem: u8) -> EcExpr {
    EcExpr::GlobAt { module, mem }
}

/// `c0 /\ (c1 /\ ..)`: `/\` is right-associative, so it renders without parentheses.
fn and_all(conjuncts: Vec<EcExpr>) -> EcExpr {
    conjuncts
        .into_iter()
        .rev()
        .reduce(|acc, c| EcExpr::Binop {
            op: EcBinop::And,
            lhs: Box::new(c),
            rhs: Box::new(acc),
        })
        .expect("a conjunction of at least one conjunct")
}

fn eq(lhs: EcExpr, rhs: EcExpr) -> EcExpr {
    EcExpr::Binop {
        op: EcBinop::Eq,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

fn index_of(comp: &Composition, name: &str) -> usize {
    comp.pkgs
        .iter()
        .position(|p| p.name == name)
        .expect("the parser resolved every package instance a reduction names")
}

fn instance<'t>(theorem: &'t Theorem<'_>, name: &str) -> &'t GameInstance {
    theorem
        .find_game_instance(name)
        .expect("the parser resolved every game instance a reduction names")
}

/// The module variable of package instance `idx` of `game`'s composition that stores theorem
/// constant `t`: the first parameter with a variable whose composition constant `game` binds
/// to `t`.
fn param_var_storing(
    game: &GameInstance,
    idx: usize,
    t: &str,
) -> Result<Option<String>, EcExportError> {
    let comp = game.game();
    let inst = &comp.pkgs[idx];
    let vars = module_vars(&inst.pkg)?;
    let param_vars = &vars[inst.pkg.state.len()..];
    let needing = inst
        .pkg
        .params
        .iter()
        .filter(|(p, ty, _)| param_needs_var(&inst.pkg, p, ty));
    for ((p, _, _), (var, _)) in needing.zip(param_vars) {
        let assigned = param_assignment(inst, p);
        let stores = game.consts.iter().any(|(id, value)| {
            references_game_const(assigned, &id.name)
                && matches!(resolve_run_arg(value), Some(RunArgValue::TheoremConst(c)) if c == t)
        });
        if stores {
            return Ok(Some(var.clone()));
        }
    }
    Ok(None)
}

struct SideCtx<'a> {
    game: &'a GameInstance,
    names: CompNames,
    assm: CompNames,
    /// `(index in the game, index in the router's composition)` of each reduction package.
    reduction: Vec<(usize, usize)>,
    /// `(index in the game, index in the assumption game)` of each mapped package.
    mapped: Vec<(usize, usize)>,
}

fn side_ctx<'a>(
    theorem: &'a Theorem<'_>,
    interfaces: &InterfacesOutput,
    input: &LemmaInput<'_>,
    red: &Reduction<'_>,
    side: usize,
) -> Result<SideCtx<'a>, EcExportError> {
    let mapping: &ReductionMapping<'_> = if side == 0 { red.left() } else { red.right() };
    let game = instance(theorem, mapping.construction_game_instance_name().as_str());
    let assm = instance(theorem, mapping.assumption_game_instance_name().as_str());
    let reduction = if side == 0 {
        input.reduction_order.iter().map(|&i| (i, i)).collect()
    } else {
        // In the router's order, so that the two sides can share their lemmas.
        input
            .reduction_order
            .iter()
            .map(|&i| {
                let left = &input.router_comp.pkgs[i].name;
                let (_, right) = red
                    .package_pairs()
                    .iter()
                    .find(|(l, _)| l == left)
                    .expect("the parser pairs every reduction package of the left game");
                (index_of(game.game(), right), i)
            })
            .collect()
    };
    let mapped = mapping
        .entries()
        .iter()
        .map(|e| {
            (
                index_of(game.game(), e.construction().as_str()),
                index_of(assm.game(), e.assumption().as_str()),
            )
        })
        .collect();
    Ok(SideCtx {
        game,
        names: CompNames::new(theorem, interfaces, game.game())?,
        assm: CompNames::new(theorem, interfaces, assm.game())?,
        reduction,
        mapped,
    })
}

fn side_spec(input: &LemmaInput<'_>, ctx: &SideCtx<'_>) -> Result<SideSpec, EcExportError> {
    let game = ctx.names.game();
    let assm_game = ctx.assm.game();
    let mut args = vec![
        (
            "game_abort".to_string(),
            EcType::Bool,
            qualified(&game, "abort_flag", 1),
        ),
        (
            "red_abort".to_string(),
            EcType::Bool,
            qualified(input.router, "abort_flag", 2),
        ),
        (
            "assm_abort".to_string(),
            EcType::Bool,
            qualified(&assm_game, "abort_flag", 2),
        ),
    ];
    let mut eqs = Vec::new();
    let mut push_pair = |args: &mut Vec<_>, ty: EcType, ty_r: EcType, l: EcExpr, r: EcExpr| {
        let n = eqs.len();
        let (ln, rn) = (format!("x{n}_l"), format!("x{n}_r"));
        args.push((ln.clone(), ty, l));
        args.push((rn.clone(), ty_r, r));
        eqs.push((ln, rn));
    };
    // C3: each constant `B_<hop>` stores equals the package parameter that stores it.
    for s in input.stored {
        let found = ctx
            .reduction
            .iter()
            .map(|&(g, _)| param_var_storing(ctx.game, g, &s.theorem_const).map(|v| (g, v)))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .find_map(|(g, v)| v.map(|v| (g, v)));
        if let Some((g, var)) = found {
            push_pair(
                &mut args,
                s.ty.clone(),
                s.ty.clone(),
                qualified(&ctx.names.clone_module(g), &var, 1),
                qualified(input.b, &s.var, 2),
            );
        }
    }
    // C4: each reduction package with its router clone, each mapped package with its partner.
    for &(g, r) in &ctx.reduction {
        let w = &input.router_wiring[r];
        let router_clone = format!("Cloned_Pkg_{}.{}", w.mangled, w.variant);
        let left = ctx.names.clone_module(g);
        push_pair(
            &mut args,
            EcType::Glob(left.clone()),
            EcType::Glob(router_clone.clone()),
            glob_at(left, 1),
            glob_at(router_clone, 2),
        );
    }
    let mut exclusions = Vec::new();
    let mut meq = Vec::new();
    for &(g, a) in &ctx.mapped {
        let (left, right) = (ctx.names.clone_module(g), ctx.assm.clone_module(a));
        push_pair(
            &mut args,
            EcType::Glob(left.clone()),
            EcType::Glob(right.clone()),
            glob_at(left.clone(), 1),
            glob_at(right.clone(), 2),
        );
        meq.push(eq(glob_at(left.clone(), 1), glob_at(right.clone(), 2)));
        exclusions.push(ctx.names.inst_module(g));
        exclusions.push(left);
    }
    for &(_, a) in &ctx.mapped {
        exclusions.push(ctx.assm.inst_module(a));
        exclusions.push(ctx.assm.clone_module(a));
    }
    Ok(SideSpec {
        game,
        assm_game,
        args,
        eqs,
        exclusions,
        meq,
    })
}

fn inv_op(name: &str, spec: &SideSpec) -> EcItem {
    let var = |n: &str| EcExpr::Var(n.to_string());
    let mut conjuncts = vec![
        eq(var("game_abort"), var("red_abort")),
        EcExpr::Binop {
            op: EcBinop::Implies,
            lhs: Box::new(var("assm_abort")),
            rhs: Box::new(var("red_abort")),
        },
    ];
    conjuncts.extend(spec.eqs.iter().map(|(l, r)| eq(var(l), var(r))));
    EcItem::OpDef {
        name: name.to_string(),
        args: spec
            .args
            .iter()
            .map(|(n, ty, _)| (n.clone(), ty.clone()))
            .collect(),
        ret: Some(EcType::Bool),
        body: and_all(conjuncts),
    }
}

fn inv_applied(name: &str, spec: &SideSpec) -> EcExpr {
    EcExpr::App {
        head: name.to_string(),
        args: spec.args.iter().map(|(_, _, v)| v.clone()).collect(),
    }
}

fn tactic(text: impl Into<String>) -> ProofLine {
    ProofLine::Tactic {
        indent: 0,
        bullet: None,
        text: text.into(),
    }
}

fn bullet(text: impl Into<String>) -> ProofLine {
    ProofLine::Tactic {
        indent: 0,
        bullet: Some('+'),
        text: text.into(),
    }
}

/// The names `alias` gives, newest first: `ec_fwd<n-2>`, …, `ec_fwd0`, `ec_fwd`.
fn alias_names() -> Vec<String> {
    (0..LADDER_RUNGS)
        .rev()
        .map(|k| match k {
            0 => "ec_fwd".to_string(),
            k => format!("ec_fwd{}", k - 1),
        })
        .collect()
}

/// One rung for each alias name: split off the first instruction of both programs (a call or
/// a sampling) and close it with `closer`.
fn ladder(closer: &str, sep: &str) -> String {
    alias_names()
        .iter()
        .map(|name| {
            format!(
                "{sep}|| (alias{{1}} 1 with ec_fwd; alias{{2}} 1 with ec_fwd;{sep}    \
                 seq 1 1 : (#pre /\\ ={{{name}}});{sep}    first by {closer})"
            )
        })
        .collect()
}

/// The oracle-lemma proof of story 97 §4.3, with two additions found on the kem-dem
/// reductions that story 97 did not prove by hand:
///
/// - `try (elim* => *)` after `sp`: once reduction code wrote a state that the invariant reads,
///   `sp` keeps the old value under an `exists`, and `smt` cannot carry an `exists` over a
///   mapped call. `elim*` makes it a logical variable.
/// - When `sim` cannot prove a mapped call (a mapped package that reads a local it did not
///   write on every path, such as `DEM.d_ENC`'s `c_`), the call's body is walked forward, as
///   the oracle is: the two bodies are the same code, so only `if`s and samplings remain.
fn oracle_proof(spec: &SideSpec) -> Vec<ProofLine> {
    let mut inline = "proc; inline *".to_string();
    for e in &spec.exclusions {
        inline.push_str(&format!("\n  -{e}"));
    }
    inline.push('.');
    let closer = if spec.meq.is_empty() {
        "auto => /#".to_string()
    } else {
        let meq = render_expr(&and_all(spec.meq.clone()));
        let body = format!(
            "inline *; do ? (sp; try (elim* => *); ((if; first by move=> /#){})); auto => /#",
            ladder("auto => /#", " ")
        );
        format!(
            "(call (: {meq}); [by sim | by auto => /#])\n        \
             || (call (: {meq}); [by {body} | by auto => /#])\n        \
             || (auto => /#)"
        )
    };
    let walk = format!(
        "do ? (sp; try (elim* => *); (\n     (if; first by move=> /#)\n  \
         || (rcondt{{2}} 1; first by auto => /#)\n  \
         || (rcondf{{2}} 1; first by auto => /#){}\n  \
         || if{{2}})); auto => /#.",
        ladder(&closer, "\n  ")
    );
    vec![tactic(inline), tactic(walk)]
}

/// The `run` arguments of a side, as expressions over the lemma binders.
fn run_args(values: &[RunArgValue], binders: &HashMap<String, String>) -> Vec<EcExpr> {
    values
        .iter()
        .map(|v| match v {
            RunArgValue::Literal(text) => literal_text_to_expr(text),
            RunArgValue::TheoremConst(t) => EcExpr::Var(binders[t].clone()),
        })
        .collect()
}

fn arg_conjunct(args: &[EcExpr], mem: u8) -> Option<String> {
    let value = match args.len() {
        0 => return None,
        1 => render_expr(&args[0]),
        _ => render_expr(&EcExpr::Tuple(args.to_vec())),
    };
    Some(format!("arg{{{mem}}} = {value}"))
}

fn pr(module: String, args: Vec<EcExpr>) -> EcExpr {
    EcExpr::Pr {
        module,
        proc: "run".to_string(),
        args,
        memory: "m".to_string(),
        event: Box::new(EcExpr::Var("res".to_string())),
    }
}

/// Adds the lemmas of the reduction to `items`, after the modules.
pub(super) fn reduction_lemmas(
    theorem: &Theorem<'_>,
    interfaces: &InterfacesOutput,
    red: &Reduction<'_>,
    input: &LemmaInput<'_>,
    items: &mut Vec<EcItem>,
) -> Result<ReductionLemmas, EcExportError> {
    let ctxs = [
        side_ctx(theorem, interfaces, input, red, 0)?,
        side_ctx(theorem, interfaces, input, red, 1)?,
    ];
    let specs = [side_spec(input, &ctxs[0])?, side_spec(input, &ctxs[1])?];
    let shared = specs[0] == specs[1];
    let suffix = |i: usize| match (shared, i) {
        (true, _) => "",
        (false, 0) => "_L",
        (false, _) => "_R",
    };
    let stem = input.stem;
    let span = super::interfaces::composition_span(input.router_comp);

    // The lemma binders: every theorem constant a `run` argument reads, theorem order.
    let game_args = ctxs.each_ref().map(|c| side_run_args(c.game.game(), c.game));
    let assm_args = [red.left(), red.right()].map(|m| {
        let a = instance(theorem, m.assumption_game_instance_name().as_str());
        side_run_args(a.game(), a)
    });
    let mut read: Vec<&str> = input
        .stored
        .iter()
        .map(|s| s.theorem_const.as_str())
        .collect();
    for v in game_args.iter().chain(assm_args.iter()).flatten() {
        if let RunArgValue::TheoremConst(t) = v {
            read.push(t);
        }
    }
    let mut binders = vec![LemmaBinder::Memory("m".to_string())];
    let mut binder_names = HashMap::new();
    let mut consts = Vec::new();
    let mut names = Names::new();
    for (t, ty) in &theorem.consts {
        if !read.contains(&t.as_str()) {
            continue;
        }
        let name = names.mangle(NameKind::Var, t)?;
        binders.push(LemmaBinder::Typed {
            name: name.clone(),
            ty: translate_type(ty, span)?,
        });
        binder_names.insert(t.clone(), name);
        consts.push(t.clone());
    }
    let binder_args: String = consts
        .iter()
        .map(|t| format!(" {}", binder_names[t]))
        .collect();

    // The invariant ops, before the section.
    let mut inv_names = Vec::new();
    for (i, spec) in specs.iter().enumerate() {
        let name = format!("inv_{stem}{}", suffix(i));
        if !inv_names.contains(&name) {
            items.push(inv_op(&name, spec));
        }
        inv_names.push(name);
    }

    let mut restrictions = Vec::new();
    for names in ctxs.iter().flat_map(|c| [&c.names, &c.assm]) {
        for r in names.restrictions() {
            if !restrictions.contains(&r) {
                restrictions.push(r);
            }
        }
    }
    restrictions.push(input.router.to_string());
    restrictions.push(input.b.to_string());
    for &idx in input.reduction_order {
        let w = &input.router_wiring[idx];
        restrictions.push(format!("Cloned_Pkg_{}.{}", w.mangled, w.variant));
    }

    let mut procs = Vec::new();
    for export in &input.router_comp.exports {
        procs.push(Names::new().mangle(NameKind::Proc, export.name())?);
    }

    let mut lemmas = Vec::new();
    let mut oracle_names: [Vec<String>; 2] = [vec![], vec![]];
    for (i, spec) in specs.iter().enumerate() {
        for p in &procs {
            let name = format!("{stem}{}_{p}", suffix(i));
            oracle_names[i].push(name.clone());
            if shared && i == 1 {
                continue;
            }
            lemmas.push(EcLemma {
                name,
                binders: vec![],
                statement: EcExpr::OracleEquiv {
                    left: format!("{}.{p}", spec.game),
                    right: format!("{}({}).{p}", input.router, spec.assm_game),
                    inv: Box::new(inv_applied(&inv_names[i], spec)),
                    assumed: vec![],
                },
                proof: oracle_proof(spec),
            });
        }
    }

    let mut equivs = Vec::new();
    let mut prs = Vec::new();
    for (i, spec) in specs.iter().enumerate() {
        let game_run = run_args(&game_args[i], &binder_names);
        let mut red_run: Vec<EcExpr> = input
            .stored
            .iter()
            .map(|s| EcExpr::Var(binder_names[&s.theorem_const].clone()))
            .collect();
        red_run.extend(run_args(&assm_args[i], &binder_names));
        let left_pr = pr(
            format!("{}.Exp_{}(A)", ctxs[i].names.theory, ctxs[i].names.mangled),
            game_run.clone(),
        );
        let right_pr = pr(format!("{}(A)", input.experiments[i]), red_run.clone());
        let mut pre = vec!["={glob A}".to_string()];
        pre.extend(arg_conjunct(&game_run, 1));
        pre.extend(arg_conjunct(&red_run, 2));
        let mut proof = vec![
            tactic(format!(
                "byequiv (: {} ==> ={{res}}) => //.",
                pre.join(" /\\ ")
            )),
            tactic("proc; inline *; wp."),
            tactic(format!(
                "call (: {}).",
                render_expr(&inv_applied(&inv_names[i], spec))
            )),
        ];
        for o in &oracle_names[i] {
            proof.push(bullet(format!("by conseq {o} => /#.")));
        }
        proof.push(tactic("by auto => /#."));
        let name = format!("{stem}_equiv{}", ["_L", "_R"][i]);
        lemmas.push(EcLemma {
            name: name.clone(),
            binders: binders.clone(),
            statement: eq(left_pr.clone(), right_pr.clone()),
            proof,
        });
        equivs.push(name);
        prs.push((left_pr, right_pr));
    }
    let sub = |a: &EcExpr, b: &EcExpr| {
        EcExpr::Abs(Box::new(EcExpr::Binop {
            op: EcBinop::Sub,
            lhs: Box::new(a.clone()),
            rhs: Box::new(b.clone()),
        }))
    };
    let bound = format!("{stem}_bound");
    lemmas.push(EcLemma {
        name: bound.clone(),
        binders,
        statement: eq(sub(&prs[0].0, &prs[1].0), sub(&prs[0].1, &prs[1].1)),
        proof: vec![tactic(format!(
            "by rewrite ({} &m{binder_args}) ({} &m{binder_args}).",
            equivs[0], equivs[1]
        ))],
    });

    items.push(EcItem::Section(EcSection {
        declares: vec![DeclareModule {
            name: "A".to_string(),
            module_type: format!("Interfaces.{}", input.adv),
            restrictions,
        }],
        assumptions: vec![],
        items: vec![],
        lemmas,
    }));
    Ok(ReductionLemmas {
        equivs: [equivs[0].clone(), equivs[1].clone()],
        bound,
        consts,
    })
}
