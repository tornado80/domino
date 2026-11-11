// SPDX-License-Identifier: MIT OR Apache-2.0

//! The lemmas of a reduction (story 99, story 102, ADR 0023 decisions 2 and 6): the invariant
//! of each side (in `Red_<L>_<R>_Router.ec`), one oracle lemma file `Red_<L>_<R>_<O>.ec` for each
//! exported oracle, and the **run lemma** of each side in `Red_<L>_<R>.ec`. The oracle proof is
//! still the ladder of story 97 (`docs/research/reduction-proof-script.md`); story 103 replaces it.
//!
//! The oracle-lemma proof is the same text for every oracle of every reduction. Only the
//! exclusion list of its `inline` (the mapped instances, each by both of its names) and `MEQ`
//! (the equal states of the mapped packages) change, and both come from the map. The two sides
//! share the invariant and the oracle lemmas when everything the lemmas name is the same on
//! both sides (ADR 0022, decision 5).

use crate::gamehops::reduction::Reduction;
use crate::package::Composition;
use crate::parser::ast::Identifier as _;
use crate::parser::reduction::ReductionMapping;
use crate::theorem::{GameInstance, Theorem};

use super::ast::{
    DeclareModule, EcBinop, EcExpr, EcFile, EcItem, EcLemma, EcSection, EcType, ProofLine, Require,
};
use super::game::{instance_wirings, InstanceWiring};
use super::interfaces::InterfacesOutput;
use super::names::{NameKind, Names};
use super::render::render_expr;
use super::EcExportError;

/// One oracle's lemma file of a reduction, `Red_<L>_<R>_<O>.ec`: the oracle lemma of each side
/// (one lemma when the sides share it).
pub struct ReductionOracleFile {
    /// The exported oracle's name, the `<O>` of the file name.
    pub oracle: String,
    pub file_name: String,
    pub file: EcFile,
}

/// What [`reduction_lemmas`] writes, apart from the invariant ops.
pub(super) struct ReductionLemmas {
    /// `run_<hop>` for both sides, or `run_<hop>_L` and `run_<hop>_R`.
    pub run_lemmas: [String; 2],
    pub oracle_files: Vec<ReductionOracleFile>,
    /// The section of `Red_<L>_<R>.ec`, with the run lemmas.
    pub section: EcSection,
}

/// Number of `alias`/`seq` rungs in the oracle-lemma walk: one is needed for each mapped call
/// or sampling on one path of an oracle (story 97 §4.3). A rung that is not needed costs one
/// type error.
const LADDER_RUNGS: usize = 8;

/// What the lemmas of the reduction need from `build_reduction_file`.
pub(super) struct LemmaInput<'a> {
    pub stem: &'a str,
    pub router: &'a str,
    pub adv: &'a str,
    /// The left game's composition, whose instances the router clones.
    pub router_comp: &'a Composition,
    pub router_wiring: &'a [InstanceWiring],
    /// Indices into `router_comp.pkgs` of the reduction packages, the router's order.
    pub reduction_order: &'a [usize],
    /// The theorem's name, for the file headers.
    pub theorem: &'a str,
    /// The `require` lines of an oracle file and of the joining file.
    pub requires: &'a [Require],
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

struct SideCtx {
    names: CompNames,
    assm: CompNames,
    /// `(index in the game, index in the router's composition)` of each reduction package.
    reduction: Vec<(usize, usize)>,
    /// `(index in the game, index in the assumption game)` of each mapped package.
    mapped: Vec<(usize, usize)>,
}

fn side_ctx(
    theorem: &Theorem<'_>,
    interfaces: &InterfacesOutput,
    input: &LemmaInput<'_>,
    red: &Reduction<'_>,
    side: usize,
) -> Result<SideCtx, EcExportError> {
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
        names: CompNames::new(theorem, interfaces, game.game())?,
        assm: CompNames::new(theorem, interfaces, assm.game())?,
        reduction,
        mapped,
    })
}

fn side_spec(input: &LemmaInput<'_>, ctx: &SideCtx) -> Result<SideSpec, EcExportError> {
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
    // C4: each reduction package with its router clone, each mapped package with its partner.
    for &(g, r) in &ctx.reduction {
        let w = &input.router_wiring[r];
        let router_clone = router_clone(w);
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

/// `Cloned_Pkg_<m>.<V>`: a router clone, unapplied.
fn router_clone(w: &InstanceWiring) -> String {
    format!("Cloned_Pkg_{}.{}", w.mangled, w.variant)
}

/// The modules `A` may not touch: every game and package of the four compositions, the router
/// and the router's clones.
fn adversary_restrictions(input: &LemmaInput<'_>, ctxs: &[SideCtx; 2]) -> Vec<String> {
    let mut restrictions = Vec::new();
    let extra = [input.router.to_string()];
    let clones = input
        .reduction_order
        .iter()
        .map(|&idx| router_clone(&input.router_wiring[idx]));
    let all = ctxs
        .iter()
        .flat_map(|c| [&c.names, &c.assm])
        .flat_map(|n| n.restrictions())
        .chain(extra)
        .chain(clones);
    for r in all {
        if !restrictions.contains(&r) {
            restrictions.push(r);
        }
    }
    restrictions
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

/// One `+ by conseq <lemma> => /#.` for each oracle; no bullet when there is one oracle.
fn conseq_lines(procs: &[String], lemmas: &[String]) -> Vec<ProofLine> {
    let mut out = Vec::new();
    for (p, l) in procs.iter().zip(lemmas) {
        out.push(tactic(format!("(* {p} *)")));
        let text = format!("by conseq {l} => /#.");
        out.push(if procs.len() == 1 {
            tactic(text)
        } else {
            bullet(text)
        });
    }
    out
}

/// Adds the invariant ops of the reduction to `router_items`, and returns its oracle lemma
/// files and the section of its joining file with the run lemmas.
pub(super) fn reduction_lemmas(
    theorem: &Theorem<'_>,
    interfaces: &InterfacesOutput,
    red: &Reduction<'_>,
    input: &LemmaInput<'_>,
    router_items: &mut Vec<EcItem>,
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
    let sides: &[usize] = if shared { &[0] } else { &[0, 1] };

    let inv_names = [0, 1].map(|i| format!("inv_{stem}{}", suffix(i)));
    for &i in sides {
        router_items.push(inv_op(&inv_names[i], &specs[i]));
    }

    let mut procs = Vec::new();
    let mut oracle_files = Vec::new();
    let mut oracle_lemmas: [Vec<String>; 2] = [vec![], vec![]];
    let mut lemma_names = Names::new();
    for export in &input.router_comp.exports {
        let p = Names::new().mangle(NameKind::Proc, export.name())?;
        let oracle_stem = format!("Red_{stem}_{}", export.name());
        let mut lemmas = Vec::new();
        for &i in sides {
            let name =
                lemma_names.mangle(NameKind::Lemma, &format!("{oracle_stem}{}", suffix(i)))?;
            lemmas.push(EcItem::Lemma(EcLemma {
                name: name.clone(),
                binders: vec![],
                statement: EcExpr::OracleEquiv {
                    left: format!("{}.{p}", specs[i].game),
                    right: format!("{}({}).{p}", input.router, specs[i].assm_game),
                    inv: Box::new(inv_applied(&inv_names[i], &specs[i])),
                    assumed: vec![],
                },
                proof: oracle_proof(&specs[i]),
            }));
            oracle_lemmas[i].push(name);
        }
        if shared {
            oracle_lemmas[1] = oracle_lemmas[0].clone();
        }
        let mut requires = input.requires.to_vec();
        requires.push(Require {
            import: true,
            names: vec![format!("Red_{stem}_Router")],
        });
        oracle_files.push(ReductionOracleFile {
            oracle: export.name().to_string(),
            file_name: format!("{oracle_stem}.ec"),
            file: EcFile {
                header: vec![format!(
                    "{oracle_stem}.ec for theorem `{}`: the oracle lemma of `{}` in the \
                     reduction `{}` — generated by `domino easycrypt`.",
                    input.theorem,
                    export.name(),
                    stem
                )],
                requires,
                items: lemmas,
            },
        });
        procs.push(p);
    }

    let mut lemmas = Vec::new();
    let mut run_lemmas = [0, 1].map(|i| format!("run_{stem}{}", suffix(i)));
    if shared {
        run_lemmas[1] = run_lemmas[0].clone();
    }
    for &i in sides {
        let inv = inv_applied(&inv_names[i], &specs[i]);
        let mut proof = vec![tactic(format!("proc ({}) => //.", render_expr(&inv)))];
        proof.extend(conseq_lines(&procs, &oracle_lemmas[i]));
        lemmas.push(EcLemma {
            name: run_lemmas[i].clone(),
            binders: vec![],
            statement: EcExpr::RunEquiv {
                left: format!("A({}).run", specs[i].game),
                right: format!("A({}({})).run", input.router, specs[i].assm_game),
                inv: Box::new(inv),
            },
            proof,
        });
    }
    Ok(ReductionLemmas {
        run_lemmas,
        oracle_files,
        section: EcSection {
            declares: vec![DeclareModule {
                name: "A".to_string(),
                module_type: format!("Interfaces.{}", input.adv),
                restrictions: adversary_restrictions(input, &ctxs),
            }],
            assumptions: vec![],
            items: vec![],
            lemmas,
        },
    })
}
