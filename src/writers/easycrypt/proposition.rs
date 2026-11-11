// SPDX-License-Identifier: MIT OR Apache-2.0

//! `Prop_<Name>.ec` for each proposition of a theorem (story 100, ADR 0022 decisions 6–8): the
//! **proposition lemma**, which bounds the advantage of the adversary between the two ends of
//! the proposition's path by one term for each reduction step and one for each open hop.
//!
//! - A **reduction step** gives the right side of its bound lemma, at the step's arguments, in
//!   the hop's direction (also when the path uses the hop in reverse).
//! - An **equivalence step** gives no term: the proof uses its lemma at the step's arguments.
//! - An **open hop** (a conjecture, or an equivalence without a translated file) gives the
//!   adversary's advantage between the two neighbouring game instances, in path order.
//! - A path with a **hybrid hop** gets no file: hybrids are out of scope (ADR 0022, decision 7).
//!
//! The proof is one `have` for each translated lemma, then `smt()`. The lemmas sit in the
//! sections of their own files; the proposition's section declares the adversary with the
//! union of their restrictions, so that each lemma applies to it.

use std::collections::HashMap;

use crate::gamehops::GameHop;
use crate::proof::{assignments, game_is_compatible, Proof};
use crate::theorem::{GameInstance, Theorem};

use super::ast::{
    DeclareModule, EcBinop, EcBlock, EcExpr, EcFile, EcItem, EcLemma, EcLvalue, EcModule, EcProc,
    EcSection, EcStmt, EcType, LemmaBinder, ProofLine, Require,
};
use super::game::composition_const_needs_arg;
use super::interfaces::{composition_span, InterfacesOutput};
use super::names::{NameKind, Names};
use super::proof::{literal_text_to_expr, side_run_args, EquivalenceFiles, RunArgValue};
use super::prop_reduction;
use super::reduction::{push_unique, ReductionFile};
use super::render::render_expr;
use super::types::translate_type;
use super::EcExportError;

/// The reason a proposition whose path has a hybrid hop gets no lemma.
pub const HYBRID_REASON: &str = "hybrid game hops are not translated";

/// A hop of a proposition's path that gives its own term: a conjecture, or an equivalence that
/// has no translated file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenHop {
    /// `"conjecture"`, `"equivalence"` or `"reduction"` (a reduction step that leaves a
    /// constant of the reduction packages free).
    pub kind: &'static str,
    /// The hop's game instances, as the hop names them.
    pub left: String,
    pub right: String,
}

/// One reduction step of a proposition's path (story 102): its adversary and its lemmas.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReductionStep {
    /// The hop's game instances, as the hop names them.
    pub left: String,
    pub right: String,
    /// `B_<L>_<R><s>`.
    pub adversary: String,
    /// The values that the step fixes for the theorem constants that the reduction packages
    /// read: `(constant, value)`, theorem order.
    pub values: Vec<(String, String)>,
    /// `equiv_<L>_<R><s>`, or the `_L` and `_R` lemmas.
    pub equiv_lemmas: Vec<String>,
    /// `bound_<L>_<R><s>`.
    pub bound_lemma: String,
}

/// One proposition's file, `Prop_<Name>.ec`.
pub struct PropositionFile {
    pub name: String,
    pub file_name: String,
    pub file: EcFile,
    /// The number of reduction terms on the right side of the lemma.
    pub reduction_terms: usize,
    /// The open hops, in path order.
    pub open_hops: Vec<OpenHop>,
    /// The reduction steps that are not open hops, in path order.
    pub reduction_steps: Vec<ReductionStep>,
}

/// A proposition that gets no file because its path has a hybrid hop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkippedProposition {
    pub name: String,
    /// The hybrid hop's game instances.
    pub left: String,
    pub right: String,
    pub reason: &'static str,
}

/// What [`compute_proposition_files`] gives for each proposition.
pub enum PropositionOutcome {
    File(PropositionFile),
    Skipped(SkippedProposition),
}

/// One outcome for each proposition of `theorem`, in `theorem.proofs` order. `equivalences` and
/// `reductions` are the files that the export writes for the theorem's hops.
pub fn compute_proposition_files(
    theorem: &Theorem<'_>,
    interfaces: &InterfacesOutput,
    equivalences: &[EquivalenceFiles],
    reductions: &[ReductionFile],
) -> Result<Vec<PropositionOutcome>, EcExportError> {
    let ctx = Ctx {
        theorem,
        interfaces,
        equivalences,
        reductions,
        binders: const_binders(theorem)?,
    };
    theorem
        .proofs
        .iter()
        .map(|proof| ctx.outcome(proof))
        .collect()
}

/// Each theorem constant's lemma binder, as the equivalence and reduction lemmas name it.
fn const_binders(theorem: &Theorem<'_>) -> Result<HashMap<String, String>, EcExportError> {
    let mut names = Names::new();
    theorem
        .consts
        .iter()
        .map(|(c, _)| Ok((c.clone(), names.mangle(NameKind::Var, c)?)))
        .collect()
}

struct Ctx<'a, 't> {
    theorem: &'a Theorem<'t>,
    interfaces: &'a InterfacesOutput,
    equivalences: &'a [EquivalenceFiles],
    reductions: &'a [ReductionFile],
    /// Theorem constant -> its binder.
    binders: HashMap<String, String>,
}

/// One step of the path: the hop, and the two neighbouring (specialized) game instances in path
/// order.
struct Step<'p> {
    hop: &'p GameHop<'p>,
    from: &'p GameInstance,
    to: &'p GameInstance,
}

/// The lemma statement, proof lines and imports that the steps add up to.
#[derive(Default)]
struct Body {
    requires: Vec<String>,
    restrictions: Vec<String>,
    module_type: Option<String>,
    terms: Vec<EcExpr>,
    haves: Vec<String>,
    /// Theorem constants that a lemma or an experiment reads where the path does not fix them.
    free: Vec<String>,
    reduction_terms: usize,
    open_hops: Vec<OpenHop>,
    /// The reduction adversaries, before the section.
    modules: Vec<EcItem>,
    /// The equivalence and bound lemmas, before the proposition lemma.
    lemmas: Vec<EcLemma>,
    reduction_steps: Vec<ReductionStep>,
}

impl Body {
    fn require(&mut self, theory: String) {
        push_unique(&mut self.requires, theory);
    }
}

impl Ctx<'_, '_> {
    fn outcome(&self, proof: &Proof<'_>) -> Result<PropositionOutcome, EcExportError> {
        let path: Vec<&GameInstance> = proof.instances().collect();
        let hops: Vec<&GameHop<'_>> = proof.game_hops().collect();
        if let Some(hybrid) = hops.iter().find(|h| matches!(h, GameHop::Hybrid(_))) {
            return Ok(PropositionOutcome::Skipped(SkippedProposition {
                name: proof.name().to_string(),
                left: hybrid.left_game_instance_name().to_string(),
                right: hybrid.right_game_instance_name().to_string(),
                reason: HYBRID_REASON,
            }));
        }
        let mut body = Body::default();
        for (i, hop) in hops.iter().enumerate() {
            let step = Step {
                hop,
                from: path[i],
                to: path[i + 1],
            };
            self.add_step(&step, &mut body)?;
        }
        let first = path[0];
        let last = path[path.len() - 1];
        let lhs = self.advantage(first, last, &mut body);
        Ok(PropositionOutcome::File(self.file(
            proof.name(),
            lhs,
            body,
        )?))
    }

    fn add_step(&self, step: &Step<'_>, body: &mut Body) -> Result<(), EcExportError> {
        let (l, r) = (
            step.hop.left_game_instance_name(),
            step.hop.right_game_instance_name(),
        );
        match step.hop {
            GameHop::Equivalence(_) => {
                let found = self
                    .equivalences
                    .iter()
                    .find(|ef| ef.proof.left_name == l && ef.proof.right_name == r);
                match found {
                    Some(ef) => {
                        let stem = stem(&ef.proof.file_name);
                        // the name proof.rs gives the equivalence lemma
                        let lemma =
                            Names::new().mangle(NameKind::Lemma, &format!("{l}_{r}_equiv"))?;
                        self.use_lemma(step, &ef.proof.file, &stem, &lemma, body);
                    }
                    None => self.open_hop("equivalence", step, body),
                }
            }
            GameHop::Reduction(_) => {
                let rf = self
                    .reductions
                    .iter()
                    .find(|rf| rf.left_name == l && rf.right_name == r)
                    .expect("every reduction outside a hybrid has a file");
                self.reduction_step(step, rf, body)?;
            }
            GameHop::Conjecture(_) => self.open_hop("conjecture", step, body),
            GameHop::Hybrid(_) => unreachable!("a path with a hybrid hop is skipped"),
        }
        Ok(())
    }

    /// A reduction step: an open hop when it leaves a constant of the reduction packages free,
    /// else its adversary, its lemmas (each one time) and the right side of its bound lemma as
    /// the term.
    fn reduction_step(
        &self,
        step: &Step<'_>,
        rf: &ReductionFile,
        body: &mut Body,
    ) -> Result<(), EcExportError> {
        let values = self.step_values(step);
        let Some(adv) = self.adversary(rf, &values, body) else {
            self.open_hop("reduction", step, body);
            return Ok(());
        };
        let sides = self.step_sides(rf, &values, &adv.name, body);
        let span = composition_span(self.theorem.instances[0].game());
        // the lemma binders after `&m`: the free constants, theorem order
        let mut binders = vec![LemmaBinder::Memory("m".to_string())];
        let mut free_args = String::new();
        for (c, ty) in &self.theorem.consts {
            if sides.free.contains(c) {
                push_unique(&mut body.free, c.clone());
                binders.push(LemmaBinder::Typed {
                    name: self.binders[c].clone(),
                    ty: translate_type(ty, span)?,
                });
                free_args.push_str(&format!(" {}", self.binders[c]));
            }
        }
        let taken: Vec<String> = sides.free.iter().map(|c| self.binders[c].clone()).collect();
        let merged = prop_reduction::merge(
            [&sides.game_args[0], &sides.game_args[1]],
            [&sides.assm_args[0], &sides.assm_args[1]],
            &run_params(self.composition(sides.games[0]), span)?,
            sides.same_compositions,
            &taken,
        );
        let hop = format!("{}_{}", rf.left_name, rf.right_name);
        let names = LemmaNames {
            equiv: format!("equiv_{hop}{}", adv.suffix),
            bound: format!("bound_{hop}{}", adv.suffix),
            free_args,
            join: stem(&rf.file_name),
            run: rf.run_lemmas.clone(),
        };
        let (lemmas, equiv_lemmas, term) = step_lemmas(&names, binders, &sides, merged.as_ref());
        // a step with the same hop and the same values uses the lemmas of the first one
        if !body.lemmas.iter().any(|l| l.name == names.bound) {
            body.lemmas.extend(lemmas);
        }
        let n = body.haves.len();
        body.haves.push(format!(
            "have h{n} := {} &m{}.",
            names.bound, names.free_args
        ));
        body.terms.push(term);
        body.reduction_terms += 1;
        body.reduction_steps.push(ReductionStep {
            left: rf.left_name.clone(),
            right: rf.right_name.clone(),
            adversary: adv.name,
            values: adv.fixed,
            equiv_lemmas,
            bound_lemma: names.bound,
        });
        Ok(())
    }

    /// The step's reduction adversary, added to `body` the first time; `None` when the step
    /// leaves a constant of the reduction packages free.
    fn adversary(
        &self,
        rf: &ReductionFile,
        values: &HashMap<String, String>,
        body: &mut Body,
    ) -> Option<Adversary> {
        let mut init = Vec::new();
        for v in &rf.router.init_values {
            init.push(match v {
                RunArgValue::Literal(text) => literal_text_to_expr(text),
                RunArgValue::TheoremConst(t) => literal_text_to_expr(values.get(t)?),
            });
        }
        let fixed: Vec<(String, String)> = self
            .theorem
            .consts
            .iter()
            .filter(|(c, _)| {
                rf.router
                    .init_values
                    .contains(&RunArgValue::TheoremConst(c.clone()))
            })
            .map(|(c, _)| (c.clone(), values[c].clone()))
            .collect();
        let suffix = prop_reduction::suffix(
            &fixed
                .iter()
                .map(|(c, v)| (self.binders[c].clone(), v.clone()))
                .collect::<Vec<_>>(),
        );
        let router_theory = stem(&rf.router_file_name);
        body.require(stem(&rf.file_name));
        body.require(router_theory.clone());
        let (declare, _) = section_lemma(&rf.file, &rf.run_lemmas[0]);
        for r in &declare.restrictions {
            push_unique(&mut body.restrictions, qualify(&router_theory, r));
        }
        if body.module_type.is_none() {
            body.module_type = Some(rf.router.adv.clone());
        }
        let name = format!("B_{}_{}{suffix}", rf.left_name, rf.right_name);
        let defined = body
            .modules
            .iter()
            .any(|m| matches!(m, EcItem::Module(m) if m.name == name));
        if !defined {
            body.modules.push(EcItem::Module(b_module(
                &name,
                &format!("{router_theory}.{}(O)", rf.router.module),
                &rf.router.adv,
                &rf.router.assm_iface,
                init,
            )));
        }
        Some(Adversary {
            name,
            suffix,
            fixed,
        })
    }

    /// The experiments and `run` arguments of the step's two sides, the path's values
    /// substituted, and the theorem constants that stay free.
    fn step_sides<'s>(
        &'s self,
        rf: &ReductionFile,
        values: &HashMap<String, String>,
        adversary: &str,
        body: &mut Body,
    ) -> StepSides<'s> {
        let find = |n: &str| {
            self.theorem
                .find_game_instance(n)
                .expect("a reduction names game instances of the theorem")
        };
        let games = [find(&rf.left_name), find(&rf.right_name)];
        let assms = [
            find(&rf.sides[0].assumption_game),
            find(&rf.sides[1].assumption_game),
        ];
        let mut free = Vec::new();
        let mut args = |inst: &GameInstance| -> Vec<EcExpr> {
            side_run_args(self.composition(inst), inst)
                .into_iter()
                .map(|v| match v {
                    RunArgValue::Literal(text) => literal_text_to_expr(&text),
                    RunArgValue::TheoremConst(c) => match values.get(&c) {
                        Some(lit) => literal_text_to_expr(lit),
                        None => {
                            push_unique(&mut free, c.clone());
                            EcExpr::Var(self.binders[&c].clone())
                        }
                    },
                })
                .collect()
        };
        let game_args = games.map(&mut args);
        let assm_args = assms.map(args);
        let mut exp = |inst: &GameInstance, applied: &str| {
            let mangled = &self.interfaces.comp_mangled[&self.composition(inst).name];
            body.require(format!("Comp_{mangled}"));
            format!("Comp_{mangled}.Exp_{mangled}({applied})")
        };
        let game_exps = games.map(|g| exp(g, "A"));
        let assm_exps = assms.map(|a| exp(a, &format!("{adversary}(A)")));
        let same = |a: &GameInstance, b: &GameInstance| a.game().name == b.game().name;
        StepSides {
            same_compositions: same(games[0], games[1]) && same(assms[0], assms[1]),
            games,
            game_args,
            assm_args,
            game_exps,
            assm_exps,
            free,
        }
    }

    fn open_hop(&self, kind: &'static str, step: &Step<'_>, body: &mut Body) {
        let term = self.advantage(step.from, step.to, body);
        body.terms.push(term);
        body.open_hops.push(OpenHop {
            kind,
            left: step.hop.left_game_instance_name().to_string(),
            right: step.hop.right_game_instance_name().to_string(),
        });
    }

    /// Adds `have` for `lemma` of `file` (the theory `stem`) at the arguments of `step`, and
    /// returns the lemma's statement at those arguments, its names qualified with `stem`.
    fn use_lemma(
        &self,
        step: &Step<'_>,
        file: &EcFile,
        stem: &str,
        lemma: &str,
        body: &mut Body,
    ) -> EcExpr {
        let (declare, lemma) = section_lemma(file, lemma);
        body.require(stem.to_string());
        if body.module_type.is_none() {
            body.module_type = Some(declare.module_type.clone());
        }
        for r in &declare.restrictions {
            push_unique(&mut body.restrictions, qualify(stem, r));
        }
        let values = self.step_values(step);
        let mut args = Vec::new();
        let mut subst = HashMap::new();
        for b in &lemma.binders {
            let LemmaBinder::Typed { name, .. } = b else {
                continue;
            };
            let value = self.binder_value(name, &values, body);
            args.push(render_expr(&value));
            subst.insert(name.clone(), value);
        }
        let n = body.haves.len();
        let applied = std::iter::once(format!("{stem}.{} A &m", lemma.name))
            .chain(args)
            .collect::<Vec<_>>()
            .join(" ");
        body.haves.push(format!("have h{n} := {applied}."));
        substitute(&lemma.statement, stem, &subst)
    }

    /// The value of the lemma binder `binder` at a step: the literal that the path fixes, or
    /// the proposition lemma's own binder.
    fn binder_value(
        &self,
        binder: &str,
        values: &HashMap<String, String>,
        body: &mut Body,
    ) -> EcExpr {
        let (c, _) = self
            .theorem
            .consts
            .iter()
            .find(|(c, _)| self.binders[c] == binder)
            .expect("a lemma binder is a theorem constant");
        match values.get(c) {
            Some(lit) => literal_text_to_expr(lit),
            None => {
                push_unique(&mut body.free, c.clone());
                EcExpr::Var(binder.to_string())
            }
        }
    }

    /// The theorem constants that the specializations of a step fix: constant -> literal.
    fn step_values(&self, step: &Step<'_>) -> HashMap<String, String> {
        let generic = |name: &str| {
            self.theorem
                .find_game_instance(name)
                .expect("a hop names game instances of the theorem")
        };
        let (gl, gr) = (
            generic(step.hop.left_game_instance_name()),
            generic(step.hop.right_game_instance_name()),
        );
        // the path neighbour's name decides; compatibility when the path names neither side
        // (an end of the path is a theorem instance with its own name)
        let forward = if step.from.name == gl.name || step.to.name == gr.name {
            true
        } else if step.from.name == gr.name || step.to.name == gl.name {
            false
        } else {
            game_is_compatible(step.from, gl) && game_is_compatible(step.to, gr)
        };
        let (sl, sr) = if forward {
            (step.from, step.to)
        } else {
            (step.to, step.from)
        };
        assignments(sl, gl)
            .into_iter()
            .chain(assignments(sr, gr))
            .map(|a| (a.original_name(), a.assigned_value()))
            .collect()
    }

    /// `` `|Pr[Exp_<a>(A).run(..) @ &m : res] - Pr[Exp_<b>(A).run(..) @ &m : res]| ``.
    fn advantage(&self, a: &GameInstance, b: &GameInstance, body: &mut Body) -> EcExpr {
        EcExpr::Abs(Box::new(EcExpr::Binop {
            op: EcBinop::Sub,
            lhs: Box::new(self.experiment(a, body)),
            rhs: Box::new(self.experiment(b, body)),
        }))
    }

    fn experiment(&self, inst: &GameInstance, body: &mut Body) -> EcExpr {
        let comp = self.composition(inst);
        let mangled = &self.interfaces.comp_mangled[&comp.name];
        let theory = format!("Comp_{mangled}");
        body.require(theory.clone());
        if body.module_type.is_none() {
            body.module_type = Some(format!(
                "Interfaces.{}",
                self.interfaces.adv_name[&comp.name]
            ));
        }
        let args = side_run_args(comp, inst)
            .into_iter()
            .map(|v| match v {
                RunArgValue::Literal(text) => literal_text_to_expr(&text),
                RunArgValue::TheoremConst(c) => {
                    push_unique(&mut body.free, c.clone());
                    EcExpr::Var(self.binders[&c].clone())
                }
            })
            .collect();
        EcExpr::Pr {
            module: format!("{theory}.Exp_{mangled}(A)"),
            proc: "run".to_string(),
            args,
            memory: "m".to_string(),
            event: Box::new(EcExpr::Var("res".to_string())),
        }
    }

    /// The transformed composition of `inst` (the path's instances come from the theorem
    /// before the transform).
    fn composition(&self, inst: &GameInstance) -> &crate::package::Composition {
        self.theorem
            .instances
            .iter()
            .map(GameInstance::game)
            .find(|c| c.name == inst.game().name)
            .expect("a path instance's composition is a composition of the theorem")
    }

    fn file(&self, name: &str, lhs: EcExpr, body: Body) -> Result<PropositionFile, EcExportError> {
        let span = composition_span(self.theorem.instances[0].game());
        let mut binders = vec![LemmaBinder::Memory("m".to_string())];
        for (c, ty) in &self.theorem.consts {
            if body.free.contains(c) {
                binders.push(LemmaBinder::Typed {
                    name: self.binders[c].clone(),
                    ty: translate_type(ty, span)?,
                });
            }
        }
        let rhs = EcExpr::right_chain(EcBinop::Add, body.terms)
            .unwrap_or_else(|| EcExpr::Var("0%r".to_string()));
        let mut proof: Vec<ProofLine> = body.haves.into_iter().map(tactic).collect();
        proof.push(tactic("smt().".to_string()));
        let lemma = EcLemma {
            name: Names::new().mangle(NameKind::Lemma, name)?,
            binders,
            statement: EcExpr::Binop {
                op: EcBinop::Le,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            proof,
        };
        let declare = DeclareModule {
            name: "A".to_string(),
            module_type: body
                .module_type
                .expect("a path has at least one game instance"),
            restrictions: body.restrictions,
        };
        let file_name = format!("Prop_{name}.ec");
        let file = EcFile {
            header: vec![format!(
                "{file_name} for theorem `{}`, the proposition `{name}` — generated by `domino \
                 easycrypt`.",
                self.theorem.name
            )],
            requires: vec![
                Require {
                    import: true,
                    names: ["AllCore", "Distr", "FMap", "Int", "IntDiv", "Types"]
                        .map(String::from)
                        .to_vec(),
                },
                Require {
                    import: false,
                    names: std::iter::once("Interfaces".to_string())
                        .chain(body.requires)
                        .collect(),
                },
            ],
            items: {
                let mut items = body.modules;
                let mut lemmas = body.lemmas;
                lemmas.push(lemma);
                items.push(EcItem::Section(EcSection {
                    declares: vec![declare],
                    assumptions: vec![],
                    items: vec![],
                    lemmas,
                }));
                items
            },
        };
        Ok(PropositionFile {
            name: name.to_string(),
            file_name,
            file,
            reduction_terms: body.reduction_terms,
            open_hops: body.open_hops,
            reduction_steps: body.reduction_steps,
        })
    }
}

/// A reduction adversary of a proposition.
struct Adversary {
    /// `B_<L>_<R><s>`.
    name: String,
    /// `<s>`.
    suffix: String,
    /// `(constant, value)` for each constant that the reduction packages read, theorem order.
    fixed: Vec<(String, String)>,
}

/// The two sides of a reduction step.
struct StepSides<'s> {
    games: [&'s GameInstance; 2],
    same_compositions: bool,
    game_args: [Vec<EcExpr>; 2],
    assm_args: [Vec<EcExpr>; 2],
    /// `Comp_<G>.Exp_<G>(A)` of each side.
    game_exps: [String; 2],
    /// `Comp_<Assm>.Exp_<Assm>(B(A))` of each side.
    assm_exps: [String; 2],
    /// The theorem constants that a `run` argument reads and the path does not fix.
    free: Vec<String>,
}

/// The names that the lemmas of a reduction step use.
struct LemmaNames {
    equiv: String,
    bound: String,
    /// ` <binder>` for each free constant.
    free_args: String,
    /// The theory of `Red_<L>_<R>.ec`.
    join: String,
    run: [String; 2],
}

/// The equivalence lemma(s) and the bound lemma of a reduction step, the names of the
/// equivalence lemmas, and the step's term.
fn step_lemmas(
    names: &LemmaNames,
    binders: Vec<LemmaBinder>,
    sides: &StepSides<'_>,
    merged: Option<&prop_reduction::Merged>,
) -> (Vec<EcLemma>, Vec<String>, EcExpr) {
    let pr = |exp: &String, args: &[EcExpr]| prop_reduction::pr(exp.clone(), args.to_vec());
    let equiv = |name: String, binders: Vec<LemmaBinder>, game: &[EcExpr], assm: &[EcExpr], i| {
        let mut pre = vec!["={glob A}".to_string()];
        pre.extend(prop_reduction::arg_conjunct(game, 1));
        pre.extend(prop_reduction::arg_conjunct(assm, 2));
        EcLemma {
            name,
            binders,
            statement: eq(pr(&sides.game_exps[i], game), pr(&sides.assm_exps[i], assm)),
            proof: vec![
                tactic(format!(
                    "byequiv (: {} ==> ={{res}}) => //.",
                    pre.join(" /\\ ")
                )),
                tactic("proc; inline *; wp.".to_string()),
                tactic(format!("call ({}.{} A).", names.join, names.run[i])),
                tactic("by auto => /#.".to_string()),
            ],
        }
    };
    let free = &names.free_args;
    let mut lemmas = Vec::new();
    let mut equivs = Vec::new();
    let rewrite = match merged {
        Some(m) => {
            let mut b = binders.clone();
            b.extend(m.binders.iter().map(|(name, ty)| LemmaBinder::Typed {
                name: name.clone(),
                ty: ty.clone(),
            }));
            lemmas.push(equiv(names.equiv.clone(), b, &m.game, &m.assm, 0));
            equivs.push(names.equiv.clone());
            format!("by rewrite !({} &m{free}).", names.equiv)
        }
        None => {
            for (i, side) in ["_L", "_R"].iter().enumerate() {
                let name = format!("{}{side}", names.equiv);
                let (g, a) = (&sides.game_args[i], &sides.assm_args[i]);
                lemmas.push(equiv(name.clone(), binders.clone(), g, a, i));
                equivs.push(name);
            }
            format!(
                "by rewrite ({} &m{free}) ({} &m{free}).",
                equivs[0], equivs[1]
            )
        }
    };
    let diff = |exps: &[String; 2], args: &[Vec<EcExpr>; 2]| {
        prop_reduction::abs_diff(pr(&exps[0], &args[0]), pr(&exps[1], &args[1]))
    };
    let term = diff(&sides.assm_exps, &sides.assm_args);
    lemmas.push(EcLemma {
        name: names.bound.clone(),
        binders,
        statement: eq(diff(&sides.game_exps, &sides.game_args), term.clone()),
        proof: vec![tactic(rewrite)],
    });
    (lemmas, equivs, term)
}

fn eq(lhs: EcExpr, rhs: EcExpr) -> EcExpr {
    EcExpr::Binop {
        op: EcBinop::Eq,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

/// The `run` parameters of `comp`'s experiment, as `Comp_<C>.ec` names them.
fn run_params(
    comp: &crate::package::Composition,
    span: miette::SourceSpan,
) -> Result<Vec<prop_reduction::Param>, EcExportError> {
    let mut names = Names::new();
    names.mangle(NameKind::Var, "abort_flag")?;
    let mut out = Vec::new();
    for (c, ty) in &comp.consts {
        if composition_const_needs_arg(comp, c, ty) {
            out.push((names.mangle(NameKind::Var, c)?, translate_type(ty, span)?));
        }
    }
    Ok(out)
}

/// `B_<L>_<R><s> (A : Adv_<G>) (O : Iface_<Assm>)`: starts the router with the step's values and
/// runs `A` against it.
fn b_module(
    name: &str,
    router: &str,
    adv: &str,
    assm_iface: &str,
    init_args: Vec<EcExpr>,
) -> EcModule {
    let run = EcProc {
        name: "run".to_string(),
        args: vec![],
        ret: EcType::Bool,
        locals: vec![("b'".to_string(), EcType::Bool, None)],
        body: EcBlock(vec![
            EcStmt::Call {
                lhs: None,
                module: router.to_string(),
                proc: "init".to_string(),
                args: init_args,
            },
            EcStmt::Call {
                lhs: Some(EcLvalue::Var("b'".to_string())),
                module: format!("A({router})"),
                proc: "run".to_string(),
                args: vec![],
            },
        ]),
        ret_expr: Some(EcExpr::Var("b'".to_string())),
    };
    EcModule {
        name: name.to_string(),
        params: vec![
            ("A".to_string(), adv.to_string()),
            ("O".to_string(), assm_iface.to_string()),
        ],
        implements: None,
        vars: vec![],
        procs: vec![run],
    }
}

fn tactic(text: String) -> ProofLine {
    ProofLine::Tactic {
        indent: 0,
        bullet: None,
        text,
    }
}

/// The file name without `.ec`: the theory that `require` loads.
fn stem(file_name: &str) -> String {
    file_name.trim_end_matches(".ec").to_string()
}

/// A module that a file names: a `Comp_` theory's module as it is, a module of the file itself
/// qualified with the file's theory.
fn qualify(stem: &str, module: &str) -> String {
    if module.starts_with("Comp_") {
        module.to_string()
    } else {
        format!("{stem}.{module}")
    }
}

/// The section's adversary and the lemma `name` of `file`.
fn section_lemma<'f>(file: &'f EcFile, name: &str) -> (&'f DeclareModule, &'f EcLemma) {
    file.items
        .iter()
        .find_map(|item| match item {
            EcItem::Section(s) => s
                .lemmas
                .iter()
                .find(|l| l.name == name)
                .map(|l| (&s.declares[0], l)),
            _ => None,
        })
        .unwrap_or_else(|| panic!("the file has the lemma {name}"))
}

/// `e` with each binder replaced by its value and each module of the file qualified.
fn substitute(e: &EcExpr, stem: &str, subst: &HashMap<String, EcExpr>) -> EcExpr {
    let go = |e: &EcExpr| Box::new(substitute(e, stem, subst));
    match e {
        EcExpr::Var(v) => subst.get(v).cloned().unwrap_or_else(|| e.clone()),
        EcExpr::Abs(inner) => EcExpr::Abs(go(inner)),
        EcExpr::Binop { op, lhs, rhs } => EcExpr::Binop {
            op: *op,
            lhs: go(lhs),
            rhs: go(rhs),
        },
        EcExpr::Pr {
            module,
            proc,
            args,
            memory,
            event,
        } => EcExpr::Pr {
            module: qualify(stem, module),
            proc: proc.clone(),
            args: args.iter().map(|a| substitute(a, stem, subst)).collect(),
            memory: memory.clone(),
            event: event.clone(),
        },
        other => other.clone(),
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::path::{Path, PathBuf};

    use crate::project::{DirectoryFiles, DirectoryProject, Project};
    use crate::writers::easycrypt::export::export_theorem;
    use crate::writers::easycrypt::export::ExportedTheorem;

    fn export(dir: &str, theorem_name: &str) -> ExportedTheorem {
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let theorem = project.get_theorem(theorem_name).unwrap();
        export_theorem(theorem, &project).unwrap()
    }

    fn text<'e>(e: &'e ExportedTheorem, file: &str) -> &'e str {
        e.files
            .get(Path::new(file))
            .unwrap_or_else(|| panic!("no {file} in {:?}", e.files.keys()))
    }

    /// The lemma statement, whitespace-normalized: from `lemma` to `proof.`.
    fn statement(text: &str) -> String {
        let start = text.find("lemma ").unwrap();
        let end = text[start..].find("proof.").unwrap() + start;
        text[start..end]
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }

    const KEM_DEM: &str = "example-projects/kem-dem/kem-dem-cca-ssp";
    const RED_CONSTS: &str = "testdata/easycrypt/reduction-consts";

    /// The statement of lemma `name`, whitespace-normalized: from `lemma <name> ` to `proof.`.
    fn statement_of(text: &str, name: &str) -> String {
        let start = text
            .find(&format!("lemma {name} "))
            .unwrap_or_else(|| panic!("no lemma {name} in {text}"));
        let end = text[start..].find("proof.").unwrap() + start;
        text[start..end]
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// `hello-world` with the one-step proposition `BigToMedium` on its reduction (story 101).
    pub(crate) fn hello_world_with_proposition() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        let from = Path::new("example-projects/hello-world");
        copy_dir(from, dir.path());
        let proof = dir.path().join("theorem/proof.ssp");
        let text = std::fs::read_to_string(&proof).unwrap();
        let end = text.trim_end().rfind('}').unwrap();
        let text = format!(
            "{}\n    propositions {{\n        BigToMedium: big_composition ~ \
             medium_composition_more_oracles\n    }}\n}}\n",
            &text[..end]
        );
        std::fs::write(proof, text).unwrap();
        dir
    }

    fn copy_dir(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).unwrap();
        for entry in std::fs::read_dir(from).unwrap() {
            let path = entry.unwrap().path();
            let target = to.join(path.file_name().unwrap());
            if path.is_dir() {
                copy_dir(&path, &target);
            } else {
                std::fs::copy(&path, &target).unwrap();
            }
        }
    }
    const OPEN_HOP: &str = "testdata/easycrypt/proposition-open-hop";

    #[test]
    fn kem_dem_main_has_one_adversary_for_each_reduction_and_bound_lemmas_in_path_order() {
        let e = export(KEM_DEM, "kem_dem_cca_ssp");
        let report = &e.propositions[0];
        assert_eq!(report.name, "Main");
        assert_eq!(report.file, "Prop_Main.ec");
        assert_eq!(report.reduction_terms, 3);
        assert!(report.open_hops.is_empty());
        let t = text(&e, "Prop_Main.ec");
        assert!(!t.contains("RedExp") && !t.contains("setup"), "{t}");
        let mut last = 0;
        for (r, step) in e.reductions.iter().zip(&report.reduction_steps) {
            let hop = format!("{}_{}", r.left_name, r.right_name);
            // one adversary with an empty suffix, and a merged equivalence lemma
            assert_eq!(step.adversary, format!("B_{hop}"));
            assert!(step.values.is_empty());
            assert_eq!(step.equiv_lemmas, vec![format!("equiv_{hop}")]);
            assert_eq!(step.bound_lemma, format!("bound_{hop}"));
            assert_eq!(t.matches(&format!("module B_{hop} ")).count(), 1, "{t}");
            assert!(t.contains(&format!("lemma equiv_{hop} &m (")), "{t}");
            let at = t
                .find(&format!(":= bound_{hop} &m."))
                .unwrap_or_else(|| panic!("no have of bound_{hop} in {t}"));
            assert!(at > last, "{t}");
            last = at;
        }
        // the third term in its hop's direction: the left side (assumption arguments `true`)
        // first
        let third = &report.reduction_steps[2].adversary;
        let s = statement_of(t, "Main");
        assert!(
            s.contains(&format!(
                "`|Pr[Comp_Game_CCA_KEM.Exp_Game_CCA_KEM({third}(A)).run(true) @ &m : res] - \
                 Pr[Comp_Game_CCA_KEM.Exp_Game_CCA_KEM({third}(A)).run(false) @ &m : res]|"
            )),
            "{s}"
        );
    }

    #[test]
    fn the_first_kem_dem_reduction_matches_the_prototype() {
        let e = export(KEM_DEM, "kem_dem_cca_ssp");
        let t = text(&e, "Prop_Main.ec");
        let proto = std::fs::read_to_string(
            "testdata/easycrypt/reduction-prototype/layout/kem-dem/Prop_FirstReduction.ec",
        )
        .unwrap();
        let hop = "Game_MOD_CCA_PKE_Real_KEM_Real_DEM_Game_MOD_CCA_PKE_Ideal_KEM_Real_DEM";
        for name in [format!("equiv_{hop}"), format!("bound_{hop}")] {
            assert_eq!(statement_of(t, &name), statement_of(&proto, &name));
        }
        let b = format!("module B_{hop} ");
        let block = |text: &str| {
            let at = text.find(&b).unwrap();
            text[at..at + text[at..].find("}.").unwrap()].to_string()
        };
        assert_eq!(block(t), block(&proto));
    }

    #[test]
    fn a_path_that_fixes_the_constant_gets_one_adversary_for_each_value() {
        let e = export(RED_CONSTS, "RedConsts");
        let flip = e
            .propositions
            .iter()
            .find(|p| p.name == "FlipBound")
            .unwrap();
        let hop = "mod_real_mod_ideal";
        let advs: Vec<&str> = flip
            .reduction_steps
            .iter()
            .map(|s| s.adversary.as_str())
            .collect();
        assert_eq!(
            advs,
            [format!("B_{hop}_b_false"), format!("B_{hop}_b_true")]
        );
        assert_eq!(
            flip.reduction_steps[0].values,
            vec![("b".to_string(), "false".to_string())]
        );
        assert_eq!(flip.open_hops.len(), 1);
        assert_eq!(flip.open_hops[0].kind, "conjecture");
        let t = text(&e, "Prop_FlipBound.ec");
        let proto = std::fs::read_to_string(
            "testdata/easycrypt/reduction-prototype/layout/reduction-consts/Prop_RedConsts.ec",
        )
        .unwrap();
        for name in [
            format!("equiv_{hop}_b_false"),
            format!("bound_{hop}_b_false"),
            format!("equiv_{hop}_b_true"),
            format!("bound_{hop}_b_true"),
            "FlipBound".to_string(),
        ] {
            assert_eq!(statement_of(t, &name), statement_of(&proto, &name));
        }
    }

    #[test]
    fn a_path_that_leaves_the_constant_free_makes_the_reduction_an_open_hop() {
        let e = export(RED_CONSTS, "RedConsts");
        let free = e.propositions.iter().find(|p| p.name == "Free").unwrap();
        assert_eq!(free.reduction_terms, 0);
        assert!(free.reduction_steps.is_empty());
        assert_eq!(free.open_hops.len(), 1);
        assert_eq!(free.open_hops[0].kind, "reduction");
        let t = text(&e, "Prop_Free.ec");
        assert!(!t.contains("module B_"), "{t}");
        assert!(t.contains("lemma Free &m (b : bool) :"), "{t}");
    }

    #[test]
    fn hello_world_with_a_proposition_gets_left_and_right_lemmas_with_literals() {
        let dir = hello_world_with_proposition();
        let e = export(dir.path().to_str().unwrap(), "Proof");
        let p = &e.propositions[0];
        let hop = "big_composition_medium_composition_more_oracles";
        assert_eq!(
            p.reduction_steps[0].equiv_lemmas,
            vec![format!("equiv_{hop}_L"), format!("equiv_{hop}_R")]
        );
        let t = text(&e, "Prop_BigToMedium.ec");
        let proto = std::fs::read_to_string(
            "testdata/easycrypt/reduction-prototype/layout/hello-world/Prop_BigToMedium.ec",
        )
        .unwrap();
        for name in [
            format!("equiv_{hop}_L"),
            format!("equiv_{hop}_R"),
            format!("bound_{hop}"),
            "BigToMedium".to_string(),
        ] {
            assert_eq!(statement_of(t, &name), statement_of(&proto, &name));
        }
        assert!(
            t.contains(&format!("call (Red_{hop}.run_{hop}_R A).")),
            "{t}"
        );
    }

    #[test]
    fn kem_dem_main_uses_the_equivalence_lemma_with_false_and_true() {
        let e = export(KEM_DEM, "kem_dem_cca_ssp");
        let t = text(&e, "Prop_Main.ec");
        let eq = "Eq_Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM.\
                  Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM_equiv A &m";
        assert!(t.contains(&format!("{eq} false.")), "{t}");
        assert!(t.contains(&format!("{eq} true.")), "{t}");
        assert!(!t.contains("admit"), "{t}");
    }

    #[test]
    fn kem_dem_main_takes_no_constant() {
        let e = export(KEM_DEM, "kem_dem_cca_ssp");
        let s = statement_of(text(&e, "Prop_Main.ec"), "Main");
        assert!(
            s.starts_with("lemma Main &m : `|Pr[Comp_Game_MON_CCA_PKE"),
            "{s}"
        );
        assert!(
            s.contains("run(false) @ &m : res] - Pr[Comp_Game_MON_CCA_PKE"),
            "{s}"
        );
    }

    #[test]
    fn a_conjecture_is_an_open_hop_with_its_own_term() {
        let e = export(OPEN_HOP, "Proof");
        let main = e.propositions.iter().find(|p| p.name == "Main").unwrap();
        assert_eq!(main.reduction_terms, 0);
        assert_eq!(main.open_hops.len(), 1);
        assert_eq!(main.open_hops[0].kind, "conjecture");
        assert_eq!(main.open_hops[0].left, "small_composition");
        assert_eq!(main.open_hops[0].right, "other_small_composition");
        let s = statement_of(text(&e, "Prop_Main.ec"), "Main");
        let small = "Pr[Comp_SmallComposition.Exp_SmallComposition(A).run() @ &m : res]";
        assert!(s.ends_with(&format!("<= `|{small} - {small}|.")), "{s}");
    }

    #[test]
    fn a_path_of_equivalences_only_is_bounded_by_zero() {
        let e = export(OPEN_HOP, "Proof");
        let s = statement(text(&e, "Prop_EqOnly.ec"));
        assert!(s.ends_with("<= 0%r."), "{s}");
        let t = text(&e, "Prop_EqOnly.ec");
        assert!(
            t.contains("medium_composition_small_composition_equiv A &m."),
            "{t}"
        );
    }

    #[test]
    fn a_path_with_a_hybrid_hop_is_skipped() {
        let e = export("example-projects/hello-world-hybrid", "Hybrid");
        assert!(!e.files.contains_key(Path::new("Prop_main.ec")));
        assert!(e.propositions.is_empty());
        assert_eq!(e.skipped_propositions.len(), 1);
        let skip = &e.skipped_propositions[0];
        assert_eq!(skip.name, "main");
        assert_eq!(skip.left, "h$false$");
        assert_eq!(skip.right, "h$true$");
        assert_eq!(skip.reason, super::HYBRID_REASON);
    }
}
