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
    DeclareModule, EcBinop, EcExpr, EcFile, EcItem, EcLemma, EcSection, LemmaBinder, ProofLine,
    Require,
};
use super::interfaces::{composition_span, InterfacesOutput};
use super::names::{NameKind, Names};
use super::proof::{literal_text_to_expr, side_run_args, EquivalenceFiles, RunArgValue};
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
    /// `"conjecture"` or `"equivalence"`.
    pub kind: &'static str,
    /// The hop's game instances, as the hop names them.
    pub left: String,
    pub right: String,
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
                let stem = stem(&rf.file_name);
                let rhs = self.use_lemma(step, &rf.file, &stem, &rf.lemmas.bound, body);
                let EcExpr::Binop { rhs: term, .. } = rhs else {
                    unreachable!("a bound lemma is an equality")
                };
                body.terms.push(*term);
                body.reduction_terms += 1;
            }
            GameHop::Conjecture(_) => self.open_hop("conjecture", step, body),
            GameHop::Hybrid(_) => unreachable!("a path with a hybrid hop is skipped"),
        }
        Ok(())
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
            items: vec![EcItem::Section(EcSection {
                declares: vec![declare],
                assumptions: vec![],
                items: vec![],
                lemmas: vec![lemma],
            })],
        };
        Ok(PropositionFile {
            name: name.to_string(),
            file_name,
            file,
            reduction_terms: body.reduction_terms,
            open_hops: body.open_hops,
        })
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
mod tests {
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
    const OPEN_HOP: &str = "testdata/easycrypt/proposition-open-hop";

    #[test]
    fn kem_dem_main_has_three_reduction_terms_in_path_order() {
        let e = export(KEM_DEM, "kem_dem_cca_ssp");
        let report = &e.propositions[0];
        assert_eq!(report.name, "Main");
        assert_eq!(report.file, "Prop_Main.ec");
        assert_eq!(report.reduction_terms, 3);
        assert!(report.open_hops.is_empty());
        let s = statement(text(&e, "Prop_Main.ec"));
        let reds: Vec<&str> = e.reductions.iter().map(|r| r.file.as_str()).collect();
        let positions: Vec<usize> = reds
            .iter()
            .map(|f| {
                let stem = f.trim_end_matches(".ec");
                s.find(&format!("Pr[{stem}.RedExp_"))
                    .unwrap_or_else(|| panic!("{stem} not in {s}"))
            })
            .collect();
        assert!(positions.windows(2).all(|w| w[0] < w[1]), "{s}");
        // the third term in its hop's direction: the left side (assumption arguments `true`)
        // first
        let third = reds[2].trim_end_matches(".ec");
        let red = &third["Red_".len()..];
        assert!(
            s.contains(&format!(
                "`|Pr[{third}.RedExp_{red}(A).run(true) @ &m : res] - \
                 Pr[{third}.RedExp_{red}(A).run(false) @ &m : res]|"
            )),
            "{s}"
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
        let s = statement(text(&e, "Prop_Main.ec"));
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
        let s = statement(text(&e, "Prop_Main.ec"));
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
