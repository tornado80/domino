// SPDX-License-Identifier: MIT OR Apache-2.0

//! The package invariants in `SideInv_<C>_<O>`, from the package lemmas (story 77, ADR 0016).
//!
//! The proof goes bottom-up along the call graph, which is acyclic. For an oracle `q` of an
//! instance `X` and an instance `Y` with invariants that `X` is or calls, the lemma
//! `inv_<Y>_by_<X>_<q>`, `hoare[Pkg_Inst_<X>.q : Inv_Y ==> res <> None => Inv_Y]` (`Inv_Y`: the
//! package invariants of `Y` on its variables), is
//!
//! - for `Y = X`: the package-invariant lemma `PkgInv_<V_X>_<q>` of `X`'s clone, with `I` set to
//!   `X`'s import provider `P`;
//! - for `Y` below `X`: the frame lemma `Frame_<V_X>_<q>` of `X`'s clone, with `I` = `P` and
//!   `J` = `J_<Y>_in_<X>`, `Inv_Y` as a function of `glob P`. The game file gives the adapter of
//!   `X` a procedure that reads every variable below `X` (`ec_footprint`), so `glob P` holds
//!   exactly the variables of the instances below `X`, and EasyCrypt orders them by their
//!   paths: `J_<Y>_in_<X>` reads `Y`'s variables at their positions in that order. The axiom
//!   for an import `p` of `X`, which `P` forwards to an oracle `r` of an instance `Z`, is the
//!   lemma of `r` of `Z` for `Y` when `Y` is `Z` or below it; otherwise `Z` cannot write the
//!   variables of `Y`, and `call (: true ==> true)` keeps `J`.
//!
//! The router calls one oracle of one instance. Its lemmas for the instances with invariants
//! that the call reaches are joined with `conseq`, two at a time, and `call` takes the joined
//! lemma: an instance that the call cannot reach keeps its invariants, as `call` keeps the
//! variables that the procedure does not write.

use std::collections::HashSet;

use crate::package::Composition;
use crate::project::Project;

use super::super::ast::{EcBinop, EcExpr, EcItem, EcType};
use super::super::game::{below, InstanceWiring};
use super::super::invariant::{package_invariant_ops, pkg_state_field_name};
use super::super::names::{NameKind, Names};
use super::super::package::{module_vars, ordered_imports};
use super::super::render::render_expr;
use super::super::EcExportError;

/// What the bottom-up proof of one composition reads about its instances, each by its index
/// into `comp.pkgs`.
pub(super) struct BottomUp<'a> {
    comp: &'a Composition,
    /// `Comp_<C>`.
    theory: String,
    wirings: Vec<InstanceWiring>,
    /// The templates `PkgInv_<N>_of_<P>` of each instance's package; empty without invariants.
    templates: Vec<Vec<String>>,
    /// `(record field, module variable)` of each state variable of each instance's package.
    fields: Vec<Vec<(String, String)>>,
    /// The variables of each instance's module.
    vars: Vec<Vec<String>>,
    /// `(Domino import name, procedure)` of each import of each instance, in the order of
    /// `<V>_Imports`.
    imports: Vec<Vec<(String, String)>>,
}

impl<'a> BottomUp<'a> {
    pub(super) fn new(
        comp: &'a Composition,
        theory: String,
        wirings: Vec<InstanceWiring>,
        project: &impl Project,
    ) -> Result<BottomUp<'a>, EcExportError> {
        let mut templates = Vec::new();
        let mut fields = Vec::new();
        let mut vars = Vec::new();
        let mut imports = Vec::new();
        for inst in &comp.pkgs {
            templates.push(
                package_invariant_ops(project, inst)
                    .map_err(EcExportError::from)?
                    .into_iter()
                    .map(|op| op.name)
                    .collect(),
            );
            let mut names = Names::new();
            let mut own = Vec::new();
            for (name, _, _) in &inst.pkg.state {
                let var = names.mangle(NameKind::Var, name)?;
                own.push((pkg_state_field_name(&inst.pkg.name, &var), var));
            }
            fields.push(own);
            vars.push(
                module_vars(&inst.pkg)?
                    .into_iter()
                    .map(|(v, _)| v)
                    .collect(),
            );
            // the procedures of `<V>_Imports`, mangled as there: one registry for all
            let mut names = Names::new();
            let mut procs = Vec::new();
            for (sig, _) in ordered_imports(&inst.pkg) {
                let proc = names.mangle(NameKind::Proc, &sig.name)?;
                for (arg, _) in &sig.args {
                    names.mangle(NameKind::Var, arg)?;
                }
                procs.push((sig.name.clone(), proc));
            }
            imports.push(procs);
        }
        Ok(BottomUp {
            comp,
            theory,
            wirings,
            templates,
            fields,
            vars,
            imports,
        })
    }

    fn has_invariants(&self, idx: usize) -> bool {
        !self.templates[idx].is_empty()
    }

    /// Whether some instance of the composition has package invariants.
    pub(super) fn any_invariants(&self) -> bool {
        (0..self.comp.pkgs.len()).any(|i| self.has_invariants(i))
    }

    /// The instances with invariants that a call to instance `idx` can change: `idx` itself
    /// and the instances below it.
    fn reach(&self, idx: usize) -> Vec<usize> {
        std::iter::once(idx)
            .chain(below(self.comp, idx))
            .filter(|&i| self.has_invariants(i))
            .collect()
    }

    fn mangled(&self, idx: usize) -> &str {
        &self.wirings[idx].mangled
    }

    /// `Comp_<C>.<P>`, the import provider of instance `idx`.
    fn provider(&self, idx: usize) -> String {
        let p = self.wirings[idx]
            .provider
            .as_ref()
            .expect("an instance with imports has a provider");
        format!("{}.{p}", self.theory)
    }

    /// The package invariants of instance `idx`, with each state field read by `read`.
    fn invariants(&self, idx: usize, read: impl Fn(&str) -> EcExpr) -> EcExpr {
        let state = EcExpr::RecordLit {
            fields: self.fields[idx]
                .iter()
                .map(|(field, var)| (field.clone(), read(var)))
                .collect(),
        };
        EcExpr::right_chain(
            EcBinop::And,
            self.templates[idx]
                .iter()
                .map(|t| EcExpr::App {
                    head: t.clone(),
                    args: vec![state.clone()],
                })
                .collect(),
        )
        .expect("an instance with invariants has a template")
    }

    /// `Inv_Y`: the package invariants of instance `idx` on its module variables.
    fn inv(&self, idx: usize) -> String {
        render_expr(&self.invariants(idx, |var| EcExpr::Qualified {
            path: vec![
                self.theory.clone(),
                format!("Pkg_Inst_{}", self.mangled(idx)),
                var.to_string(),
            ],
            mem: None,
        }))
    }

    /// `J_<Y>_in_<X>`.
    fn j_name(&self, y: usize, x: usize) -> String {
        format!("J_{}_in_{}", self.mangled(y), self.mangled(x))
    }

    /// `J_<Y>_in_<X> (glob <P>)`.
    fn j(&self, y: usize, x: usize) -> String {
        format!("{} (glob {})", self.j_name(y, x), self.provider(x))
    }

    /// The operators the proofs use: `J_<Y>_in_<X>` for each instance `X` with imports and each
    /// instance `Y` with invariants below it.
    pub(super) fn items(&self) -> Vec<EcItem> {
        let mut items = Vec::new();
        for x in (0..self.comp.pkgs.len()).filter(|&x| self.wirings[x].provider.is_some()) {
            // `glob` of the provider: every variable below `x`, ordered by its path
            let mut glob: Vec<(String, usize, &str)> = below(self.comp, x)
                .into_iter()
                .flat_map(|j| {
                    let path = format!(
                        "{}.Cloned_Pkg_{}.{}",
                        self.theory,
                        self.mangled(j),
                        self.wirings[j].variant
                    );
                    self.vars[j]
                        .iter()
                        .map(move |v| (format!("{path}.{v}"), j, v.as_str()))
                })
                .collect();
            glob.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
            for y in below(self.comp, x)
                .into_iter()
                .filter(|&y| self.has_invariants(y))
            {
                let read = |var: &str| {
                    let at = glob
                        .iter()
                        .position(|(_, j, v)| *j == y && *v == var)
                        .expect("a state variable of an instance below is in the glob");
                    let g = EcExpr::Var("g".to_string());
                    if glob.len() == 1 {
                        g
                    } else {
                        EcExpr::Proj {
                            expr: Box::new(g),
                            index: at + 1,
                        }
                    }
                };
                items.push(EcItem::OpDef {
                    name: self.j_name(y, x),
                    args: vec![("g".to_string(), EcType::Glob(self.provider(x)))],
                    ret: Some(EcType::Bool),
                    body: self.invariants(y, read),
                });
            }
        }
        items
    }

    /// The proof lines before the router: one `have` for each lemma that the call of oracle
    /// `oracle` of instance `idx` needs; and the `call` of the router's `if` branch.
    pub(super) fn call_of(&self, idx: usize, oracle: &str) -> (Vec<String>, String) {
        let mut gen = Gen {
            up: self,
            lines: Vec::new(),
            done: HashSet::new(),
        };
        let reach = self.reach(idx);
        let Some((&first, rest)) = reach.split_first() else {
            return (
                Vec::new(),
                "call (: true ==> true); 1: trivial.".to_string(),
            );
        };
        let mut joined = gen.lemma(first, idx, oracle);
        let mut parts = vec![self.inv(first)];
        for &y in rest {
            let next = gen.lemma(y, idx, oracle);
            parts.push(self.inv(y));
            let conj = format!("({})", parts.join(") /\\ ("));
            let name = format!(
                "all_{}_{}_{}",
                self.mangled(idx),
                proc_name(oracle),
                parts.len()
            );
            gen.have(
                &name,
                &format!(
                    "{} : {conj} ==> res <> None => {conj}",
                    self.proc(idx, oracle)
                ),
                &format!("by conseq {joined} {next} => /#."),
            );
            joined = name;
        }
        (gen.lines, format!("call {joined}."))
    }

    /// `Comp_<C>.Pkg_Inst_<X>.<q>`.
    fn proc(&self, idx: usize, oracle: &str) -> String {
        format!(
            "{}.Pkg_Inst_{}.{}",
            self.theory,
            self.mangled(idx),
            proc_name(oracle)
        )
    }

    /// `Comp_<C>.Cloned_Pkg_<X>.<lemma>`, applied to `X`'s import provider when it has one.
    fn clone_lemma(&self, idx: usize, lemma: &str) -> String {
        let path = format!("{}.Cloned_Pkg_{}.{lemma}", self.theory, self.mangled(idx));
        match self.wirings[idx].provider {
            Some(_) => format!("{path} {}", self.provider(idx)),
            None => path,
        }
    }
}

/// The `have`s of one oracle's proof, each once, a lemma after the lemmas it uses.
struct Gen<'u, 'a> {
    up: &'u BottomUp<'a>,
    lines: Vec<String>,
    done: HashSet<String>,
}

impl Gen<'_, '_> {
    fn have(&mut self, name: &str, judgement: &str, proof: &str) {
        self.lines
            .push(format!("have {name} : hoare[{judgement}]."));
        self.lines.push(format!("+ {proof}"));
        self.done.insert(name.to_string());
    }

    /// The lemma that oracle `oracle` of instance `x` keeps the invariants of instance `y`,
    /// which is `x` or below it. Returns its name.
    fn lemma(&mut self, y: usize, x: usize, oracle: &str) -> String {
        let up = self.up;
        let name = format!(
            "inv_{}_by_{}_{}",
            up.mangled(y),
            up.mangled(x),
            proc_name(oracle)
        );
        if self.done.contains(&name) {
            return name;
        }
        let variant = &up.wirings[x].variant;
        let proof = if y == x {
            let lemma = up.clone_lemma(x, &format!("PkgInv_{variant}_{oracle}"));
            format!("by conseq ({lemma}) => /#.")
        } else {
            let axioms: Vec<String> = up.imports[x]
                .iter()
                .map(|(import, proc)| self.axiom(y, x, import, proc))
                .collect();
            let frame = up.clone_lemma(x, &format!("Frame_{variant}_{oracle}"));
            format!(
                "by conseq ({frame} {} {}) => /#.",
                up.j_name(y, x),
                axioms.join(" ")
            )
        };
        let inv = up.inv(y);
        self.have(
            &name,
            &format!("{} : {inv} ==> res <> None => {inv}", up.proc(x, oracle)),
            &proof,
        );
        name
    }

    /// The axiom of a frame lemma of instance `x` about its import `import` (procedure `proc`),
    /// for the invariants of instance `y`. Returns its name.
    fn axiom(&mut self, y: usize, x: usize, import: &str, proc: &str) -> String {
        let up = self.up;
        let name = format!("ax_{}_via_{}_{proc}", up.mangled(y), up.mangled(x));
        if self.done.contains(&name) {
            return name;
        }
        let edge = up
            .comp
            .edges
            .iter()
            .find(|e| e.from() == x && e.name() == import)
            .expect("every import is wired to one edge");
        let (z, callee) = (edge.to(), edge.sig().name.as_str());
        let direct = up.wirings[x].provider.as_deref()
            == Some(format!("Pkg_Inst_{}", up.mangled(z)).as_str());
        let proof = match (up.reach(z).contains(&y), direct) {
            (true, true) => format!("by conseq {} => /#.", self.lemma(y, z, callee)),
            (true, false) => format!("by proc; call {}; auto => /#.", self.lemma(y, z, callee)),
            (false, true) => {
                "by proc*; call (: true ==> true); [trivial | auto => /#].".to_string()
            }
            (false, false) => {
                "by proc; call (: true ==> true); [trivial | auto => /#].".to_string()
            }
        };
        let j = up.j(y, x);
        self.have(
            &name,
            &format!("{}.{proc} : {j} ==> res <> None => {j}", up.provider(x)),
            &proof,
        );
        name
    }
}

/// The EasyCrypt procedure of a Domino oracle.
fn proc_name(oracle: &str) -> String {
    Names::new()
        .mangle(NameKind::Proc, oracle)
        .expect("an oracle name that the package file mangled")
}

/// A formula as one line.
pub(super) fn line(e: &EcExpr) -> String {
    render_expr(e)
}
