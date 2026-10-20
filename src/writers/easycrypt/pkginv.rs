// SPDX-License-Identifier: MIT OR Apache-2.0

//! The package lemmas of the package variants (stories 76 and 77, ADR 0016).
//!
//! For each package variant `<V>` whose package `P` has package invariants, with the named
//! invariants `PkgInv_<N>_of_<P>` (story 73) applied to the variant's state record:
//!
//! - `PkgInv_<V>_<O>.ec`, for each oracle `<O>`: the **package-invariant lemma**
//!   `hoare[<V>(I).<o> : PkgInv_… ==> res <> None => PkgInv_…]`, in a section over
//!   `declare module I <: <V>_Imports {-<V>}`. Its proof is `+ proc; inline. admit.`: the
//!   package-invariant job owns the file after translation.
//! - `Frame_<V>_<O>.ec`, for each oracle `<O>`, when the package has imports: the **frame
//!   lemma** `hoare[<V>(I).<o> : J (glob I) ==> res <> None => J (glob I)]`, for any
//!   `J : (glob I) -> bool` that each import keeps (`declare op`, one `declare axiom` for each
//!   import). An import that aborts returns `None`, and then the oracle returns `None`, so its
//!   axiom says nothing about `J` then. Its proof is structural and complete
//!   ([`frame_proof`]); the package-invariant job checks it.
//! - `PkgInv_<V>_init.ec`: the **start lemma** `hoare[<V>(I).init : true ==> PkgInv_…]`, its
//!   proof admitted as the oracle lemmas are; the job owns it.
//!
//! A variant whose package has no package invariant but has imports gets its frame lemmas only
//! (story 77): `SideInv_<C>_<O>` carries the invariants of the instances it calls through it.
//!
//! **The chain.** A composition clones a package variant once for each instance, and a lemma
//! about `<V>` says nothing about a clone. So the files of a variant form one chain of
//! theories: the first file holds `clone include Pkg_<V>.`, each other file `clone include` of
//! the file before it (oracle lemmas, then frame lemmas, then the start lemma), and the join,
//! `PkgInv_<V>.ec`, `clone include` of the last file. The composition clones the join instead
//! of `Pkg_<V>`, and each clone has every lemma about its own copy of `<V>`.
//!
//! A package without imports has no `I`: its lemmas are about `<V>` itself, outside a section,
//! and it has no frame lemmas.

use super::ast::{
    DeclareModule, EcBinop, EcExpr, EcFile, EcItem, EcLemma, EcModule, EcProc, EcSection, EcStmt,
    EcType, ProcSig, ProofLine, Require, SectionAssumption,
};
use super::invariant::{package_invariant_ops, StateOwners};
use super::names::{NameKind, Names};
use super::package::PackageVariant;
use super::EcExportError;
use crate::project::Project;
use crate::theorem::Theorem;

/// The name of the abstract import module in the section of a package lemma.
const IMPORTS: &str = "I";
/// The predicate of a frame lemma.
const FRAME_PRED: &str = "J";
/// The procedure name of the start lemma, and the `<O>` of its file name.
pub const INIT: &str = "init";

/// The package lemma files of one package variant.
pub struct PkgInvFiles {
    /// The package's name in Domino.
    pub package: String,
    /// The variant's module name, `<V>`.
    pub variant: String,
    /// `PkgInv_<V>.ec`, which requires every other file.
    pub join_file: String,
    pub join: EcFile,
    /// `PkgInv_<V>_<O>.ec` for each oracle, in the package's order; empty for a variant
    /// without package invariants.
    pub oracles: Vec<PkgInvLemmaFile>,
    /// `Frame_<V>_<O>.ec` for each oracle; empty for a package without imports.
    pub frames: Vec<PkgInvLemmaFile>,
    /// `PkgInv_<V>_init.ec`; `None` for a variant without package invariants.
    pub start: Option<PkgInvLemmaFile>,
}

/// One lemma file of a package variant.
pub struct PkgInvLemmaFile {
    /// The oracle's Domino name, or [`INIT`] for the start lemma.
    pub oracle: String,
    pub file_name: String,
    pub file: EcFile,
}

/// The stem of the join file of variant `variant`: `PkgInv_<V>`.
pub fn pkg_inv_stem(variant: &str) -> String {
    format!("PkgInv_{variant}")
}

/// The package lemma files of every variant in `variants` that has them
/// ([`lemma_variants`](super::game::lemma_variants)), in the order of `variants`.
pub fn build_pkg_inv_files(
    theorem: &Theorem<'_>,
    project: &impl Project,
    variants: &[PackageVariant],
    owners: &StateOwners,
) -> Result<Vec<PkgInvFiles>, EcExportError> {
    let lemma_variants = super::game::lemma_variants(theorem)?;
    let mut out = Vec::new();
    for variant in variants.iter().filter(|v| lemma_variants.contains(&v.name)) {
        let inst = owners.instance_of(&variant.package);
        let templates: Vec<String> = package_invariant_ops(project, inst)
            .map_err(EcExportError::from)?
            .into_iter()
            .map(|op| op.name)
            .collect();
        let module = variant
            .file
            .items
            .iter()
            .find_map(|item| match item {
                EcItem::Module(m) if m.name == variant.name => Some(m),
                _ => None,
            })
            .expect("a variant file has the variant's module");
        let ctx = VariantCtx::new(theorem, variant, module, inst, templates, owners)?;
        out.push(ctx.files()?);
    }
    Ok(out)
}

/// What every lemma file of one variant shares.
struct VariantCtx<'a> {
    theorem: &'a str,
    variant: &'a PackageVariant,
    module: &'a EcModule,
    /// `(Domino name, EasyCrypt procedure name)` of each oracle, in the package's order.
    oracles: Vec<(String, String)>,
    /// The procedures of `<V>_Imports`; empty without imports.
    imports: Vec<ProcSig>,
    /// The template operators, file order.
    templates: Vec<String>,
    /// The state record literal of the variant's state at the one memory.
    state: EcExpr,
    requires: Vec<Require>,
}

impl<'a> VariantCtx<'a> {
    fn new(
        theorem: &'a Theorem<'_>,
        variant: &'a PackageVariant,
        module: &'a EcModule,
        inst: &crate::package::PackageInstance,
        templates: Vec<String>,
        owners: &StateOwners,
    ) -> Result<VariantCtx<'a>, EcExportError> {
        let imports = module
            .params
            .first()
            .and_then(|(_, iface)| {
                variant.file.items.iter().find_map(|item| match item {
                    EcItem::ModuleType { name, procs, .. } if name == iface => Some(procs.clone()),
                    _ => None,
                })
            })
            .unwrap_or_default();
        let mut oracles = Vec::with_capacity(inst.pkg.oracles.len());
        for oracle in &inst.pkg.oracles {
            let name = &oracle.sig.name;
            oracles.push((name.clone(), Names::new().mangle(NameKind::Proc, name)?));
        }
        let mut names = Names::new();
        let mut fields = Vec::with_capacity(inst.pkg.state.len());
        for (name, _ty, _span) in &inst.pkg.state {
            let mangled = names.mangle(NameKind::Var, name)?;
            fields.push((
                super::invariant::pkg_state_field_name(&variant.package, &mangled),
                EcExpr::Qualified {
                    path: vec![variant.name.clone(), mangled],
                    mem: None,
                },
            ));
        }
        let mut requires = vec![Require {
            import: true,
            names: ["AllCore", "Distr", "FMap", "Int", "IntDiv", "Types"]
                .map(String::from)
                .to_vec(),
        }];
        // the chain includes `Pkg_<V>`; the templates are in the file of the package's owner
        let owner_file = owners.file_of(&variant.package);
        if !templates.is_empty() && owner_file != format!("Pkg_{}", variant.name) {
            requires.push(Require {
                import: true,
                names: vec![owner_file],
            });
        }
        Ok(VariantCtx {
            theorem: &theorem.name,
            variant,
            module,
            oracles,
            imports,
            templates,
            state: EcExpr::RecordLit { fields },
            requires,
        })
    }

    fn has_imports(&self) -> bool {
        !self.module.params.is_empty()
    }

    /// `<V>(I).<proc>`, or `<V>.<proc>` without imports.
    fn proc_path(&self, proc: &str) -> String {
        if self.has_imports() {
            format!("{}({IMPORTS}).{proc}", self.variant.name)
        } else {
            format!("{}.{proc}", self.variant.name)
        }
    }

    /// `PkgInv_<N1>_of_<P> {| … |} /\ …`.
    fn invariants(&self) -> EcExpr {
        EcExpr::right_chain(
            EcBinop::And,
            self.templates
                .iter()
                .map(|t| EcExpr::App {
                    head: t.clone(),
                    args: vec![self.state.clone()],
                })
                .collect(),
        )
        .expect("a variant with package lemmas has an invariant")
    }

    fn has_invariants(&self) -> bool {
        !self.templates.is_empty()
    }

    fn files(&self) -> Result<PkgInvFiles, EcExportError> {
        let v = &self.variant.name;
        let mut oracles = Vec::new();
        let mut frames = Vec::new();
        for (oracle, proc_name) in &self.oracles {
            let proc = self
                .module
                .procs
                .iter()
                .find(|p| &p.name == proc_name)
                .expect("the variant's module has a procedure for each oracle");
            if self.has_invariants() {
                oracles.push(self.oracle_file(proc, oracle));
            }
            if self.has_imports() {
                frames.push(self.frame_file(proc, oracle));
            }
        }
        let mut start = self.has_invariants().then(|| self.start_file());
        let mut prev = format!("Pkg_{v}");
        for file in oracles.iter_mut().chain(&mut frames).chain(&mut start) {
            prev = chain_onto(&mut file.file, prev, &file.file_name);
        }
        let stem = pkg_inv_stem(v);
        let mut join = EcFile {
            header: vec![format!(
                "{stem}.ec for theorem `{}`: the package lemmas of `{v}`, the theory each \
                 composition clones for an instance of `{v}` — generated by `domino easycrypt`.",
                self.theorem
            )],
            requires: vec![],
            items: vec![],
        };
        chain_onto(&mut join, prev, "");
        Ok(PkgInvFiles {
            package: self.variant.package.clone(),
            variant: v.clone(),
            join_file: format!("{stem}.ec"),
            join,
            oracles,
            frames,
            start,
        })
    }

    /// The items of a lemma file: the lemma in a section over `I` when the package has imports.
    fn lemma_items(&self, lemma: EcLemma, assumptions: Vec<SectionAssumption>) -> Vec<EcItem> {
        if !self.has_imports() {
            return vec![EcItem::Lemma(lemma)];
        }
        vec![EcItem::Section(EcSection {
            declares: vec![DeclareModule {
                name: IMPORTS.to_string(),
                module_type: self.module.params[0].1.clone(),
                restrictions: vec![self.variant.name.clone()],
            }],
            assumptions,
            items: vec![],
            lemmas: vec![lemma],
        })]
    }

    fn lemma_file(
        &self,
        stem: String,
        what: String,
        oracle: &str,
        lemma: EcLemma,
    ) -> PkgInvLemmaFile {
        self.lemma_file_with(stem, what, oracle, lemma, vec![])
    }

    fn lemma_file_with(
        &self,
        stem: String,
        what: String,
        oracle: &str,
        lemma: EcLemma,
        assumptions: Vec<SectionAssumption>,
    ) -> PkgInvLemmaFile {
        PkgInvLemmaFile {
            oracle: oracle.to_string(),
            file_name: format!("{stem}.ec"),
            file: EcFile {
                header: vec![format!(
                    "{stem}.ec for theorem `{}`: {what} — generated by `domino easycrypt`.",
                    self.theorem
                )],
                requires: self.requires.clone(),
                items: self.lemma_items(lemma, assumptions),
            },
        }
    }

    fn oracle_file(&self, proc: &EcProc, oracle: &str) -> PkgInvLemmaFile {
        let stem = format!("PkgInv_{}_{oracle}", self.variant.name);
        let lemma = EcLemma {
            name: stem.clone(),
            binders: vec![],
            statement: EcExpr::OracleHoare {
                proc: self.proc_path(&proc.name),
                pre: Box::new(self.invariants()),
                post: Box::new(unless_aborted(self.invariants())),
            },
            proof: admitted(&proc.name),
        };
        let what = format!(
            "the package-invariant lemma of oracle `{oracle}` of `{}`",
            self.variant.name
        );
        self.lemma_file(stem, what, oracle, lemma)
    }

    fn frame_file(&self, proc: &EcProc, oracle: &str) -> PkgInvLemmaFile {
        let stem = format!("Frame_{}_{oracle}", self.variant.name);
        let j = || EcExpr::App {
            head: FRAME_PRED.to_string(),
            args: vec![EcExpr::Glob(IMPORTS.to_string())],
        };
        let mut assumptions = vec![SectionAssumption::Op {
            name: FRAME_PRED.to_string(),
            ty: EcType::Fun(
                Box::new(EcType::Glob(IMPORTS.to_string())),
                Box::new(EcType::Bool),
            ),
        }];
        for import in &self.imports {
            assumptions.push(SectionAssumption::Axiom {
                name: import_axiom(&import.name),
                formula: EcExpr::OracleHoare {
                    proc: format!("{IMPORTS}.{}", import.name),
                    pre: Box::new(j()),
                    post: Box::new(unless_aborted(j())),
                },
            });
        }
        let lemma = EcLemma {
            name: stem.clone(),
            binders: vec![],
            statement: EcExpr::OracleHoare {
                proc: self.proc_path(&proc.name),
                pre: Box::new(j()),
                post: Box::new(unless_aborted(j())),
            },
            proof: frame_proof(proc),
        };
        let what = format!(
            "the frame lemma of oracle `{oracle}` of `{}`",
            self.variant.name
        );
        self.lemma_file_with(stem, what, oracle, lemma, assumptions)
    }

    fn start_file(&self) -> PkgInvLemmaFile {
        let stem = format!("PkgInv_{}_{INIT}", self.variant.name);
        let lemma = EcLemma {
            name: stem.clone(),
            binders: vec![],
            statement: EcExpr::OracleHoare {
                proc: self.proc_path(INIT),
                pre: Box::new(EcExpr::Bool(true)),
                post: Box::new(self.invariants()),
            },
            proof: admitted(INIT),
        };
        let what = format!("the start lemma of `{}`", self.variant.name);
        self.lemma_file(stem, what, INIT, lemma)
    }
}

/// Puts `file` after theory `prev` in its variant's chain: `require <prev>.` and
/// `clone include <prev>.` first. Returns the theory of `file_name`, the next file's `prev`.
fn chain_onto(file: &mut EcFile, prev: String, file_name: &str) -> String {
    file.requires.push(Require {
        import: false,
        names: vec![prev.clone()],
    });
    file.items.insert(0, EcItem::CloneInclude { base: prev });
    file_name.trim_end_matches(".ec").to_string()
}

/// The axiom of a frame lemma about import `proc`: `I_<proc>`.
pub fn import_axiom(proc: &str) -> String {
    format!("{IMPORTS}_{proc}")
}

/// `res <> None => post`.
fn unless_aborted(post: EcExpr) -> EcExpr {
    EcExpr::Binop {
        op: EcBinop::Implies,
        lhs: Box::new(EcExpr::Binop {
            op: EcBinop::Ne,
            lhs: Box::new(EcExpr::Var("res".to_string())),
            rhs: Box::new(EcExpr::None_(EcType::Unit)),
        }),
        rhs: Box::new(post),
    }
}

/// The proof of a lemma that a proof job owns: `(* <proc> *)` and `+ proc; inline. admit.`.
fn admitted(proc: &str) -> Vec<ProofLine> {
    vec![
        tactic(0, None, format!("(* {proc} *)")),
        tactic(0, Some('+'), "proc; inline. admit.".to_string()),
    ]
}

fn tactic(indent: usize, bullet: Option<char>, text: String) -> ProofLine {
    ProofLine::Tactic {
        indent,
        bullet,
        text,
    }
}

/// The structural proof of a frame lemma, forward over the procedure's body: `sp` over the
/// leading assignments, and `elim*` on what it leaves; at an import call `ecall ->> (I_<f>)`, which keeps every fact of the
/// precondition that the call cannot change and adds the axiom's post; at a branch `if.` with a
/// bullet for each arm, the statements after the branch in both; at a sampling
/// `seq 1 : (#pre)`. Statements without a call to come are closed by `auto => /#.`: the
/// package's own statements cannot write `glob I`.
pub fn frame_proof(proc: &EcProc) -> Vec<ProofLine> {
    let initialised = proc.locals.iter().filter(|(_, _, e)| e.is_some()).count();
    let stmts: Vec<&EcStmt> = proc
        .body
        .0
        .iter()
        .filter(|s| !matches!(s, EcStmt::Comment(_)))
        .collect();
    let mut lines = vec![tactic(0, None, "proc.".to_string())];
    frame_walk(&stmts, initialised, 0, &mut lines);
    lines
}

fn frame_walk(stmts: &[&EcStmt], leading: usize, indent: usize, out: &mut Vec<ProofLine>) {
    if !stmts.iter().any(|s| has_call(s)) {
        out.push(tactic(indent, None, "auto => /#.".to_string()));
        return;
    }
    let k = stmts
        .iter()
        .take_while(|s| matches!(s, EcStmt::Assign { .. }))
        .count();
    if leading + k > 0 {
        // `sp` over an assignment to a variable that the precondition reads leaves an
        // existential, and `ecall ->>` refuses that precondition: `elim*` takes it out
        out.push(tactic(
            indent,
            None,
            format!("sp {}; elim* => *.", leading + k),
        ));
    }
    let rest = &stmts[k..];
    match rest[0] {
        EcStmt::Call { proc, .. } => {
            out.push(tactic(
                indent,
                None,
                format!("ecall ->> ({}); 1: by move=> &hr /#.", import_axiom(proc)),
            ));
            frame_walk(&rest[1..], 0, indent, out);
        }
        EcStmt::If {
            then_block,
            else_block,
            ..
        } => {
            out.push(tactic(indent, None, "if.".to_string()));
            let empty = Vec::new();
            let arms = [&then_block.0, else_block.as_ref().map_or(&empty, |b| &b.0)];
            for arm in arms {
                let mut path: Vec<&EcStmt> = arm
                    .iter()
                    .filter(|s| !matches!(s, EcStmt::Comment(_)))
                    .collect();
                path.extend(&rest[1..]);
                let at = out.len();
                frame_walk(&path, 0, indent + 1, out);
                if let Some(ProofLine::Tactic {
                    bullet, indent: i, ..
                }) = out.get_mut(at)
                {
                    *bullet = Some('+');
                    *i = indent;
                }
            }
        }
        EcStmt::Sample { .. } => {
            out.push(tactic(
                indent,
                None,
                "seq 1 : (#pre); 1: by auto.".to_string(),
            ));
            frame_walk(&rest[1..], 0, indent, out);
        }
        EcStmt::Assign { .. } | EcStmt::Comment(_) => {
            unreachable!("`sp` took the assignments, and comments are filtered")
        }
    }
}

fn has_call(stmt: &EcStmt) -> bool {
    match stmt {
        EcStmt::Call { .. } => true,
        EcStmt::If {
            then_block,
            else_block,
            ..
        } => {
            then_block.0.iter().any(has_call)
                || else_block
                    .as_ref()
                    .is_some_and(|b| b.0.iter().any(has_call))
        }
        EcStmt::Assign { .. } | EcStmt::Sample { .. } | EcStmt::Comment(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::*;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::writers::easycrypt::ast::{EcBlock, EcLvalue};
    use crate::writers::easycrypt::export::export_theorem;
    use crate::writers::easycrypt::render::render_proof_lines;

    fn assign(x: &str) -> EcStmt {
        EcStmt::Assign {
            lhs: EcLvalue::Var(x.to_string()),
            rhs: EcExpr::Int(0),
        }
    }

    fn call(r: &str, proc: &str) -> EcStmt {
        EcStmt::Call {
            lhs: Some(EcLvalue::Var(r.to_string())),
            module: "O".to_string(),
            proc: proc.to_string(),
            args: vec![],
        }
    }

    fn branch(then: Vec<EcStmt>, els: Option<Vec<EcStmt>>) -> EcStmt {
        EcStmt::If {
            cond: EcExpr::Bool(true),
            then_block: EcBlock(then),
            else_block: els.map(EcBlock),
        }
    }

    #[test]
    fn the_frame_proof_follows_the_calls_and_the_branches_that_hold_them() {
        let proc = EcProc {
            name: "d_O".to_string(),
            args: vec![],
            ret: EcType::Int,
            locals: vec![],
            body: EcBlock(vec![
                assign("ec_result"),
                branch(
                    vec![
                        call("ec_r1", "d_Get"),
                        branch(vec![assign("ec_result")], None),
                    ],
                    Some(vec![assign("x")]),
                ),
                call("ec_r2", "d_Put"),
                branch(vec![assign("ec_result")], None),
            ]),
            ret_expr: None,
        };
        let text = render_proof_lines(&frame_proof(&proc));
        let expected = [
            "proc.",
            "sp 1; elim* => *.",
            "if.",
            "+ ecall ->> (I_d_Get); 1: by move=> &hr /#.",
            "  if.",
            "  + sp 1; elim* => *.",
            "    ecall ->> (I_d_Put); 1: by move=> &hr /#.",
            "    auto => /#.",
            "  + ecall ->> (I_d_Put); 1: by move=> &hr /#.",
            "    auto => /#.",
            "+ sp 1; elim* => *.",
            "  ecall ->> (I_d_Put); 1: by move=> &hr /#.",
            "  auto => /#.",
        ]
        .join("\n");
        assert_eq!(text, expected);
    }

    #[test]
    fn a_package_with_imports_gets_lemmas_over_any_imports_and_frame_lemmas() {
        let dir = PathBuf::from("test-projects/test-package-invariant-import-aborts");
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let exported = export_theorem(project.get_theorem("Proof").unwrap(), &project).unwrap();
        let [pkg] = exported.package_invariants.as_slice() else {
            panic!("one variant with package invariants");
        };
        assert_eq!((pkg.package.as_str(), pkg.variant.as_str()), ("Ctr", "Ctr"));
        let file = |name: &str| exported.files[Path::new(name)].clone();
        let lemma = file("PkgInv_Ctr_Step.ec");
        for part in [
            "declare module I <: Ctr_Imports { -Ctr }.",
            "lemma PkgInv_Ctr_Step : hoare[Ctr(I).d_Step :",
            "==> res <> None => PkgInv_nonneg_of_Ctr {| Ctr_ctr = Ctr.ctr |}]",
            "(* d_Step *)\n+ proc; inline. admit.",
        ] {
            assert!(lemma.contains(part), "{part} in:\n{lemma}");
        }
        let frame = file("Frame_Ctr_Step.ec");
        for part in [
            "declare op J : (glob I) -> bool.",
            "declare axiom I_d_Get : hoare[I.d_Get :",
            "==> res <> None => J (glob I)].",
            "ecall ->> (I_d_Get)",
        ] {
            assert!(frame.contains(part), "{part} in:\n{frame}");
        }
        assert!(file("PkgInv_Ctr_init.ec").contains("hoare[Ctr(I).init :"));
        // story 77: one chain of theories, from `Pkg_Ctr` to the join
        for (name, prev) in [
            ("PkgInv_Ctr_Step.ec", "Pkg_Ctr"),
            ("Frame_Ctr_Step.ec", "PkgInv_Ctr_Step"),
            ("PkgInv_Ctr_init.ec", "Frame_Ctr_Step"),
            ("PkgInv_Ctr.ec", "PkgInv_Ctr_init"),
        ] {
            let text = file(name);
            assert!(
                text.contains(&format!("require {prev}.\n\nclone include {prev}.")),
                "{name}:\n{text}"
            );
        }
    }

    /// Story 77: a package without package invariants that calls one with them through its
    /// imports gets frame lemmas, and no package-invariant or start lemma.
    #[test]
    fn a_caller_of_a_package_with_invariants_gets_frame_lemmas_only() {
        let dir = PathBuf::from("example-projects/4WHS");
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let exported = export_theorem(project.get_theorem("Full4WHS").unwrap(), &project).unwrap();
        let kx = exported
            .package_invariants
            .iter()
            .find(|p| p.variant == "KX_noprfkey")
            .expect("KX calls PRF");
        assert!(kx.oracle_files.is_empty() && kx.start_file.is_none());
        assert_eq!(kx.frame_files.len(), 11);
        // `Nonces` has neither invariants nor imports
        assert!(!exported
            .package_invariants
            .iter()
            .any(|p| p.package == "Nonces"));
        let comp = &exported.files[Path::new("Comp_H6.ec")];
        for clone in [
            "clone PkgInv_PRF as Cloned_Pkg_PRF.",
            "clone Pkg_Nonces as Cloned_Pkg_Nonces.",
            "clone PkgInv_KX_noprfkey as Cloned_Pkg_KX.",
        ] {
            assert!(comp.contains(clone), "{clone} in:\n{comp}");
        }
    }

    #[test]
    fn a_package_without_imports_gets_no_section_and_no_frame_lemma() {
        let dir = PathBuf::from("example-projects/4WHS");
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let exported = export_theorem(project.get_theorem("Full4WHS").unwrap(), &project).unwrap();
        let prf = exported
            .package_invariants
            .iter()
            .find(|p| p.package == "PRF")
            .expect("PRF has a package invariant");
        assert!(prf.frame_files.is_empty());
        let lemma = &exported.files[Path::new("PkgInv_PRF_Eval.ec")];
        assert!(!lemma.contains("section"), "{lemma}");
        assert!(lemma.contains("hoare[PRF.d_Eval :"), "{lemma}");
    }
}
