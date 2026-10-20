// SPDX-License-Identifier: MIT OR Apache-2.0

//! The side-invariant lemmas of the compositions (stories 69 and 77, ADRs 0014 and 0016).
//!
//! For each composition `C` with a side invariant (a package invariant of one of its packages,
//! or a game invariant), and for each oracle `O` it exports, `SideInv_<C>_<O>.ec` holds
//!
//! ```text
//! lemma SideInv_<C>_<O> : hoare[Comp_<C>.Game_<C>.<o> : side_inv_<C> {| … |} ==> side_inv_<C> {| … |}].
//! ```
//!
//! Its proof:
//!
//! - the package invariants come from the package lemmas, bottom-up along the call graph
//!   ([`bottom_up`]); translation writes this part, and it is complete;
//! - the game invariants: `conseq` splits off `hoare[… : side_inv_<C> ==> game_inv_<C>]`, whose
//!   bullet is `+ proc; inline. admit.`, and the side-invariant job proves it along the side
//!   tree. A composition without game invariants has no such bullet.
//!
//! `SideInvInit_<C>.ec`, for a composition with game invariants, holds the start lemma of the
//! game invariants, `hoare[Game_<C>.init : true ==> game invariants]`, its proof admitted; the
//! side-invariant job proves it.
//!
//! `SideInv_<C>.ec` requires each of them, and the glue of each equivalence with a side of `C`
//! requires `SideInv_<C>.ec` and joins the lemmas with `conseq`. The lemmas say nothing about
//! the composition's parameters, so they hold for every value.

mod bottom_up;

use crate::package::Composition;
use crate::project::Project;
use crate::theorem::Theorem;

use self::bottom_up::{line, BottomUp};
use super::ast::{EcBinop, EcExpr, EcFile, EcItem, EcLemma, ProofLine, Require};
use super::game::instance_wirings;
use super::interfaces::{discover_compositions, InterfacesOutput};
use super::invariant::{
    game_inv_op_name, game_invariant_names, game_side_inv_op_name, has_side_invariants,
    pkg_side_inv_op_name, side_inv_op_name, StateOwners,
};
use super::names::{NameKind, Names};
use super::proof::{
    compute_layout, side_inv_app, side_inv_oracle_stem, side_inv_stem, state_files,
};
use super::EcExportError;

/// The side-invariant files of one composition.
pub struct SideInvFiles {
    /// The composition's name in Domino.
    pub composition: String,
    /// `SideInv_<C>.ec`, which requires each oracle's file.
    pub join_file: String,
    pub join: EcFile,
    /// One file for each exported oracle, in the composition's export order.
    pub oracles: Vec<SideInvOracleFile>,
    /// `SideInvInit_<C>.ec`, the start lemma of the game invariants; `None` without game
    /// invariants.
    pub start: Option<SideInvOracleFile>,
    /// Whether the composition has game invariants: only then does the side-invariant job walk
    /// a side tree.
    pub game_invariants: bool,
}

/// `SideInv_<C>_<O>.ec`: the side-invariant lemma of one oracle; or `SideInvInit_<C>.ec`.
pub struct SideInvOracleFile {
    /// The exported oracle's name, the `<O>` of the file name; `init` for the start lemma.
    pub oracle: String,
    pub file_name: String,
    pub file: EcFile,
}

/// The procedure of the start lemma, and the `<O>` of its [`SideInvOracleFile`].
pub const INIT: &str = "init";

/// The side-invariant files of every composition of `theorem` that has a side invariant, in
/// first-discovery order ([`discover_compositions`]).
pub fn build_side_inv_files(
    theorem: &Theorem<'_>,
    project: &impl Project,
    interfaces: &InterfacesOutput,
    owners: &StateOwners,
) -> Result<Vec<SideInvFiles>, EcExportError> {
    discover_compositions(theorem)
        .iter()
        .filter(|comp| has_side_invariants(comp))
        .map(|comp| composition_files(theorem, project, comp, interfaces, owners))
        .collect()
}

fn composition_files(
    theorem: &Theorem<'_>,
    project: &impl Project,
    comp: &Composition,
    interfaces: &InterfacesOutput,
    owners: &StateOwners,
) -> Result<SideInvFiles, EcExportError> {
    let layout = compute_layout(comp, interfaces)?;
    let inv = side_inv_app(comp, &layout, None)?
        .expect("a composition with a side invariant has `side_inv_<C>`");
    let theory = layout.comp_theory.clone();
    let c = layout.comp_mangled.clone();
    let up = BottomUp::new(
        comp,
        theory.clone(),
        instance_wirings(theorem, comp)?,
        project,
    )?;
    let game_names = game_invariant_names(project, comp).map_err(EcExportError::from)?;
    let with_head = |head: String| match &inv {
        EcExpr::App { args, .. } => EcExpr::App {
            head: format!("{theory}.{head}"),
            args: args.clone(),
        },
        other => unreachable!("`side_inv_app` is an application, not {other:?}"),
    };
    let mut requires = vec![
        Require {
            import: true,
            names: ["AllCore", "Distr", "FMap", "Int", "IntDiv", "Types"]
                .map(String::from)
                .to_vec(),
        },
        Require {
            import: false,
            names: vec![theory.clone()],
        },
    ];
    let state = state_files(owners, [comp]);
    if !state.is_empty() {
        requires.push(Require {
            import: true,
            names: state,
        });
    }
    let header = |stem: &str, what: String| {
        vec![format!(
            "{stem}.ec for theorem `{}`: {what} — generated by `domino easycrypt`.",
            theorem.name
        )]
    };

    let mut proc_names = Names::new();
    let mut oracles = Vec::with_capacity(comp.exports.len());
    for export in &comp.exports {
        let proc_name = proc_names.mangle(NameKind::Proc, export.name())?;
        let stem = side_inv_oracle_stem(&c, export.name());
        let game = format!("{theory}.Game_{c}.{proc_name}");
        let proof = if up.any_invariants() {
            let (haves, call) = up.call_of(export.to(), &export.sig().name);
            let parts = SideParts {
                game: &game,
                pre: line(&inv),
                pkg_inv: line(&with_head(pkg_side_inv_op_name(&c))),
                game_inv: line(&with_head(game_side_inv_op_name(&c))),
                unfold: format!(
                    "/{theory}.{} /{theory}.{} /{theory}.{}",
                    pkg_side_inv_op_name(&c),
                    game_side_inv_op_name(&c),
                    side_inv_op_name(&c)
                ),
            };
            bottom_up_proof(&parts, haves, &call, &proc_name, !game_names.is_empty())
        } else {
            walked(&proc_name)
        };
        let lemma = EcLemma {
            name: stem.clone(),
            binders: vec![],
            statement: EcExpr::OracleHoare {
                proc: game,
                pre: Box::new(inv.clone()),
                post: Box::new(inv.clone()),
            },
            proof,
        };
        let mut items = up.items();
        items.push(EcItem::Lemma(lemma));
        oracles.push(SideInvOracleFile {
            oracle: export.name().to_string(),
            file_name: format!("{stem}.ec"),
            file: EcFile {
                header: header(
                    &stem,
                    format!(
                        "the side-invariant lemma of `{}` of composition `{}`",
                        export.name(),
                        comp.name
                    ),
                ),
                requires: requires.clone(),
                items,
            },
        });
    }

    let start = (!game_names.is_empty()).then(|| {
        let stem = side_inv_start_stem(&c);
        let post = EcExpr::right_chain(
            EcBinop::And,
            game_names
                .iter()
                .map(|n| with_head(game_inv_op_name(n, &c)))
                .collect(),
        )
        .expect("a composition with game invariants has one");
        SideInvOracleFile {
            oracle: INIT.to_string(),
            file_name: format!("{stem}.ec"),
            file: EcFile {
                header: header(
                    &stem,
                    format!("the start lemma of the game invariants of `{}`", comp.name),
                ),
                requires: requires.clone(),
                items: vec![EcItem::Lemma(EcLemma {
                    name: stem.clone(),
                    binders: vec![],
                    statement: EcExpr::OracleHoare {
                        proc: format!("{theory}.Game_{c}.{INIT}"),
                        pre: Box::new(EcExpr::Bool(true)),
                        post: Box::new(post),
                    },
                    proof: walked(INIT),
                })],
            },
        }
    });

    let join_stem = side_inv_stem(&c);
    let names: Vec<String> = oracles
        .iter()
        .chain(&start)
        .map(|o| o.file_name.trim_end_matches(".ec").to_string())
        .collect();
    let join = EcFile {
        header: header(
            &join_stem,
            format!("the side-invariant lemmas of composition `{}`", comp.name),
        ),
        requires: if names.is_empty() {
            vec![]
        } else {
            vec![Require {
                import: false,
                names,
            }]
        },
        items: vec![],
    };
    Ok(SideInvFiles {
        composition: comp.name.clone(),
        join_file: format!("{join_stem}.ec"),
        join,
        oracles,
        start,
        game_invariants: !game_names.is_empty(),
    })
}

/// `SideInvInit_<C>`.
pub(super) fn side_inv_start_stem(comp: &str) -> String {
    format!("SideInvInit_{comp}")
}

/// The formulas of a side-invariant lemma whose package invariants come from the package
/// lemmas.
struct SideParts<'a> {
    /// `Comp_<C>.Game_<C>.<o>`.
    game: &'a str,
    /// `side_inv_<C> {| … |}`.
    pre: String,
    /// `pkg_inv_<C> {| … |}` and `game_inv_<C> {| … |}`, with game invariants.
    pkg_inv: String,
    game_inv: String,
    /// `/side_inv_<C>` and the two parts, to unfold.
    unfold: String,
}

/// The proof of a side-invariant lemma with package invariants: the lemmas of the package
/// invariants (`haves`), then the router, whose call is `call`. With game invariants the
/// package part is the lemma `pkg`, and `conseq` leaves the game part to the walked bullet.
fn bottom_up_proof(
    parts: &SideParts<'_>,
    haves: Vec<String>,
    call: &str,
    proc_name: &str,
    game_invariants: bool,
) -> Vec<ProofLine> {
    let mut lines = vec![plain(
        "(* the package invariants, from the package lemmas (ADR 0016) *)",
    )];
    lines.extend(haves.into_iter().map(|h| match h.strip_prefix("+ ") {
        Some(rest) => tactic(Some('+'), rest.to_string()),
        None => plain(&h),
    }));
    let router = [
        "proc; sp; if; 2: by auto => /#.".to_string(),
        format!("wp; {call}"),
        "by auto => /#.".to_string(),
    ];
    if !game_invariants {
        lines.extend(router.iter().map(|l| plain(l)));
        return lines;
    }
    lines.push(plain(&format!(
        "have pkg : hoare[{} : {} ==> {}].",
        parts.game, parts.pre, parts.pkg_inv
    )));
    for (i, l) in router.iter().enumerate() {
        lines.push(ProofLine::Tactic {
            indent: usize::from(i > 0),
            bullet: (i == 0).then_some('+'),
            text: l.clone(),
        });
    }
    lines.push(plain("(* the game invariants, along the side tree *)"));
    lines.push(plain(&format!(
        "conseq pkg (_: {} ==> {}).",
        parts.pre, parts.game_inv
    )));
    lines.push(tactic(Some('+'), "by move=> &hr h; split.".to_string()));
    lines.push(tactic(
        Some('+'),
        format!("by move=> &hr _ *; rewrite {} /=; smt().", parts.unfold),
    ));
    lines.extend(walked(proc_name));
    lines
}

/// `(* <proc> *)` and the bullet that a job proves along a tree.
fn walked(proc_name: &str) -> Vec<ProofLine> {
    vec![
        plain(&format!("(* {proc_name} *)")),
        tactic(Some('+'), "proc; inline. admit.".to_string()),
    ]
}

fn plain(text: &str) -> ProofLine {
    tactic(None, text.to_string())
}

fn tactic(bullet: Option<char>, text: String) -> ProofLine {
    ProofLine::Tactic {
        indent: 0,
        bullet,
        text,
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::project::{DirectoryFiles, DirectoryProject, Project};
    use crate::writers::easycrypt::export::{export_theorem, write_files};

    /// Story 77 on Full4WHS: each `SideInv_<C>_<O>` takes the package invariants from the
    /// package lemmas (`PRF` called through `KX` and `Prot` needs their frame lemmas), no
    /// composition has a game invariant, so nothing is walked; with the package lemmas
    /// admitted as translation writes them, each `SideInv_<C>.ec` compiles.
    #[test]
    fn full_4whs_side_invariants_come_from_the_package_lemmas_and_compile() {
        let dir = PathBuf::from("example-projects/4WHS");
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let exported = export_theorem(project.get_theorem("Full4WHS").unwrap(), &project).unwrap();
        assert!(!exported.side_invariants.is_empty());
        for side in &exported.side_invariants {
            assert!(!side.game_invariants, "{}", side.composition);
            for (_, file) in &side.oracle_files {
                let text = &exported.files[Path::new(file)];
                assert!(
                    text.contains("(* the package invariants, from the package lemmas"),
                    "{file}"
                );
                assert!(!text.contains("admit"), "{file}:\n{text}");
            }
        }
        let send1 = &exported.files[Path::new("SideInv_H6_Send1.ec")];
        for part in [
            "Comp_H6.Cloned_Pkg_KX.Frame_KX_noprfkey_Send1 Comp_H6.Pkg_Imports_KX J_PRF_in_KX",
            "Comp_H6.Cloned_Pkg_Prot.Frame_ProtNoKeyOnlyKid_Run1 Comp_H6.Pkg_Imports_Prot",
            "Comp_H6.Cloned_Pkg_PRF.PkgInv_PRF_Eval",
        ] {
            assert!(send1.contains(part), "{part} in:\n{send1}");
        }
        let out = tempfile::tempdir().unwrap();
        write_files(out.path(), &exported.files).unwrap();
        let base = out.path().to_str().unwrap().to_string();
        for side in &exported.side_invariants {
            super::super::test_support::assert_compiles(
                &base,
                &format!("{base}/{}", side.join_file),
            );
        }
    }
}
