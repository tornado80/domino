// SPDX-License-Identifier: MIT OR Apache-2.0

//! `export_theorem` (`docs/stories/easycrypt/05-easycrypt-command.md` §3.4):
//! the one function that turns a Domino [`Theorem`] into the in-memory
//! contents of an EasyCrypt project — `Types.ec`, `Interfaces.ec`,
//! `Pkg_*.ec` (story 14 §3.6 renamed this from `Variant_*.ec`), `Comp_*.ec`
//! — plus the data `domino easycrypt`'s stdout
//! report is built from. All files land directly in the theorem's own
//! output directory, flat (story 10 §3.2: no `packages/`/`games/`
//! subdirectories). It runs [`EasyCryptTransform`] itself (story 16 §3.6
//! replaced story 05's `EquivalenceTransform`: the same pipeline with
//! `easycryptify` in place of `treeify`), so callers pass the *untransformed*
//! theorem exactly as `Project::get_theorem` returns it.
//!
//! Nothing here touches disk — [`write_files`] is the "thin wrapper" the
//! story asks for, kept separate so golden/unit tests can build an
//! [`ExportedTheorem`] without a temp directory. This is a deliberate
//! divergence from the story's own illustrative signature (§3.4:
//! `export_theorem(theorem: &Theorem, out: &Path)`) — `out` is dropped here
//! precisely *because* nothing here writes, and re-appears as
//! [`write_files`]'s own parameter instead.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::gamehops::GameHop;
use crate::project::Project;
use crate::theorem::{RandomnessType, Theorem};
use crate::transforms::theorem_transforms::EasyCryptTransform;
use crate::transforms::TheoremTransform;
use crate::types::Type;

use super::ast::{EcFile, Require};
use super::game::{compute_game_files_observed, GameFile};
use super::interfaces::{build_interfaces_file, discover_compositions, InterfacesOutput};
use super::invariant::{
    composition_items, has_side_invariants, params_record_packages, SideCtx, StateOwners,
};
use super::package::compute_package_variants_observed;
use super::pkginv::{build_pkg_inv_files, PkgInvFiles};
use super::progress::{ExportEvent, ExportObserver, ExportPhase, NopExportObserver, PhaseScope};
use super::proof::{compute_equivalence_files_observed, state_files, EquivalenceFiles};
use super::render::render_file;
use super::sideinv::{build_side_inv_files, SideInvFiles};
use super::types::func_op_name;
use super::typesfile::{build_types_file, collect_bits_types, collect_fn_consts};
use super::EcExportError;

/// One translated equivalence hop's report data (§3.2 of story 07): the
/// files it wrote, the oracle count, and the admit count — the CLI's stdout
/// report needs these without re-deriving them from `files`/re-parsing
/// rendered text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EquivalenceReport {
    /// Index of the hop in `theorem.game_hops` (`domino proofsteps`' numbering).
    pub proofstep: usize,
    pub left_name: String,
    pub right_name: String,
    pub invariants_file: String,
    /// The glue, `Eq_<L>_<R>.ec`: a translation file (story 68).
    pub proof_file: String,
    /// `(exported oracle, Eq_<L>_<R>_<O>.ec)` for each oracle lemma, in the game interface's
    /// order: the files the proof jobs own.
    pub oracle_files: Vec<(String, String)>,
    pub oracle_count: usize,
    pub admit_count: usize,
    pub oracle_set_mismatch: Option<String>,
    /// The SMT names of the state relations the invariant file translates, file order.
    pub state_relations: Vec<String>,
    /// The SMT names of the helper `define-fun`s the invariant file translates, file order.
    pub helpers: Vec<String>,
    /// The compositions of the two sides that have side invariants (story 69), by their Domino
    /// names, the left one first, each one time: the glue needs their `SideInv_<C>.ec`.
    pub side_compositions: Vec<String>,
}

/// The side-invariant files of one composition (story 69): what its side-invariant job proves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SideInvReport {
    /// The composition's name in Domino.
    pub composition: String,
    /// `SideInv_<C>.ec`, which joins the lemmas: a translation file.
    pub join_file: String,
    /// `(exported oracle, SideInv_<C>_<O>.ec)` for each oracle, in export order: the files the
    /// side-invariant job owns.
    pub oracle_files: Vec<(String, String)>,
    /// `SideInvInit_<C>.ec`, the start lemma of the game invariants, which the job owns too;
    /// `None` without game invariants (story 77).
    pub start_file: Option<String>,
    /// Whether the composition has game invariants. Without them the job walks no side tree:
    /// translation proves each `SideInv_<C>_<O>` from the package lemmas, and the job checks it.
    pub game_invariants: bool,
    /// The packages whose package lemma files the composition's lemmas use, each once: the
    /// side-invariant job does not start without them (story 77).
    pub packages: Vec<String>,
}

/// The package lemma files of one package variant (story 76): what a package-invariant job
/// proves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PkgInvReport {
    /// The package's name in Domino.
    pub package: String,
    /// The variant's module name.
    pub variant: String,
    /// `PkgInv_<V>.ec`, which joins the lemmas: a translation file.
    pub join_file: String,
    /// `(oracle, PkgInv_<V>_<O>.ec)` for each oracle of the package, in its order: the
    /// package-invariant lemmas, walked along the package tree.
    pub oracle_files: Vec<(String, String)>,
    /// `(oracle, Frame_<V>_<O>.ec)` for each oracle, when the package has imports.
    pub frame_files: Vec<(String, String)>,
    /// `PkgInv_<V>_init.ec`, the start lemma; `None` for a variant without package invariants
    /// (frame lemmas only, story 77).
    pub start_file: Option<String>,
}

/// A game hop this exporter does not translate, named with its kind and the
/// pair of game instances it connects (`GameHop::{left,right}_game_instance_name`)
/// — `domino easycrypt`'s report lists these so a missing `Eq_*.ec` (stories
/// 06/07) is never a silent gap.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkipNote {
    pub kind: &'static str,
    pub left: String,
    pub right: String,
    pub reason: &'static str,
}

/// The in-memory result of exporting one theorem (§3.4). `files` keys are
/// bare file names, flat in the theorem's own output directory (`Types.ec`,
/// `Pkg_KX.ec`, ... — story 10 §3.2: no `packages/`/`games/`
/// subdirectories); [`write_files`] joins them onto an `out` root. The
/// remaining fields are exactly the data `domino easycrypt`'s stdout report
/// (§3.3) needs, computed once here so the report never re-derives it (and
/// can never disagree with what was actually written).
#[derive(Debug, Default)]
pub struct ExportedTheorem {
    pub files: BTreeMap<PathBuf, String>,
    pub skipped: Vec<SkipNote>,
    /// `Types.ec`'s bits types, already-mangled EasyCrypt names
    /// (`bits_n`, ...), in emission order.
    pub bits_type_names: Vec<String>,
    /// `Types.ec`'s function constants, already-mangled EasyCrypt op names
    /// (`func_prf`, ...), in emission order.
    pub fn_const_names: Vec<String>,
    /// `Pkg_*.ec` variant names (unprefixed, e.g. `"KX"`), discovery
    /// order.
    pub package_variant_names: Vec<String>,
    /// `Comp_*.ec` composition names (unprefixed, e.g. `"Hybrid0"`),
    /// discovery order.
    pub game_names: Vec<String>,
    /// How many oracles, across this theorem's equivalence hops (direct or
    /// nested in a hybrid), declare an explicit `randomness: simple`/`none`
    /// mapping — a feature this epic does not translate (see
    /// [`super::EcExportError`]'s doc and `Equivalence::randomness`).
    pub randomness_mapping_oracles: usize,
    /// One entry per translated `GameHop::Equivalence`, `theorem.game_hops`
    /// order (story 07).
    pub equivalences: Vec<EquivalenceReport>,
    /// One entry per composition with side invariants, first-discovery order (story 69).
    pub side_invariants: Vec<SideInvReport>,
    /// One entry per package variant whose package has package invariants, discovery order
    /// (story 76).
    pub package_invariants: Vec<PkgInvReport>,
}

/// The kind + reason for a hop this exporter skips, or `None` for
/// [`GameHop::Equivalence`], which is exactly what §3.2 translates into
/// `Pkg_*.ec`/`Comp_*.ec`.
fn skip_kind_and_reason(hop: &GameHop<'_>) -> Option<(&'static str, &'static str)> {
    match hop {
        GameHop::Equivalence(_) => None,
        GameHop::Reduction(_) => Some(("reduction", "reductions are not translated")),
        GameHop::Hybrid(_) => Some(("hybrid", "hybrid game hops are not translated")),
        GameHop::Conjecture(_) => Some(("conjecture", "conjectures are not translated")),
    }
}

fn compute_skipped(theorem: &Theorem<'_>) -> Vec<SkipNote> {
    theorem
        .game_hops
        .iter()
        .filter_map(|hop| {
            skip_kind_and_reason(hop).map(|(kind, reason)| SkipNote {
                kind,
                left: hop.left_game_instance_name().to_string(),
                right: hop.right_game_instance_name().to_string(),
                reason,
            })
        })
        .collect()
}

/// The equivalence every [`GameHop`] variant carries or wraps, or `None` for
/// [`GameHop::Reduction`]/[`GameHop::Conjecture`], which have none.
fn hop_equivalence<'a>(
    hop: &'a GameHop<'_>,
) -> Option<&'a crate::gamehops::equivalence::Equivalence> {
    match hop {
        GameHop::Equivalence(eq) => Some(eq),
        GameHop::Hybrid(hybrid) => Some(hybrid.equivalence()),
        GameHop::Reduction(_) | GameHop::Conjecture(_) => None,
    }
}

fn count_randomness_mapping_oracles(theorem: &Theorem<'_>) -> usize {
    theorem
        .game_hops
        .iter()
        .filter_map(hop_equivalence)
        .flat_map(|eq| eq.randomness())
        .filter(|(_, randomness)| !matches!(randomness, RandomnessType::Custom))
        .count()
}

/// Builds the whole EasyCrypt project for `theorem` in memory (§3.2, §3.4).
/// Runs [`EasyCryptTransform`] itself — `theorem` is the plain,
/// untransformed `Theorem` a `Project` hands back. Never touches disk and
/// never invokes a solver (§6: "export must never invoke cvc5 or touch
/// `EquivalenceContext`"). `project` is needed to read each equivalence
/// hop's hand-written invariant file(s) (story 06/07); it must be the same
/// project `theorem` came from.
pub fn export_theorem(
    theorem: &Theorem<'_>,
    project: &impl Project,
) -> Result<ExportedTheorem, EcExportError> {
    export_theorem_observed(theorem, project, &mut NopExportObserver)
}

/// [`export_theorem`] streaming the `transform`, `types`, `packages`, `games`,
/// `invariants` and `proofs` phases to `observer` (story 21). The caller owns
/// the theorem-level events (`TheoremStarted`/`TheoremFinished`) and the
/// `write` phase. The result does not depend on the observer.
pub fn export_theorem_observed(
    theorem: &Theorem<'_>,
    project: &impl Project,
    observer: &mut dyn ExportObserver,
) -> Result<ExportedTheorem, EcExportError> {
    let skipped = compute_skipped(theorem);
    let randomness_mapping_oracles = count_randomness_mapping_oracles(theorem);

    let mut scope = PhaseScope::start(observer, ExportPhase::Transform, 1);
    scope.item(&theorem.name);
    let (theorem, auxs) = EasyCryptTransform.transform_theorem(theorem)?;
    scope.finish();

    let types: HashSet<Type> = auxs
        .iter()
        .flat_map(|(_, aux)| aux.types.iter().cloned())
        .collect();

    let mut scope = PhaseScope::start(observer, ExportPhase::Types, 2);
    scope.item("Types.ec");
    let types_file = build_types_file(&theorem, &types)?;
    let bits_type_names = collect_bits_types(&types).into_keys().collect();
    let fn_const_names = collect_fn_consts(&theorem.consts)
        .into_keys()
        .map(|name| func_op_name(&name))
        .collect();

    scope.item("Interfaces.ec");
    let interfaces_output = build_interfaces_file(&theorem)?;
    scope.finish();
    let mut package_variants = compute_package_variants_observed(&theorem, observer)?;
    let mut game_files = compute_game_files_observed(&theorem, observer)?;
    // story 69: the state types and package invariant templates go to the package files, the
    // side records and side invariants to the composition files
    let owners = StateOwners::of(&theorem)?;
    for (variant, items) in owners.package_items(&theorem, project)? {
        if let Some(v) = package_variants.iter_mut().find(|v| v.name == variant) {
            v.file.items.extend(items);
        }
    }
    add_side_invariants(
        &theorem,
        project,
        &interfaces_output,
        &owners,
        &mut game_files,
    )?;

    let pkg_files = build_pkg_inv_files(&theorem, project, &package_variants, &owners)?;
    let package_variant_names = package_variants.iter().map(|v| v.name.clone()).collect();
    let game_names = game_files.iter().map(|g| g.name.clone()).collect();

    let mut files = BTreeMap::new();
    files.insert(PathBuf::from("Types.ec"), render_file(&types_file));
    files.insert(
        PathBuf::from("Interfaces.ec"),
        render_file(&interfaces_output.file),
    );
    for variant in &package_variants {
        files.insert(
            PathBuf::from(format!("Pkg_{}.ec", variant.name)),
            render_file(&variant.file),
        );
    }
    for game in &game_files {
        files.insert(
            PathBuf::from(format!("Comp_{}.ec", game.name)),
            render_file(&game.file),
        );
    }

    let equivalence_files =
        compute_equivalence_files_observed(&theorem, project, &interfaces_output, observer)?;
    let mut equivalences = Vec::with_capacity(equivalence_files.len());
    for ef in &equivalence_files {
        files.insert(
            PathBuf::from(ef.invariants.file_name.clone()),
            render_file(&ef.invariants.file),
        );
        files.insert(
            PathBuf::from(ef.proof.file_name.clone()),
            render_file(&ef.proof.file),
        );
        equivalences.push(EquivalenceReport {
            proofstep: ef.proof.proofstep,
            left_name: ef.proof.left_name.clone(),
            right_name: ef.proof.right_name.clone(),
            invariants_file: ef.invariants.file_name.clone(),
            proof_file: ef.proof.file_name.clone(),
            oracle_files: ef
                .proof
                .oracle_files
                .iter()
                .map(|o| (o.oracle.clone(), o.file_name.clone()))
                .collect(),
            oracle_count: ef.proof.oracle_count,
            admit_count: ef.proof.admit_count,
            oracle_set_mismatch: ef.proof.oracle_set_mismatch.clone(),
            state_relations: ef.invariants.state_relations.clone(),
            helpers: ef.invariants.helpers.clone(),
            side_compositions: side_compositions(&theorem, ef),
        });
    }

    let side_files = build_side_inv_files(&theorem, project, &interfaces_output, &owners)?;
    let side_invariants = side_files
        .iter()
        .map(|f| SideInvReport {
            composition: f.composition.clone(),
            join_file: f.join_file.clone(),
            oracle_files: f
                .oracles
                .iter()
                .map(|o| (o.oracle.clone(), o.file_name.clone()))
                .collect(),
            start_file: f.start.as_ref().map(|s| s.file_name.clone()),
            game_invariants: f.game_invariants,
            packages: side_packages(&theorem, &f.composition, &pkg_files),
        })
        .collect();

    let package_invariants = pkg_files
        .iter()
        .map(|f| {
            let pairs = |files: &[super::pkginv::PkgInvLemmaFile]| {
                files
                    .iter()
                    .map(|o| (o.oracle.clone(), o.file_name.clone()))
                    .collect()
            };
            PkgInvReport {
                package: f.package.clone(),
                variant: f.variant.clone(),
                join_file: f.join_file.clone(),
                oracle_files: pairs(&f.oracles),
                frame_files: pairs(&f.frames),
                start_file: f.start.as_ref().map(|s| s.file_name.clone()),
            }
        })
        .collect();

    // after every other file: a lemma file may collide with any of them
    insert_lemma_files(
        &mut files,
        &lemma_files(&equivalence_files, &side_files, &pkg_files),
    )?;

    if let Some(file) = files
        .keys()
        .find(|rel| super::overwrite::takes_reserved_dir_name(rel))
    {
        return Err(EcExportError::ReservedFileName {
            file: file.display().to_string(),
        });
    }

    Ok(ExportedTheorem {
        files,
        skipped,
        bits_type_names,
        fn_const_names,
        package_variant_names,
        game_names,
        randomness_mapping_oracles,
        equivalences,
        side_invariants,
        package_invariants,
    })
}

/// The packages of composition `composition` that have package lemma files, each once, in the
/// order of `pkg_files`.
fn side_packages(
    theorem: &Theorem<'_>,
    composition: &str,
    pkg_files: &[PkgInvFiles],
) -> Vec<String> {
    let comp = discover_compositions(theorem)
        .into_iter()
        .find(|c| c.name == composition)
        .expect("a side-invariant report names a composition of the theorem");
    let mut out: Vec<String> = Vec::new();
    for f in pkg_files {
        if comp.pkgs.iter().any(|i| i.pkg.name == f.package) && !out.contains(&f.package) {
            out.push(f.package.clone());
        }
    }
    out
}

/// Adds what each composition with side invariants declares for them (story 69) to its file:
/// the items of [`composition_items`], and the import of the package files that declare the
/// state types they use.
fn add_side_invariants(
    theorem: &Theorem<'_>,
    project: &impl Project,
    interfaces: &InterfacesOutput,
    owners: &StateOwners,
    game_files: &mut [GameFile],
) -> Result<(), EcExportError> {
    let ctx = SideCtx {
        theorem_consts: &theorem.consts,
        project,
        params_records: params_record_packages(theorem),
    };
    for comp in discover_compositions(theorem) {
        let name = &interfaces.comp_mangled[&comp.name];
        // the first game instance of the composition, as in `discover_compositions`
        let game = theorem
            .instances
            .iter()
            .find(|g| g.game().name == comp.name)
            .expect("every composition comes from a game instance");
        let Some(items) = composition_items(game, name, &ctx)? else {
            continue;
        };
        let game = game_files
            .iter_mut()
            .find(|g| &g.name == name)
            .expect("every composition has a game file");
        let state = state_files(owners, [&comp]);
        if !state.is_empty() {
            game.file.requires.push(Require {
                import: true,
                names: state,
            });
        }
        game.file.items.extend(items);
    }
    Ok(())
}

/// The compositions of `ef`'s two sides with side invariants, by Domino name, left first,
/// each one time.
fn side_compositions(theorem: &Theorem<'_>, ef: &EquivalenceFiles) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for name in [&ef.proof.left_name, &ef.proof.right_name] {
        let comp = theorem
            .find_game_instance(name)
            .expect("an exported equivalence names game instances of its theorem")
            .game();
        if has_side_invariants(comp) && !out.contains(&comp.name) {
            out.push(comp.name.clone());
        }
    }
    out
}

/// A lemma file to add under the name rule: its name, what it is (for the error), its file.
struct LemmaFile<'a> {
    name: &'a str,
    owner: String,
    file: &'a EcFile,
}

/// Every lemma file of the export, in order: the oracle lemmas of each equivalence, then the
/// side-invariant lemmas of each composition and the file that joins them, then the package
/// lemmas of each package variant and the file that joins them.
fn lemma_files<'a>(
    equivalence_files: &'a [EquivalenceFiles],
    side_files: &'a [SideInvFiles],
    pkg_files: &'a [PkgInvFiles],
) -> Vec<LemmaFile<'a>> {
    let mut out = Vec::new();
    for ef in equivalence_files {
        let equivalence = ef.proof.file_name.trim_end_matches(".ec");
        for o in &ef.proof.oracle_files {
            out.push(LemmaFile {
                name: &o.file_name,
                owner: format!("oracle `{}` of `{equivalence}`", o.oracle),
                file: &o.file,
            });
        }
    }
    for f in side_files {
        for o in &f.oracles {
            out.push(LemmaFile {
                name: &o.file_name,
                owner: format!(
                    "the side-invariant lemma of oracle `{}` of composition `{}`",
                    o.oracle, f.composition
                ),
                file: &o.file,
            });
        }
        if let Some(start) = &f.start {
            out.push(LemmaFile {
                name: &start.file_name,
                owner: format!(
                    "the start lemma of the game invariants of composition `{}`",
                    f.composition
                ),
                file: &start.file,
            });
        }
        out.push(LemmaFile {
            name: &f.join_file,
            owner: format!(
                "the side-invariant lemmas of composition `{}`",
                f.composition
            ),
            file: &f.join,
        });
    }
    for f in pkg_files {
        for (kind, lemmas) in [
            ("package-invariant lemma", &f.oracles),
            ("frame lemma", &f.frames),
        ] {
            for o in lemmas {
                out.push(LemmaFile {
                    name: &o.file_name,
                    owner: format!(
                        "the {kind} of oracle `{}` of package variant `{}`",
                        o.oracle, f.variant
                    ),
                    file: &o.file,
                });
            }
        }
        if let Some(start) = &f.start {
            out.push(LemmaFile {
                name: &start.file_name,
                owner: format!("the start lemma of package variant `{}`", f.variant),
                file: &start.file,
            });
        }
        out.push(LemmaFile {
            name: &f.join_file,
            owner: format!("the package lemmas of package variant `{}`", f.variant),
            file: &f.join,
        });
    }
    out
}

/// Adds the lemma files to `files`, which holds every other file of the export. The **name
/// rule** (stories 68, 69): a lemma file whose name, ignoring case (the file system may), is
/// already taken, by another file of the export or by another lemma file, is
/// [`EcExportError::LemmaFileCollision`], which names both.
fn insert_lemma_files(
    files: &mut BTreeMap<PathBuf, String>,
    lemmas: &[LemmaFile<'_>],
) -> Result<(), EcExportError> {
    let mut taken: HashMap<String, String> = files
        .keys()
        .map(|rel| {
            let name = rel.display().to_string();
            (
                name.to_lowercase(),
                format!("the file `{name}` of the export"),
            )
        })
        .collect();
    for lemma in lemmas {
        if let Some(other) = taken.insert(lemma.name.to_lowercase(), lemma.owner.clone()) {
            return Err(EcExportError::LemmaFileCollision {
                file: lemma.name.to_string(),
                owner: lemma.owner.clone(),
                other,
            });
        }
        files.insert(PathBuf::from(lemma.name), render_file(lemma.file));
    }
    Ok(())
}

/// Writes every entry of `exported.files` under `out_dir`, flat (story 10
/// §3.2 — no `packages/`/`games/` subdirectories; `create_dir_all` here only
/// ever creates `out_dir` itself). The caller (`domino easycrypt`) only
/// calls this after [`export_theorem`] has returned `Ok` for *every*
/// requested theorem (§3.2: "a failed export must not leave a half-written
/// tree").
pub fn write_files(out_dir: &Path, files: &BTreeMap<PathBuf, String>) -> std::io::Result<()> {
    for (rel_path, contents) in files {
        let path = out_dir.join(rel_path);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, contents)?;
    }
    Ok(())
}

/// Writes every theorem's files (`(name, out_dir, files)`), reporting the `write`
/// phase and the closing `Finished` event (story 21). Same bytes as calling
/// [`write_files`] per theorem.
pub fn write_all_observed(
    outputs: &[(&str, &Path, &BTreeMap<PathBuf, String>)],
    observer: &mut dyn ExportObserver,
) -> std::io::Result<()> {
    let total: usize = outputs.iter().map(|(_, _, files)| files.len()).sum();
    let mut scope = PhaseScope::start(observer, ExportPhase::Write, total);
    for (name, out_dir, files) in outputs {
        for (rel_path, contents) in *files {
            scope.item(&format!("{name}/{}", rel_path.display()));
            let path = out_dir.join(rel_path);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(path, contents)?;
        }
    }
    scope.finish();
    observer.on_event(&ExportEvent::Finished {
        files_written: total,
    });
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::project::{DirectoryFiles, DirectoryProject, Project};

    use super::*;

    fn export(dir: &str, theorem_name: &str) -> Result<ExportedTheorem, EcExportError> {
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let theorem = project.get_theorem(theorem_name).unwrap();
        export_theorem(theorem, &project)
    }

    /// Writes `exported` to a scratch directory and compiles every file in
    /// dependency order (skips without `easycrypt`). `tag` only names the scratch
    /// directory.
    fn assert_tree_compiles(exported: &ExportedTheorem, tag: &str) {
        let tmp = std::env::temp_dir().join(format!(
            "domino-easycrypt-export-compile-test-{tag}-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&tmp);
        write_files(&tmp, &exported.files).unwrap();
        let base = tmp.to_str().unwrap().to_string();
        let compile = super::super::test_support::assert_compiles;
        compile(&base, &format!("{base}/Types.ec"));
        compile(&base, &format!("{base}/Interfaces.ec"));
        for name in &exported.package_variant_names {
            compile(&base, &format!("{base}/Pkg_{name}.ec"));
        }
        for name in &exported.game_names {
            compile(&base, &format!("{base}/Comp_{name}.ec"));
        }
        for side in &exported.side_invariants {
            for (_, file) in &side.oracle_files {
                compile(&base, &format!("{base}/{file}"));
            }
            compile(&base, &format!("{base}/{}", side.join_file));
        }
        for eq in &exported.equivalences {
            compile(&base, &format!("{base}/{}", eq.invariants_file));
            for (_, file) in &eq.oracle_files {
                compile(&base, &format!("{base}/{file}"));
            }
            compile(&base, &format!("{base}/{}", eq.proof_file));
        }
        std::fs::remove_dir_all(&tmp).unwrap();
    }

    // Story 20: `hello-world`'s invariant was migrated from the old
    // solver-facing `GameState_` dialect to `define-state-relation`, so the
    // project now exports (this replaces the test that pinned the failure).
    #[test]
    fn hello_world_exports_its_one_equivalence() {
        let exported = export("example-projects/hello-world", "Proof").unwrap();
        assert_eq!(exported.equivalences.len(), 1);
        let eq = &exported.equivalences[0];
        assert_eq!(eq.left_name, "medium_composition");
        assert_eq!(eq.right_name, "small_composition");
        assert_eq!(eq.oracle_count, 1);
        assert_eq!(eq.admit_count, 1);
        assert_eq!(eq.oracle_set_mismatch, None);
        let invariants = &exported.files[Path::new(&eq.invariants_file)];
        assert!(
            invariants.contains(
                "op StateRelation_invariant (l : medium_composition_state) (r : small_composition_state) : bool =\n  l.`l_pkg_rand.`Rand_ctr = r.`r_pkg_rand.`Rand_ctr."
            ),
            "{invariants}"
        );
    }

    #[test]
    fn hello_world_full_tree_compiles() {
        let exported = export("example-projects/hello-world", "Proof").unwrap();
        assert_tree_compiles(&exported, "hello-world");
    }

    #[test]
    fn simple_4whs_reports_the_reduction_hop_and_the_composition_names() {
        let exported = export("example-projects/4WHS", "Simple4WHS").unwrap();

        assert_eq!(
            exported.skipped,
            vec![SkipNote {
                kind: "reduction",
                left: "Hybrid2".to_string(),
                right: "Hybrid3".to_string(),
                reason: "reductions are not translated",
            }]
        );

        assert_eq!(
            exported.game_names,
            vec!["Hybrid0", "Hybrid1", "Hybrid2", "PRF"]
        );
        assert_eq!(exported.bits_type_names, vec!["bits_n"]);
        assert_eq!(exported.fn_const_names, vec!["func_mac", "func_prf"]);

        // Simple4WHS's three equivalences annotate several oracles with
        // `randomness: simple`/`randomness: none` — a real, hit-in-practice
        // case for the acceptance target, not a hypothetical.
        assert!(exported.randomness_mapping_oracles > 0);
    }

    #[test]
    fn simple_4whs_exports_the_same_package_variants_as_story_03() {
        let exported = export("example-projects/4WHS", "Simple4WHS").unwrap();
        let mut names = exported.package_variant_names.clone();
        names.sort();
        assert_eq!(
            names,
            vec![
                "KX",
                "KX_NoKeys",
                "KX_NoPrf",
                "PRF",
                "Prot",
                "Prot_NoKey",
                "Prot_NoPrf"
            ]
        );
    }

    // `Full4WHS`'s `theorem/full/*.smt2` invariants hit three distinct
    // gaps, all now fixed in `invariant.rs`: their `define-state-relation`
    // binders are spelled `state-left`/`state-right` instead of
    // `Simple4WHS`'s `left`/`right` (binder names are purely positional,
    // like an ordinary `define-fun`'s own argument names); at least two
    // files compare a *whole package instance's* state in one equality
    // (`(= state-left.KX state-right.KX)`, `invariant-KX-H1_0.smt2` and
    // `invariant-H1_1-H2_0.smt2` — `translate_eq_n`'s
    // `resolve_instance_atom`/`translate_instance_equality` turn that
    // into one equality of the two `<Pkg>_pkgstate` records, story 42);
    // and `invariant-H7_1_1_0-H7_1_1_1.smt2` uses `<0_n>`, the
    // SMT-text form of a fixed-width `BitsLiteral` zero/one value
    // (`src/writers/smt/expr_expr.rs`'s own `<{0|1}_{suffix}>` encoding,
    // not a placeholder — `translate_bits_literal_atom` now maps it onto
    // the same `zero_<suffix>`/`one_<suffix>` ops `Types.ec` already
    // declares for every bits type in scope). `Full4WHS` now exports with
    // no error at all.
    #[test]
    fn full_4whs_exports_without_error() {
        let exported = export("example-projects/4WHS", "Full4WHS").unwrap();
        assert!(exported.files.contains_key(Path::new("Types.ec")));
        assert!(!exported.package_variant_names.is_empty());
        assert!(!exported.game_names.is_empty());
        assert_eq!(exported.equivalences.len(), 9);
        for eq in &exported.equivalences {
            assert_eq!(eq.oracle_set_mismatch, None);
        }
    }

    // Story 20: `simple-KEM-example` (literal-width `Bits(256)`) had its two
    // invariants migrated to `define-state-relation`; both equivalences now
    // export, four oracles each, the invariant relating every state field.
    #[test]
    fn simple_kem_example_exports_its_two_equivalences() {
        let exported = export("example-projects/simple-KEM-example", "KEM_Proof").unwrap();
        assert_eq!(exported.bits_type_names, vec!["bits_256"]);
        let pairs: Vec<(&str, &str)> = exported
            .equivalences
            .iter()
            .map(|eq| (eq.left_name.as_str(), eq.right_name.as_str()))
            .collect();
        assert_eq!(
            pairs,
            vec![
                ("Prot", "H1_kem_correctness_real"),
                ("H1_kem_correctness_ideal", "H2"),
            ]
        );
        for eq in &exported.equivalences {
            assert_eq!(eq.oracle_count, 4);
            assert_eq!(eq.oracle_set_mismatch, None);
        }
        let first = &exported.files[Path::new(&exported.equivalences[0].invariants_file)];
        for field in [
            "d_SENTCTXT",
            "d_SENTKEY",
            "d_RECEIVEDCTXT",
            "d_RECEIVEDKEY",
            "d_TESTED",
        ] {
            assert!(
                first.contains(&format!(
                    "l.`l_pkg_Prot.`Prot_{field} = r.`r_pkg_Corr_reduction.`Corr_reduction_{field}"
                )),
                "{field}: {first}"
            );
        }
        assert!(
            first.contains("l.`l_pkg_Prot.`Prot_sk = r.`r_pkg_Corr_KEM.`Corr_KEM_sk"),
            "{first}"
        );
        let second = &exported.files[Path::new(&exported.equivalences[1].invariants_file)];
        assert!(
            second.contains("l.`l_pkg_Corr_reduction.`Corr_reduction_ctr = r.`r_pkg_CPA.`CPA_ctr"),
            "{second}"
        );
        assert!(
            second.contains("l.`l_pkg_Corr_KEM.`Corr_KEM_pk = r.`r_pkg_CPA.`CPA_pk"),
            "{second}"
        );
    }

    #[test]
    fn simple_kem_example_full_tree_compiles() {
        let exported = export("example-projects/simple-KEM-example", "KEM_Proof").unwrap();
        assert_tree_compiles(&exported, "simple-kem");
    }

    #[test]
    fn kem_dem_cca_ssp_exports_without_error() {
        let exported = export(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        )
        .unwrap();
        assert!(exported.files.contains_key(Path::new("Types.ec")));
        assert!(!exported.package_variant_names.is_empty());
        assert!(!exported.game_names.is_empty());

        // Its one equivalence hop (`Game_MON_CCA_PKE ~
        // Game_MOD_CCA_PKE_Real_KEM`) uses story 06's supported
        // `define-state-relation (left right)` grammar, so this is the
        // acceptance target for story 07's own "kem-dem ... also produce
        // compiling `Eq_*.ec` files" bullet (§4) — both files are present
        // and report 3 oracles/3 admits (`PKGEN`/`PKENC`/`PKDEC`).
        assert_eq!(exported.equivalences.len(), 1);
        let eq = &exported.equivalences[0];
        assert_eq!(eq.left_name, "Game_MON_CCA_PKE");
        assert_eq!(eq.right_name, "Game_MOD_CCA_PKE_Real_KEM");
        assert_eq!(eq.oracle_count, 3);
        assert_eq!(eq.admit_count, 3);
        assert_eq!(eq.oracle_set_mismatch, None);
        assert!(exported.files.contains_key(Path::new(&eq.invariants_file)));
        assert!(exported.files.contains_key(Path::new(&eq.proof_file)));

        // Story 19: the base case is one line, so the `smt` can never run on
        // the first oracle's goal when `auto => />` already closed the base.
        let proof = &exported.files[Path::new(&eq.proof_file)];
        assert!(proof
            .lines()
            .any(|l| l.trim() == "auto => />; smt(emptyE map_empty)."));
        assert!(!proof.lines().any(|l| l.trim() == "smt(emptyE map_empty)."));
    }

    #[test]
    fn yao_theorem_fails_with_a_real_miette_diagnostic() {
        // Acceptance: "point it at a project using an unsupported construct
        // ... reports a `miette` diagnostic with a span". `example-projects/
        // yao`'s `Yao` theorem hits one (confirmed empirically here, not
        // merely asserted) — `export_theorem` returns `Err`, so the CLI
        // layer never reaches `write_files` and nothing is written.
        let err = export("example-projects/yao", "Yao").unwrap_err();
        let report = format!("{:?}", miette::Report::new(err));
        assert!(!report.is_empty(), "diagnostic should render");
    }

    /// Yao's `HybridSecurity` declares the theorem constants `h`, `d` and `hplusone` in an
    /// assertion file, pins them with `(assert (= (<theorem-consts-…-h> <<theorem-consts>>) h))`,
    /// and reads them in its invariants. Each reads the parameter field bound to the constant.
    /// An import of `Sim` has an argument `r`, so the adapter's result local is `r0`.
    #[test]
    fn yao_hybrid_security_reads_declared_theorem_constants_as_parameter_fields() {
        let exported = export("example-projects/yao", "HybridSecurity").unwrap();
        let inv = &exported.files[Path::new("Eq_HybridIdeal_HybridReal1_Invariants.ec")];
        assert!(inv.contains("i < l.`l_pkg_LayeredLev_h"), "{inv}");
        let comp = &exported.files[Path::new("Comp_HybridIdeal.ec")];
        assert!(comp.contains("var r0 : unit option;"), "{comp}");
        assert_tree_compiles(&exported, "yao-hybrid");
    }

    fn export_observed(
        dir: &str,
        theorem_name: &str,
        rec: &mut super::super::progress::tests::Recorder,
    ) -> Result<ExportedTheorem, EcExportError> {
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let theorem = project.get_theorem(theorem_name).unwrap();
        export_theorem_observed(theorem, &project, rec)
    }

    // Story 21: the event stream of one theorem, phase by phase, items numbered from 1.
    #[test]
    fn observer_sees_a_well_formed_event_stream() {
        let mut rec = super::super::progress::tests::Recorder::default();
        let exported = export_observed("example-projects/hello-world", "Proof", &mut rec).unwrap();
        let events = &rec.0;

        // Phases in order, each opened once and closed before the next opens.
        let phases: Vec<&str> = events
            .iter()
            .filter_map(|e| e.strip_prefix("phase "))
            .map(|e| e.split(' ').next().unwrap())
            .collect();
        assert_eq!(
            phases,
            [
                "transform",
                "types",
                "packages",
                "games",
                "invariants",
                "proofs"
            ]
        );
        let mut open: Option<String> = None;
        let mut next_index = 0usize;
        let mut declared = 0usize;
        for ev in events {
            if let Some(rest) = ev.strip_prefix("phase ") {
                assert!(open.is_none(), "phase opened inside another: {events:?}");
                let mut it = rest.split(' ');
                open = Some(it.next().unwrap().to_string());
                declared = it.next().unwrap().parse().unwrap();
                next_index = 1;
            } else if let Some(rest) = ev.strip_prefix("item ") {
                let mut it = rest.split(' ');
                assert_eq!(Some(it.next().unwrap().to_string()), open);
                assert_eq!(it.next().unwrap().parse::<usize>().unwrap(), next_index);
                next_index += 1;
            } else if let Some(name) = ev.strip_prefix("end ") {
                assert_eq!(Some(name.to_string()), open);
                assert_eq!(
                    next_index - 1,
                    declared,
                    "{name}: item count != total_items"
                );
                open = None;
            }
        }
        assert!(open.is_none());

        // Items are the things the export produces.
        assert!(
            events.contains(&"item transform 1 Proof".to_string()),
            "{events:?}"
        );
        assert!(events.contains(&"item types 1 Types.ec".to_string()));
        assert!(events.contains(&"item types 2 Interfaces.ec".to_string()));
        for name in &exported.package_variant_names {
            assert!(
                events.iter().any(|e| e.ends_with(&format!(" Pkg_{name}"))),
                "{name}"
            );
        }
        for name in &exported.game_names {
            assert!(
                events.iter().any(|e| e.ends_with(&format!(" Comp_{name}"))),
                "{name}"
            );
        }
        let eq = &exported.equivalences[0];
        let stem = eq.proof_file.trim_end_matches(".ec");
        assert!(
            events.contains(&format!("item invariants 1 {stem}_Invariants")),
            "{events:?}"
        );
        assert!(
            events.contains(&format!("item proofs 1 {stem}")),
            "{events:?}"
        );
    }

    #[test]
    fn observing_does_not_change_the_export() {
        let mut rec = super::super::progress::tests::Recorder::default();
        let observed = export_observed("example-projects/hello-world", "Proof", &mut rec).unwrap();
        let plain = export("example-projects/hello-world", "Proof").unwrap();
        assert_eq!(observed.files, plain.files);
    }

    #[test]
    fn write_phase_names_every_file_and_ends_with_finished() {
        let exported = export("example-projects/hello-world", "Proof").unwrap();
        let tmp =
            std::env::temp_dir().join(format!("domino-ec-write-progress-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        let mut rec = super::super::progress::tests::Recorder::default();
        write_all_observed(&[("Proof", tmp.as_path(), &exported.files)], &mut rec).unwrap();
        let n = exported.files.len();
        assert_eq!(rec.0.first().unwrap(), &format!("phase write {n}"));
        assert_eq!(
            rec.0
                .iter()
                .filter(|e| e.starts_with("item write "))
                .count(),
            n
        );
        assert!(
            rec.0
                .contains(&"item write 8 Proof/Interfaces.ec".to_string()),
            "{:?}",
            rec.0
        );
        assert_eq!(rec.0[rec.0.len() - 2], "end write");
        assert_eq!(rec.0.last().unwrap(), &format!("finished {n}"));
        for (rel, contents) in &exported.files {
            assert_eq!(&std::fs::read_to_string(tmp.join(rel)).unwrap(), contents);
        }
        std::fs::remove_dir_all(&tmp).unwrap();
    }

    // Story 21 §6: when the export fails, the last event is the item that failed.
    #[test]
    fn a_failing_export_ends_on_the_failing_item() {
        let mut rec = super::super::progress::tests::Recorder::default();
        assert!(export_observed("example-projects/yao", "Yao", &mut rec).is_err());
        let last = rec.0.last().unwrap();
        assert!(
            last.starts_with("item "),
            "last event should be an item: {:?}",
            rec.0
        );
        assert!(!rec.0.iter().any(|e| e.starts_with("theorem-end")));
    }

    #[test]
    fn rendering_is_deterministic() {
        let a = export("example-projects/4WHS", "Simple4WHS").unwrap();
        let b = export("example-projects/4WHS", "Simple4WHS").unwrap();
        assert_eq!(a.files, b.files);
    }

    #[test]
    fn write_files_round_trips_and_rewriting_is_byte_identical() {
        // Not `hello-world` (see the test above pinning its known
        // pre-easycrypt invariant-format gap) — `kem-dem-cca-ssp` fully
        // exports, including its equivalence's `Eq_*.ec`/`Eq_*_Invariants.ec`.
        let exported = export(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        )
        .unwrap();
        let tmp = std::env::temp_dir().join(format!(
            "domino-easycrypt-export-test-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&tmp);

        write_files(&tmp, &exported.files).unwrap();
        let first: BTreeMap<PathBuf, String> = exported
            .files
            .keys()
            .map(|p| (p.clone(), std::fs::read_to_string(tmp.join(p)).unwrap()))
            .collect();

        write_files(&tmp, &exported.files).unwrap();
        let second: BTreeMap<PathBuf, String> = exported
            .files
            .keys()
            .map(|p| (p.clone(), std::fs::read_to_string(tmp.join(p)).unwrap()))
            .collect();

        assert_eq!(first, second);
        assert_eq!(first, exported.files);

        std::fs::remove_dir_all(&tmp).unwrap();
    }

    /// `hello-world` with every `UsefulOracle` renamed to `oracle`, in a scratch directory.
    fn hello_world_with_oracle(oracle: &str) -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        let from = Path::new("example-projects/hello-world");
        for entry in walkdir_files(from) {
            let to = dir.path().join(entry.strip_prefix(from).unwrap());
            std::fs::create_dir_all(to.parent().unwrap()).unwrap();
            // a file that is not text (`.DS_Store`) is copied as it is
            let bytes = std::fs::read(&entry).unwrap();
            match String::from_utf8(bytes) {
                Ok(text) => std::fs::write(to, text.replace("UsefulOracle", oracle)),
                Err(e) => std::fs::write(to, e.into_bytes()),
            }
            .unwrap();
        }
        dir
    }

    fn walkdir_files(dir: &Path) -> Vec<PathBuf> {
        let mut out = Vec::new();
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                out.extend(walkdir_files(&path));
            } else {
                out.push(path);
            }
        }
        out
    }

    #[test]
    fn each_oracle_has_a_lemma_file_and_the_glue_closes_it_with_conseq() {
        let exported = export("example-projects/hello-world", "Proof").unwrap();
        let eq = &exported.equivalences[0];
        let file = "Eq_medium_composition_small_composition_UsefulOracle.ec";
        assert_eq!(
            eq.oracle_files,
            vec![("UsefulOracle".to_string(), file.to_string())]
        );
        let oracle = &exported.files[Path::new(file)];
        assert!(oracle.contains(
            "lemma Eq_medium_composition_small_composition_UsefulOracle : \
             equiv[Comp_MediumComposition.Game_MediumComposition.d_UsefulOracle ~ \
             Comp_SmallComposition.Game_SmallComposition.d_UsefulOracle :\n      ={arg} /\\ inv"
        ));
        assert!(oracle.contains("==> ={res} /\\ inv"));
        assert!(oracle.contains("(* d_UsefulOracle *)\n+ proc; inline. admit.\nqed."));
        assert!(!oracle.contains("section"));
        let glue = &exported.files[Path::new(&eq.proof_file)];
        assert!(
            glue.contains("require import Eq_medium_composition_small_composition_UsefulOracle.")
        );
        assert!(glue.contains(
            "(* d_UsefulOracle *)\n+ by conseq Eq_medium_composition_small_composition_UsefulOracle => /#."
        ));
        assert!(!glue.contains("admit"));
    }

    #[test]
    fn the_name_rule_rejects_an_oracle_called_invariants_and_names_both_files() {
        let dir = hello_world_with_oracle("Invariants");
        let err = export(dir.path().to_str().unwrap(), "Proof").unwrap_err();
        assert!(
            matches!(&err, EcExportError::LemmaFileCollision { file, .. }
                if file == "Eq_medium_composition_small_composition_Invariants.ec"),
            "{err}"
        );
        let message = err.to_string();
        assert!(
            message.contains("oracle `Invariants` of `Eq_medium_composition_small_composition`"),
            "{message}"
        );
        assert!(
            message.contains(
                "the file `Eq_medium_composition_small_composition_Invariants.ec` of the export"
            ),
            "{message}"
        );
    }

    // --- full-tree compile, dependency order (skips without `easycrypt`) ---

    #[test]
    fn simple_4whs_full_tree_compiles_in_dependency_order() {
        let exported = export("example-projects/4WHS", "Simple4WHS").unwrap();
        assert_tree_compiles(&exported, "simple4whs");
    }

    // Story 58: package and game invariants on both sides, base case included.
    #[test]
    fn story58_one_sided_full_tree_compiles_in_dependency_order() {
        let exported = export("testdata/easycrypt/story58", "OneSided").unwrap();
        assert_tree_compiles(&exported, "story58");
    }

    #[test]
    fn kem_dem_cca_ssp_full_tree_compiles_in_dependency_order() {
        let exported = export(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        )
        .unwrap();
        assert_tree_compiles(&exported, "kemdem");
    }

    // `Full4WHS` is a much larger project than `Simple4WHS`/`kem-dem-cca-ssp`
    // (18 package variants, 12 games, 9 equivalence hops) — exercising it
    // here, on top of the smaller acceptance targets above, is what actually
    // found (and, once fixed, now confirms the fix for) the three real
    // `invariant.rs` gaps documented in `full_4whs_exports_without_error`'s
    // own comment.
    #[test]
    fn full_4whs_full_tree_compiles_in_dependency_order() {
        let exported = export("example-projects/4WHS", "Full4WHS").unwrap();
        assert_tree_compiles(&exported, "full4whs");
    }
}
