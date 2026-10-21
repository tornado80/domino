// SPDX-License-Identifier: MIT OR Apache-2.0

//! The lemmas of a job that no tree is walked for (stories 76 and 77): the frame lemmas of a
//! package-invariant job and the side-invariant lemmas of a composition without game
//! invariants, whose proof translation writes, and the start lemmas of the package invariants
//! and of the game invariants.
//!
//! Each lemma file is sent whole to a fresh EasyCrypt, one sentence at a time: the file is
//! proved when EasyCrypt accepts every sentence, `qed.` and `end section.` included.
//!
//! - A lemma whose proof translation wrote is sent as translation wrote it. When EasyCrypt
//!   refuses a sentence, its proof becomes `admit.`, and the job says which sentence was
//!   refused.
//! - A start lemma is sent with each of [`start_proofs`] in place of its admitted proof, until
//!   one is accepted. When none is, it keeps its admitted proof, and the job names the claims
//!   it stands for: the package invariants on the state after `init`, which is the start check
//!   of the package (story 75), or the game invariants after the composition's `init`.
//!
//! The job writes each file it checked, atomically. A file EasyCrypt accepted ends with
//! [`CHECKED`], and the next job does not check it again; any other file (missing, as
//! translation wrote it, or admitted) it checks again, also when the records say every oracle
//! is done.

use std::path::Path;

use crate::easycrypt::json::Status;
use crate::easycrypt::session::{split_sentences, Want};
use crate::project::Project;
use crate::writers::easycrypt::invariant::{game_invariant_names, package_invariant_ops};
use crate::writers::easycrypt::pkginv::INIT;
use crate::writers::easycrypt::progress::{ExportEvent, ExportObserver, ExportPhase, JobProgress};
use crate::writers::easycrypt::EcExportError;
use crate::writers::smt::contexts::game_invariant_claim_name;

use super::driver::BASE_SMT_LEMMAS;
use super::oracles::EquivalenceJob;
use super::{spawn_easycrypt, with_script, write_atomically, FixedLemma, JobKind, TacticsError};

/// The proofs tried for a start lemma, in order: the quick close, then `smt` with the base
/// lemmas about maps and the project's hints (`[easycrypt] smt_hints`).
fn start_proofs(hints: &[String]) -> [String; 2] {
    let mut names: Vec<&str> = BASE_SMT_LEMMAS.to_vec();
    names.extend(hints.iter().map(String::as_str));
    [
        "+ proc; auto => /#.".to_string(),
        format!("+ proc; inline; auto => />; smt({}).", names.join(" ")),
    ]
}

/// The last line of a lemma file that EasyCrypt accepted.
const CHECKED: &str = "(* EasyCrypt accepted this file. *)\n";

/// Whether `file` is a lemma file that EasyCrypt accepted in an earlier job.
fn is_proved<P, B>(job: &EquivalenceJob<'_, P, B>, file: &str) -> bool {
    std::fs::read_to_string(job.out_dir.join(file)).is_ok_and(|text| text.ends_with(CHECKED))
}

/// The lemma files a job checks without a tree.
pub(super) struct FixedFiles<'a> {
    /// Files whose proof translation wrote complete, checked as written: the frame lemmas of the
    /// selected oracles, or the side-invariant lemmas of a composition without game invariants.
    written: Vec<&'a str>,
    /// The start lemma, when the job proves every oracle.
    start: Option<&'a str>,
    /// What the job is about: `package P` or `composition C`.
    owner: Owner<'a>,
}

#[derive(Clone, Copy)]
enum Owner<'a> {
    Package(&'a str),
    Composition(&'a str),
}

impl<'a> FixedFiles<'a> {
    /// The files `job` checks without a tree; `None` for the proof job of an equivalence.
    pub(super) fn of<P, B>(job: &EquivalenceJob<'a, P, B>) -> Option<FixedFiles<'a>> {
        let selected = |oracle: &str| job.options.oracle.as_deref().is_none_or(|o| o == oracle);
        let every = job.options.oracle.is_none();
        match job.kind {
            JobKind::Equivalence => None,
            JobKind::PackageInvariants(_) => {
                let pkg = job
                    .exported
                    .package_invariants
                    .iter()
                    .find(|p| p.join_file == job.eq.proof_file)?;
                Some(FixedFiles {
                    written: pkg
                        .frame_files
                        .iter()
                        .filter(|(o, _)| selected(o))
                        .map(|(_, f)| f.as_str())
                        .collect(),
                    start: pkg.start_file.as_deref().filter(|_| every),
                    owner: Owner::Package(&pkg.package),
                })
            }
            JobKind::SideInvariants(c) => {
                let side = job
                    .exported
                    .side_invariants
                    .iter()
                    .find(|s| s.composition == c)?;
                Some(FixedFiles {
                    written: side
                        .oracle_files
                        .iter()
                        .filter(|(o, _)| !side.game_invariants && selected(o))
                        .map(|(_, f)| f.as_str())
                        .collect(),
                    start: side.start_file.as_deref().filter(|_| every),
                    owner: Owner::Composition(&side.composition),
                })
            }
        }
    }

    fn files(&self) -> impl Iterator<Item = &'a str> + '_ {
        self.written.iter().copied().chain(self.start)
    }

    /// Whether a file that the job checks is not proved yet.
    pub(super) fn any_unproved<P, B>(&self, job: &EquivalenceJob<'_, P, B>) -> bool {
        self.files().any(|f| !is_proved(job, f))
    }
}

/// Checks the files of `fixed`: those whose proof translation wrote, then the start lemma. A
/// file that is proved already is not checked again and has no row. Stops, with what it has,
/// when the run is asked to stop.
///
/// Each file it checks is a row of `progress` (story 84, ADR 0020 point 6), named by the file
/// stem without the job's stem (`Frame_Ctr_Peek`, `init`). The row sees `ItemStarted` (`check
/// file`, or `attempt k/n` for the start lemma) and `SentenceSent` with the first line of the
/// text before each send, then `GoalFinished` (admitted or not) when the file is accepted or
/// admitted, and is dropped.
pub(super) fn prove_fixed_lemmas<P: Project, B>(
    job: &EquivalenceJob<'_, P, B>,
    fixed: &FixedFiles<'_>,
    tmp_dir: &Path,
    progress: &dyn JobProgress,
) -> Result<Vec<FixedLemma>, TacticsError> {
    let mut out = Vec::new();
    for file in fixed.files() {
        if job.options.stop_requested() {
            return Ok(out);
        }
        let admitted = if is_proved(job, file) {
            None
        } else {
            let name = row_name(job.stem(), file);
            let mut row = progress.oracle(name);
            let admitted = if fixed.start == Some(file) {
                check_start(job, fixed.owner, file, tmp_dir, row.as_mut())?
            } else {
                check_written(job, file, tmp_dir, row.as_mut())?
            };
            row.on_event(&ExportEvent::GoalFinished {
                oracle: name,
                goal: name,
                admitted: admitted.is_some(),
            });
            admitted
        };
        out.push(FixedLemma {
            file: file.to_string(),
            admitted,
        });
    }
    Ok(out)
}

/// The row name of lemma file `file` in job `stem`: the file stem without `<stem>_`
/// (`PkgInv_Ctr_init.ec` → `init`, `Frame_Ctr_Peek.ec` → `Frame_Ctr_Peek`).
fn row_name<'f>(stem: &str, file: &'f str) -> &'f str {
    let name = file.strip_suffix(".ec").unwrap_or(file);
    name.strip_prefix(stem)
        .and_then(|rest| rest.strip_prefix('_'))
        .unwrap_or(name)
}

/// Checks the lemma in `file` as translation wrote it; when EasyCrypt refuses it, its proof
/// becomes `admit.`, and the result says why.
fn check_written<P: Project, B>(
    job: &EquivalenceJob<'_, P, B>,
    file: &str,
    tmp_dir: &Path,
    row: &mut dyn ExportObserver,
) -> Result<Option<String>, TacticsError> {
    let source = job.exported_file(file)?;
    Ok(match first_accepted(job, vec![source.to_string()], row)? {
        Ok(text) => {
            write_atomically(&job.out_dir.join(file), tmp_dir, &(text + CHECKED))?;
            None
        }
        Err(refused) => {
            write_atomically(&job.out_dir.join(file), tmp_dir, &admitted_proof(source))?;
            Some(format!(
                "the proof translation wrote was refused: {refused}"
            ))
        }
    })
}

/// Checks the start lemma in `file` with each of [`start_proofs`]; when none is accepted, it
/// keeps its admitted proof, and the result names the claims it stands for.
fn check_start<P: Project, B>(
    job: &EquivalenceJob<'_, P, B>,
    owner: Owner<'_>,
    file: &str,
    tmp_dir: &Path,
    row: &mut dyn ExportObserver,
) -> Result<Option<String>, TacticsError> {
    let source = job.exported_file(file)?;
    let candidates =
        start_proofs(&job.options.smt_hints).map(|proof| with_script(source, INIT, &proof));
    Ok(match first_accepted(job, candidates.into(), row)? {
        Ok(text) => {
            write_atomically(&job.out_dir.join(file), tmp_dir, &(text + CHECKED))?;
            None
        }
        Err(refused) => {
            write_atomically(&job.out_dir.join(file), tmp_dir, source)?;
            let what = match owner {
                Owner::Package(p) => format!(
                    "{}; Domino: the start check of package {p} (story 75)",
                    start_claims(job, p)?
                ),
                Owner::Composition(c) => format!(
                    "{}; Domino: the start check of the game invariants of {c}",
                    game_start_claims(job, c)?
                ),
            };
            Some(format!("{what}; last refusal: {refused}"))
        }
    })
}

/// The first of `candidates`, whole lemma files, that a fresh EasyCrypt accepts sentence by
/// sentence; else the last refusal, as `` `<sentence>`: <message> ``. Before each candidate,
/// `row` sees `ItemStarted` and `SentenceSent` (see [`announce`]).
fn first_accepted<P, B>(
    job: &EquivalenceJob<'_, P, B>,
    candidates: Vec<String>,
    row: &mut dyn ExportObserver,
) -> Result<Result<String, String>, TacticsError> {
    let mut refused = String::from("no proof was tried");
    let total = candidates.len();
    for (k, text) in candidates.into_iter().enumerate() {
        announce(row, k + 1, total, &text);
        #[cfg(test)]
        let mut session = spawn_easycrypt(job.out_dir, job.fake.as_ref())?;
        #[cfg(not(test))]
        let mut session = spawn_easycrypt(job.out_dir)?;
        session.set_timeout(job.options.ec_timeout);
        if let Some(stop) = &job.options.stop {
            session.set_stop(stop.clone());
        }
        let mut accepted = true;
        for sentence in split_sentences(&text) {
            let response = session.send(&sentence, Want::Status)?;
            if response.status != Status::Ok {
                let msg = response
                    .error
                    .as_ref()
                    .map_or_else(|| format!("{:?}", response.status), |e| e.msg.clone());
                refused = format!("`{sentence}`: {}", msg.trim());
                accepted = false;
                break;
            }
        }
        if accepted {
            return Ok(Ok(text));
        }
    }
    Ok(Err(refused))
}

/// Tells `row` that candidate `index` of `total` is sent: `ItemStarted` named `check file` when
/// there is one candidate, else `attempt <index>/<total>`; then `SentenceSent` with the first
/// line of `text`, so the row's timer starts again.
fn announce(row: &mut dyn ExportObserver, index: usize, total: usize, text: &str) {
    let name = if total == 1 {
        "check file".to_string()
    } else {
        format!("attempt {index}/{total}")
    };
    row.on_event(&ExportEvent::ItemStarted {
        phase: ExportPhase::Tactics,
        name: &name,
        index,
    });
    row.on_event(&ExportEvent::SentenceSent {
        sentence: text.lines().next().unwrap_or(""),
    });
}

/// `source`, one lemma file, with the lemma's proof `admit.`.
fn admitted_proof(source: &str) -> String {
    let (Some(start), Some(end)) = (source.find("proof.\n"), source.rfind("\nqed.")) else {
        return source.to_string();
    };
    let start = start + "proof.\n".len();
    format!("{}admit.{}", &source[..start], &source[end..])
}

/// The claims of the start lemma of composition `comp`: each of its game invariants.
fn game_start_claims<P: Project, B>(
    job: &EquivalenceJob<'_, P, B>,
    comp: &str,
) -> Result<String, TacticsError> {
    let composition = job
        .theorem_ec
        .instances
        .iter()
        .map(|i| i.game())
        .find(|g| g.name == comp)
        .expect("the theorem uses the composition");
    let claims: Vec<String> = game_invariant_names(job.project, composition)
        .map_err(EcExportError::from)?
        .iter()
        .map(|n| game_invariant_claim_name(n, comp))
        .collect();
    Ok(format!("claims {}", claims.join(", ")))
}

/// The claims of the start lemma: each package invariant of `package`.
fn start_claims<P: Project, B>(
    job: &EquivalenceJob<'_, P, B>,
    package: &str,
) -> Result<String, TacticsError> {
    let inst = job
        .theorem_ec
        .instances
        .iter()
        .flat_map(|i| i.game().pkgs.iter())
        .find(|i| i.pkg.name == package)
        .expect("the theorem uses the package");
    let claims: Vec<String> = package_invariant_ops(job.project, inst)
        .map_err(EcExportError::from)?
        .into_iter()
        .filter_map(|op| op.claim)
        .collect();
    Ok(format!("claims {}", claims.join(", ")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::writers::easycrypt::progress::tests::Recorder;

    #[test]
    fn a_fixed_row_is_named_by_the_file_stem_without_the_job_stem() {
        assert_eq!(row_name("PkgInv_Ctr", "PkgInv_Ctr_init.ec"), "init");
        assert_eq!(
            row_name("PkgInv_Ctr", "Frame_Ctr_Peek.ec"),
            "Frame_Ctr_Peek"
        );
    }

    #[test]
    fn a_frame_file_is_one_check_and_a_start_lemma_one_item_for_each_attempt() {
        let mut frame = Recorder::default();
        announce(
            &mut frame,
            1,
            1,
            "require import AllCore.\nlemma L : true.\n",
        );
        let mut start = Recorder::default();
        announce(&mut start, 1, 2, "a.\n");
        announce(&mut start, 2, 2, "b.\n");
        assert_eq!(frame.0.len(), 2);
        assert!(frame.0[0].contains("check file"), "{:?}", frame.0);
        assert_eq!(frame.0[1], "sentence require import AllCore.");
        assert!(start.0[0].contains("attempt 1/2"), "{:?}", start.0);
        assert!(start.0[2].contains("attempt 2/2"), "{:?}", start.0);
        assert_eq!(start.0[3], "sentence b.");
    }

    #[test]
    fn an_admitted_proof_keeps_the_section_and_the_statement() {
        let source =
            "section.\nlemma L : true.\nproof.\nproc.\nauto => /#.\nqed.\n\nend section.\n";
        assert_eq!(
            admitted_proof(source),
            "section.\nlemma L : true.\nproof.\nadmit.\nqed.\n\nend section.\n"
        );
    }
}
