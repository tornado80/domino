// SPDX-License-Identifier: MIT OR Apache-2.0

//! The lemmas of a package-invariant job that no tree is walked for (story 76): the frame
//! lemmas, whose proof translation writes, and the start lemma.
//!
//! Each lemma file is sent whole to a fresh EasyCrypt, one sentence at a time: the file is
//! proved when EasyCrypt accepts every sentence, `qed.` and `end section.` included.
//!
//! - A frame lemma is sent as translation wrote it. When EasyCrypt refuses a sentence, its
//!   proof becomes `admit.`, and the job says which sentence was refused.
//! - The start lemma is sent with each of [`start_proofs`] in place of its admitted proof, until
//!   one is accepted. When none is, it keeps its admitted proof, and the job names the claims
//!   it stands for: the package invariants on the state after `init`, which is the start check
//!   of the package (story 75).
//!
//! The job writes each file it checked, atomically. A file EasyCrypt accepted ends with
//! [`CHECKED`], and the next job does not check it again; any other file (missing, as
//! translation wrote it, or admitted) it checks again, also when the records say every oracle
//! is done.

use std::path::Path;

use crate::easycrypt::json::Status;
use crate::easycrypt::session::{split_sentences, Want};
use crate::project::Project;
use crate::writers::easycrypt::export::PkgInvReport;
use crate::writers::easycrypt::invariant::package_invariant_ops;
use crate::writers::easycrypt::pkginv::INIT;
use crate::writers::easycrypt::EcExportError;

use super::driver::BASE_SMT_LEMMAS;
use super::oracles::EquivalenceJob;
use super::{spawn_easycrypt, with_script, write_atomically, FixedLemma, TacticsError};

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

/// The frame files of the oracles the job proves, then, when it proves every oracle, the start
/// file of `pkg`.
fn selected_files<'a, P, B>(job: &EquivalenceJob<'_, P, B>, pkg: &'a PkgInvReport) -> Vec<&'a str> {
    let selected = |oracle: &str| job.options.oracle.as_deref().is_none_or(|o| o == oracle);
    let frames = pkg.frame_files.iter().filter(|(o, _)| selected(o));
    let start = job.options.oracle.is_none().then_some(&pkg.start_file);
    frames
        .map(|(_, f)| f.as_str())
        .chain(start.map(String::as_str))
        .collect()
}

/// Whether a frame or start lemma that the job checks is not proved yet.
pub(super) fn any_unproved<P, B>(job: &EquivalenceJob<'_, P, B>, pkg: &PkgInvReport) -> bool {
    selected_files(job, pkg).iter().any(|f| !is_proved(job, f))
}

/// Checks the frame lemmas of the oracles the job proves, then, when it proves every oracle,
/// the start lemma of `pkg`. A file that is proved already is not checked again. Stops, with
/// what it has, when the run is asked to stop.
pub(super) fn prove_fixed_lemmas<P: Project, B>(
    job: &EquivalenceJob<'_, P, B>,
    pkg: &PkgInvReport,
    tmp_dir: &Path,
) -> Result<Vec<FixedLemma>, TacticsError> {
    let mut out = Vec::new();
    for file in selected_files(job, pkg) {
        if job.options.stop_requested() {
            return Ok(out);
        }
        let admitted = if is_proved(job, file) {
            None
        } else if file == pkg.start_file {
            check_start(job, pkg, tmp_dir)?
        } else {
            check_frame(job, file, tmp_dir)?
        };
        out.push(FixedLemma {
            file: file.to_string(),
            admitted,
        });
    }
    Ok(out)
}

/// Checks the frame lemma in `file` as translation wrote it; when EasyCrypt refuses it, its
/// proof becomes `admit.`, and the result says why.
fn check_frame<P: Project, B>(
    job: &EquivalenceJob<'_, P, B>,
    file: &str,
    tmp_dir: &Path,
) -> Result<Option<String>, TacticsError> {
    let source = job.exported_file(file)?;
    Ok(
        match first_accepted(job, std::iter::once(source.to_string()))? {
            Ok(text) => {
                write_atomically(&job.out_dir.join(file), tmp_dir, &(text + CHECKED))?;
                None
            }
            Err(refused) => {
                write_atomically(&job.out_dir.join(file), tmp_dir, &admitted_proof(source))?;
                Some(format!("the frame proof was refused: {refused}"))
            }
        },
    )
}

/// Checks the start lemma of `pkg` with each of [`start_proofs`]; when none is accepted, it
/// keeps its admitted proof, and the result names the claims it stands for.
fn check_start<P: Project, B>(
    job: &EquivalenceJob<'_, P, B>,
    pkg: &PkgInvReport,
    tmp_dir: &Path,
) -> Result<Option<String>, TacticsError> {
    let file = &pkg.start_file;
    let source = job.exported_file(file)?;
    let candidates =
        start_proofs(&job.options.smt_hints).map(|proof| with_script(source, INIT, &proof));
    Ok(match first_accepted(job, candidates.into_iter())? {
        Ok(text) => {
            write_atomically(&job.out_dir.join(file), tmp_dir, &(text + CHECKED))?;
            None
        }
        Err(refused) => {
            write_atomically(&job.out_dir.join(file), tmp_dir, source)?;
            Some(format!(
                "{}; Domino: the start check of package {} (story 75); last refusal: {refused}",
                start_claims(job, &pkg.package)?,
                pkg.package
            ))
        }
    })
}

/// The first of `candidates`, whole lemma files, that a fresh EasyCrypt accepts sentence by
/// sentence; else the last refusal, as `` `<sentence>`: <message> ``.
fn first_accepted<P, B>(
    job: &EquivalenceJob<'_, P, B>,
    candidates: impl Iterator<Item = String>,
) -> Result<Result<String, String>, TacticsError> {
    let mut refused = String::from("no proof was tried");
    for text in candidates {
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

/// `source`, one lemma file, with the lemma's proof `admit.`.
fn admitted_proof(source: &str) -> String {
    let (Some(start), Some(end)) = (source.find("proof.\n"), source.rfind("\nqed.")) else {
        return source.to_string();
    };
    let start = start + "proof.\n".len();
    format!("{}admit.{}", &source[..start], &source[end..])
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
