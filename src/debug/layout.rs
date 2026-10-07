// SPDX-License-Identifier: MIT OR Apache-2.0

//! Where a debug run writes its files (story 19 §4.6).
//!
//! The two Domino strategies write into the **same** directory and coexist, so every
//! artifact that both would write carries its strategy in its name:
//!
//! ```text
//! <oracle>/!all-claims!/
//!     inlined.txt                 shared: both lower the same Domino listing
//!     sequential_viewer.html   sequential_trace.json   sequential_summary.txt
//!     lockstep_viewer.html     lockstep_trace.json     lockstep_summary.txt
//!     sequential/  { smt/, models/, transcript.smt2 }
//!     lockstep/    { smt/, models/, transcript.smt2 }
//! ```
//!
//! The EasyCrypt listing has only one strategy, so its directory keeps the plain names
//! (`index.html`, `trace.json`, `summary.txt`, `smt/`, `models/`): nothing to disambiguate, and
//! `prove` keeps resolving `index.html` by relative href.

use std::path::{Path, PathBuf};

use crate::debug::sweep::Target;

/// The directory a Domino all-claim run writes to, in place of `<claim>`.
pub const ALL_CLAIMS_DIR: &str = "!all-claims!";

/// The `_build` subdirectory debug runs go under.
pub const DOMINO_DEBUG_DIR: &str = "_build/debug";

/// The directory of one Domino-listing run: `<root>/<theorem>/<left>-<right>/<oracle>/<claim>/`.
pub fn run_dir(root: &Path, target: &Target, claim_label: &str) -> PathBuf {
    proofstep_dir(root, &target.theorem, &target.left, &target.right)
        .join(&target.oracle)
        .join(claim_label)
}

/// The directory of one equivalence proofstep: `<root>/<theorem>/<left>-<right>/`.
pub fn proofstep_dir(root: &Path, theorem: &str, left: &str, right: &str) -> PathBuf {
    root.join(theorem).join(format!("{left}-{right}"))
}

/// How the artifact names of one run are spelled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Layout {
    /// `index.html`, `trace.json`, `summary.txt`, `smt/`, `models/`.
    Plain,
    /// `<strategy>_viewer.html`, `<strategy>_trace.json`, `<strategy>_summary.txt`,
    /// `<strategy>/smt/`, `<strategy>/models/`.
    Strategy(&'static str),
}

impl Layout {
    /// The HTML viewer.
    pub fn viewer(self) -> String {
        match self {
            Layout::Plain => "index.html".to_string(),
            Layout::Strategy(s) => format!("{s}_viewer.html"),
        }
    }

    /// The JSON trace.
    pub fn trace(self) -> String {
        match self {
            Layout::Plain => "trace.json".to_string(),
            Layout::Strategy(s) => format!("{s}_trace.json"),
        }
    }

    /// The result record (story 22): what a row of a debug index needs.
    pub fn result(self) -> String {
        match self {
            Layout::Plain => "result.json".to_string(),
            Layout::Strategy(s) => format!("{s}_result.json"),
        }
    }

    /// The text summary.
    pub fn summary(self) -> String {
        match self {
            Layout::Plain => "summary.txt".to_string(),
            Layout::Strategy(s) => format!("{s}_summary.txt"),
        }
    }

    /// `name` (a file or directory that only this strategy writes) relative to the run's
    /// output directory: `smt`, `models/J1.smt2`, `transcript.smt2`.
    pub fn rel(self, name: &str) -> String {
        match self {
            Layout::Plain => name.to_string(),
            Layout::Strategy(s) => format!("{s}/{name}"),
        }
    }

    /// [`rel`](Self::rel), resolved under `out_dir`.
    pub fn path(self, out_dir: &Path, name: &str) -> PathBuf {
        out_dir.join(self.rel(name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_run_directory_is_below_its_theorem_proofstep_and_oracle() {
        let target = Target {
            theorem: "T".into(),
            proofstep: 3,
            left: "L".into(),
            right: "R".into(),
            oracle: "O".into(),
        };
        assert_eq!(
            run_dir(Path::new("/x"), &target, ALL_CLAIMS_DIR),
            Path::new("/x/T/L-R/O/!all-claims!")
        );
    }

    #[test]
    fn plain_keeps_the_names_the_easycrypt_directory_has_always_had() {
        let l = Layout::Plain;
        assert_eq!(l.viewer(), "index.html");
        assert_eq!(l.trace(), "trace.json");
        assert_eq!(l.summary(), "summary.txt");
        assert_eq!(l.rel("models/J1.smt2"), "models/J1.smt2");
    }

    #[test]
    fn a_strategy_prefixes_every_name_it_owns() {
        let l = Layout::Strategy("lockstep");
        assert_eq!(l.viewer(), "lockstep_viewer.html");
        assert_eq!(l.trace(), "lockstep_trace.json");
        assert_eq!(l.summary(), "lockstep_summary.txt");
        assert_eq!(l.result(), "lockstep_result.json");
        assert_eq!(l.rel("smt"), "lockstep/smt");
        assert_eq!(
            l.path(Path::new("/o"), "transcript.smt2"),
            Path::new("/o/lockstep/transcript.smt2")
        );
    }
}
