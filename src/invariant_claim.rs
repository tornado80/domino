// SPDX-License-Identifier: MIT OR Apache-2.0

//! `--claim` with `domino prove --package P` or `--game C` (symbolic-execution story 31): a
//! wildcard on the **declared** names of the owner's invariants (`main`, `nonce*`). The full
//! claim name (`package-invariant!<name>!<P>!`) is not part of the interface.

use miette::Diagnostic;
use thiserror::Error;
use wildcard::Wildcard;

use crate::theorem::ResolvedClaim;

/// No invariant of the owner matches the pattern. It comes before any solver work, so that a
/// run that checks zero claims never says "verified".
#[derive(Debug, Error, Diagnostic)]
#[error("no invariant of `{owner}` matches `{pattern}`")]
#[diagnostic(help("the invariants of {owner} are: {}", .declared_names.join(", ")))]
pub struct NoInvariantMatches {
    pub owner: String,
    pub pattern: String,
    pub declared_names: Vec<String>,
}

/// The declared name of an invariant claim: the part between the first two `!` of
/// `package-invariant!<name>!…` or `game-invariant!<name>!…`.
fn declared_name(claim: &ResolvedClaim) -> &str {
    claim.name().split('!').nth(1).unwrap_or_default()
}

/// The invariant claims of `owner` whose declared name matches `pattern`, in their order.
/// With no pattern, all of them. A pattern that is not a valid wildcard matches nothing.
///
/// Errors: [`NoInvariantMatches`] when the pattern matches no claim; its help lists the
/// declared names.
pub(crate) fn select(
    claims: Vec<ResolvedClaim>,
    pattern: Option<&str>,
    owner: &str,
) -> Result<Vec<ResolvedClaim>, NoInvariantMatches> {
    let Some(pattern) = pattern else {
        return Ok(claims);
    };
    select_by(claims, pattern, owner, |name| {
        Wildcard::new(pattern.as_bytes()).is_ok_and(|wildcard| wildcard.is_match(name.as_bytes()))
    })
}

/// As [`select`], but `name` is the exact declared name of one invariant: `domino debug`
/// takes an exact name, because it is also the name of the run directory (story 32).
///
/// Errors: [`NoInvariantMatches`] when no invariant has that name.
pub(crate) fn select_exact(
    claims: Vec<ResolvedClaim>,
    name: Option<&str>,
    owner: &str,
) -> Result<Vec<ResolvedClaim>, NoInvariantMatches> {
    let Some(name) = name else {
        return Ok(claims);
    };
    select_by(claims, name, owner, |declared| declared == name)
}

fn select_by(
    claims: Vec<ResolvedClaim>,
    pattern: &str,
    owner: &str,
    matches: impl Fn(&str) -> bool,
) -> Result<Vec<ResolvedClaim>, NoInvariantMatches> {
    let declared_names = claims
        .iter()
        .map(|c| declared_name(c).to_string())
        .collect();
    let selected: Vec<ResolvedClaim> = claims
        .into_iter()
        .filter(|claim| matches(declared_name(claim)))
        .collect();
    if selected.is_empty() {
        return Err(NoInvariantMatches {
            owner: owner.to_string(),
            pattern: pattern.to_string(),
            declared_names,
        });
    }
    Ok(selected)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theorem::{BuiltInFact, ClaimKind};

    fn claim(name: &str) -> ResolvedClaim {
        ResolvedClaim {
            name: name.to_string(),
            kind: ClaimKind::BuiltIn(BuiltInFact::NoAbort),
            dependencies: Vec::new(),
            admitted: false,
        }
    }

    fn names(claims: &[ResolvedClaim]) -> Vec<&str> {
        claims.iter().map(ResolvedClaim::name).collect()
    }

    fn two() -> Vec<ResolvedClaim> {
        vec![
            claim("package-invariant!main!P!"),
            claim("package-invariant!bad!P!"),
        ]
    }

    #[test]
    fn a_wildcard_matches_the_declared_name_only() {
        let selected = select(two(), Some("ma*"), "P").unwrap();
        assert_eq!(names(&selected), ["package-invariant!main!P!"]);
        // the full claim name is not the interface
        assert!(select(two(), Some("package-invariant*"), "P").is_err());
    }

    #[test]
    fn no_pattern_selects_every_claim() {
        assert_eq!(select(two(), None, "P").unwrap().len(), 2);
    }

    #[test]
    fn an_exact_name_is_not_a_wildcard() {
        let selected = select_exact(two(), Some("main"), "P").unwrap();
        assert_eq!(names(&selected), ["package-invariant!main!P!"]);
        let err = select_exact(two(), Some("ma*"), "P").unwrap_err();
        assert_eq!(err.declared_names, ["main", "bad"]);
        assert_eq!(select_exact(two(), None, "P").unwrap().len(), 2);
    }

    #[test]
    fn no_match_lists_the_declared_names() {
        let err = select(two(), Some("nope"), "P").unwrap_err();
        assert_eq!(err.to_string(), "no invariant of `P` matches `nope`");
        assert_eq!(err.declared_names, ["main", "bad"]);
    }
}
