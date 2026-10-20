// SPDX-License-Identifier: MIT OR Apache-2.0

//! Claim kinds from declarations (story EC 72).
//!
//! A proof names claims and dependencies. Each name must be a built-in fact or a statement of the
//! parsed invariant files: a `define-state-relation`, or a `define-lemma` of the same oracle. The
//! resolution runs once, when the equivalence loads its invariant files. A name that resolves to
//! nothing, or to a helper `define-fun`, is a load error. The kind never comes from the spelling of
//! the name.

use crate::{
    gamehops::equivalence::{
        error::{Error, Result},
        smtrewrite::SmtStatementKind,
    },
    theorem::{BuiltInFact, Claim, ClaimKind, ResolvedClaim, ResolvedDependency},
    writers::smt::contexts::EquivalenceContext,
};

/// The names that the invariant files of one equivalence declare.
#[derive(Default)]
struct Declarations<'a> {
    state_relations: Vec<&'a str>,
    /// `(lemma name, oracle name)`
    lemmas: Vec<(&'a str, &'a str)>,
    helpers: Vec<&'a str>,
}

impl<'a> Declarations<'a> {
    fn from_kinds(kinds: impl IntoIterator<Item = &'a SmtStatementKind>) -> Self {
        let mut decls = Declarations::default();
        for kind in kinds {
            match kind {
                SmtStatementKind::StateRelation { name } => decls.state_relations.push(name),
                SmtStatementKind::GeneralRelation { name, oracle } => {
                    decls.lemmas.push((name, oracle))
                }
                SmtStatementKind::Function { name } => decls.helpers.push(name),
                SmtStatementKind::PackageInvariant { .. }
                | SmtStatementKind::GameInvariant { .. }
                | SmtStatementKind::Other => {}
            }
        }
        decls
    }

    fn lookup(&self, oracle: &str, name: &str) -> std::result::Result<ClaimKind, Unresolved> {
        if let Some(fact) = BuiltInFact::from_name(name) {
            return Ok(ClaimKind::BuiltIn(fact));
        }
        if self.state_relations.contains(&name) {
            return Ok(ClaimKind::StateRelation);
        }
        if self.lemmas.contains(&(name, oracle)) {
            return Ok(ClaimKind::ProjectLemma);
        }
        if self.helpers.contains(&name) {
            return Err(Unresolved::Helper);
        }
        Err(Unresolved::Undeclared {
            nearest: self.nearest(oracle, name),
        })
    }

    /// The usable name with the smallest edit distance to `name`, when the distance is small.
    fn nearest(&self, oracle: &str, name: &str) -> Option<String> {
        let candidates = BuiltInFact::ALL
            .iter()
            .map(|fact| fact.name())
            .chain(self.state_relations.iter().copied())
            .chain(
                self.lemmas
                    .iter()
                    .filter(|(_, lemma_oracle)| *lemma_oracle == oracle)
                    .map(|(lemma, _)| *lemma),
            );
        let limit = (name.chars().count() / 3).max(2);
        candidates
            .map(|candidate| (edit_distance(name, candidate), candidate))
            .filter(|(distance, _)| *distance <= limit)
            .min()
            .map(|(_, candidate)| candidate.to_string())
    }

    fn resolve_tree(
        &self,
        oracle: &str,
        tree: &[Claim],
    ) -> std::result::Result<Vec<ResolvedClaim>, (String, Unresolved)> {
        tree.iter()
            .map(|claim| {
                let kind = self
                    .lookup(oracle, claim.name())
                    .map_err(|err| (format!("claim {}", claim.name()), err))?;
                let dependencies = claim
                    .dependencies()
                    .iter()
                    .map(|dep| {
                        self.lookup(oracle, dep)
                            .map(|kind| ResolvedDependency {
                                name: dep.clone(),
                                kind,
                            })
                            .map_err(|err| {
                                (format!("dependency {dep} of claim {}", claim.name()), err)
                            })
                    })
                    .collect::<std::result::Result<_, _>>()?;
                Ok(ResolvedClaim {
                    name: claim.name().to_string(),
                    kind,
                    dependencies,
                    admitted: claim.is_admitted(),
                })
            })
            .collect()
    }
}

#[derive(Debug, PartialEq)]
enum Unresolved {
    Helper,
    Undeclared { nearest: Option<String> },
}

/// The Levenshtein distance of `a` and `b`, in characters.
fn edit_distance(a: &str, b: &str) -> usize {
    let b: Vec<char> = b.chars().collect();
    let mut row: Vec<usize> = (0..=b.len()).collect();
    for (i, ca) in a.chars().enumerate() {
        let mut diagonal = row[0];
        row[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let above = row[j + 1];
            row[j + 1] = (diagonal + usize::from(ca != *cb))
                .min(above + 1)
                .min(row[j] + 1);
            diagonal = above;
        }
    }
    row[b.len()]
}

impl EquivalenceContext<'_> {
    /// Resolves the kind of each claim and dependency of each oracle's proof tree, from the
    /// invariant files that `load_invariants` parsed. Stores the result in the context.
    ///
    /// Errors: [`Error::UndeclaredClaimName`] (with the nearest declared name when one is close)
    /// and [`Error::ClaimNamesHelper`].
    pub(crate) fn resolve_claims(&mut self) -> Result<()> {
        let equivalence = self.equivalence();
        let decls = Declarations::from_kinds(self.all_invariant_stmts().map(|stmt| &stmt.kind));
        let trees = equivalence
            .trees()
            .iter()
            .map(|(oracle, tree)| {
                let resolved = decls.resolve_tree(oracle, tree).map_err(|(role, err)| {
                    let oracle_name = oracle.clone();
                    let left_game_inst_name = equivalence.left_name().to_string();
                    let right_game_inst_name = equivalence.right_name().to_string();
                    match err {
                        Unresolved::Helper => Error::ClaimNamesHelper {
                            role,
                            oracle_name,
                            left_game_inst_name,
                            right_game_inst_name,
                        },
                        Unresolved::Undeclared { nearest } => Error::UndeclaredClaimName {
                            role,
                            oracle_name,
                            left_game_inst_name,
                            right_game_inst_name,
                            nearest,
                        },
                    }
                })?;
                Ok((oracle.clone(), resolved))
            })
            .collect::<Result<_>>()?;
        self.set_proof_trees(trees);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decls() -> Vec<SmtStatementKind> {
        vec![
            SmtStatementKind::StateRelation {
                name: "invariant".into(),
            },
            SmtStatementKind::StateRelation {
                name: "relation-keys".into(),
            },
            SmtStatementKind::GeneralRelation {
                name: "<lemma-send1>".into(),
                oracle: "Send1".into(),
            },
            SmtStatementKind::Function {
                name: "helper".into(),
            },
        ]
    }

    fn claim(name: &str, deps: &[&str]) -> Claim {
        Claim::from_tuple((
            name.to_string(),
            deps.iter().map(|d| d.to_string()).collect(),
            false,
        ))
    }

    #[test]
    fn claim_kinds_come_from_declarations() {
        let kinds = decls();
        let decls = Declarations::from_kinds(&kinds);
        for fact in BuiltInFact::ALL {
            assert_eq!(
                decls.lookup("Send1", fact.name()),
                Ok(ClaimKind::BuiltIn(fact))
            );
        }
        assert_eq!(
            decls.lookup("Send1", "invariant"),
            Ok(ClaimKind::StateRelation)
        );
        assert_eq!(
            decls.lookup("Send1", "relation-keys"),
            Ok(ClaimKind::StateRelation)
        );
        assert_eq!(
            decls.lookup("Send1", "<lemma-send1>"),
            Ok(ClaimKind::ProjectLemma)
        );
    }

    #[test]
    fn claim_misspelled_relation_is_undeclared_with_suggestion() {
        let kinds = decls();
        let decls = Declarations::from_kinds(&kinds);
        let err = decls
            .resolve_tree("Send1", &[claim("relaton-keys", &[])])
            .unwrap_err();
        assert_eq!(
            err,
            (
                "claim relaton-keys".to_string(),
                Unresolved::Undeclared {
                    nearest: Some("relation-keys".into())
                }
            )
        );
    }

    #[test]
    fn claim_naming_a_helper_is_an_error() {
        let kinds = decls();
        let decls = Declarations::from_kinds(&kinds);
        let err = decls
            .resolve_tree("Send1", &[claim("invariant", &["helper"])])
            .unwrap_err();
        assert_eq!(
            err,
            (
                "dependency helper of claim invariant".to_string(),
                Unresolved::Helper
            )
        );
    }

    #[test]
    fn claim_lemma_of_another_oracle_is_undeclared() {
        let kinds = decls();
        let decls = Declarations::from_kinds(&kinds);
        assert_eq!(
            decls.lookup("Send2", "<lemma-send1>"),
            Err(Unresolved::Undeclared { nearest: None })
        );
    }

    #[test]
    fn claim_resolves_dependencies() {
        let kinds = decls();
        let decls = Declarations::from_kinds(&kinds);
        let tree = decls
            .resolve_tree(
                "Send1",
                &[claim("invariant", &["no-abort", "<lemma-send1>"])],
            )
            .unwrap();
        assert_eq!(tree[0].kind(), ClaimKind::StateRelation);
        assert_eq!(
            tree[0]
                .dependencies()
                .iter()
                .map(|d| d.kind())
                .collect::<Vec<_>>(),
            vec![
                ClaimKind::BuiltIn(BuiltInFact::NoAbort),
                ClaimKind::ProjectLemma
            ]
        );
    }

    #[test]
    fn claim_undeclared_error_message_names_the_suggestion() {
        let err = Error::UndeclaredClaimName {
            role: "claim relaton-keys".into(),
            oracle_name: "Send1".into(),
            left_game_inst_name: "L".into(),
            right_game_inst_name: "R".into(),
            nearest: Some("relation-keys".into()),
        };
        assert_eq!(
            err.to_string(),
            "claim relaton-keys of oracle Send1 in the equivalence of L and R is not declared; \
             did you mean relation-keys?"
        );
    }

    #[test]
    fn claim_edit_distance() {
        assert_eq!(edit_distance("relaton-keys", "relation-keys"), 1);
        assert_eq!(edit_distance("", "abc"), 3);
        assert_eq!(edit_distance("kitten", "sitting"), 3);
    }
}
