// SPDX-License-Identifier: MIT OR Apache-2.0

//! Which claims of one theorem are established, and what they rest on.
//!
//! A base assumption is established. A derived assumption `A: G0 ~ G1` is established
//! when a hop path from `G0` to `G1` exists whose reductions all cite assumptions that
//! are already established. This is a least fixpoint, so the order of hops, claims and
//! blocks has no effect, and a derived assumption never rests on itself. Propositions
//! are checked after the fixpoint, with the same rule. Equivalence, hybrid and
//! conjecture hops are always edges; a conjecture on a path is recorded, so the result
//! is "established modulo conjecture".
//!
//! This is graph work only: no solver calls. Another theorem never establishes an
//! assumption of this one.

use std::collections::{BTreeSet, HashMap};
use std::fmt;

use crate::{
    gamehops::{
        reduction::{Assumption, AssumptionKind},
        GameHop,
    },
    parser::ast::Identifier as _,
    proof::Proof,
    theorem::GameInstance,
};

/// A proposition of a theorem: a claim that the hops must prove.
#[derive(Debug, Clone)]
pub struct Proposition {
    pub name: String,
    pub left_name: String,
    pub right_name: String,
}

/// The established assumptions of a theorem and what the theorem trusts.
#[derive(Debug, Clone, Default)]
pub struct Derivation {
    /// Every established assumption. A base assumption has depth 0; a derived one has
    /// 1 + the largest depth of the assumptions its path cites.
    depths: HashMap<String, usize>,
    /// The base assumptions, sorted.
    base: Vec<String>,
    /// The conjectures on the paths of established claims, as `left ~ right`.
    conjectures: BTreeSet<String>,
}

impl Derivation {
    /// The depth of an established assumption, or `None` if it is not established.
    pub fn depth(&self, assumption: &str) -> Option<usize> {
        self.depths.get(assumption).copied()
    }

    pub fn base_assumptions(&self) -> &[String] {
        &self.base
    }

    pub fn conjectures(&self) -> Vec<&str> {
        self.conjectures.iter().map(String::as_str).collect()
    }

    /// The one-line account of what the theorem trusts. Because an unmarked assumption is
    /// trusted, this line is the only guard against a forgotten `derived`; it must always
    /// be shown.
    pub fn summary(&self, theorem_name: &str) -> String {
        let derived_depths = || self.depths.values().copied().filter(|depth| *depth > 0);
        format!(
            "{theorem_name}: proven relative to {} base assumptions: {}; \
             {} derived assumptions established (max depth {}); modulo conjectures: {}",
            self.base.len(),
            list_or_none(self.base.iter().map(String::as_str)),
            derived_depths().count(),
            derived_depths().max().unwrap_or(0),
            list_or_none(self.conjectures.iter().map(String::as_str)),
        )
    }
}

fn list_or_none<'s>(items: impl Iterator<Item = &'s str>) -> String {
    let list = items.collect::<Vec<_>>().join(", ");
    if list.is_empty() {
        "none".to_string()
    } else {
        list
    }
}

/// A claim that is not established, with the index into the slice it came from.
#[derive(Debug, Clone)]
pub enum Failure {
    Assumption { index: usize, reason: Unestablished },
    Proposition { index: usize, reason: Unestablished },
}

/// Why a claim is not established.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Unestablished {
    /// No hop path exists, even with every reduction allowed.
    NoPath { left: String, right: String },
    /// The claim rests on itself: `assumptions` is the cycle (first and last are the same)
    /// and `reductions[i]` is the reduction by which `assumptions[i]` cites `assumptions[i + 1]`.
    Cycle {
        assumptions: Vec<String>,
        reductions: Vec<String>,
    },
    /// The path cites derived assumptions that are not established, but there is no cycle.
    Needs(Vec<String>),
}

impl fmt::Display for Unestablished {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Unestablished::NoPath { left, right } => {
                write!(f, "no path between {left} and {right}")
            }
            Unestablished::Cycle {
                assumptions,
                reductions,
            } => write!(
                f,
                "cycle {} via {}",
                assumptions.join(" -> "),
                reductions.join(", ")
            ),
            Unestablished::Needs(names) if names.len() == 1 => {
                write!(
                    f,
                    "the path needs the unestablished assumption {}",
                    names[0]
                )
            }
            Unestablished::Needs(names) => write!(
                f,
                "the path needs the unestablished assumptions {}",
                names.join(", ")
            ),
        }
    }
}

/// Establishes the derived assumptions of one theorem and proves its propositions.
///
/// On success, returns the derivation and one proof per proposition, in order. On
/// failure, returns every derived assumption and proposition that is not established,
/// not only the first.
pub fn derive<'a>(
    instances: &[GameInstance],
    hops: &[GameHop<'a>],
    assumptions: &[Assumption],
    propositions: &[Proposition],
) -> Result<(Derivation, Vec<Proof<'a>>), Vec<Failure>> {
    let search = PathSearch { instances, hops };
    let mut conjectures = BTreeSet::new();
    let depths = establish(&search, assumptions, &mut conjectures);

    let established = |cited: &str| depths.contains_key(cited);
    let mut failures = Vec::new();
    let mut proofs = Vec::new();
    for (index, proposition) in propositions.iter().enumerate() {
        match search.find(
            &established,
            &proposition.name,
            &proposition.left_name,
            &proposition.right_name,
        ) {
            Some(proof) => {
                conjectures.extend(conjecture_names(&proof));
                proofs.push(proof);
            }
            None => failures.push(Failure::Proposition {
                index,
                reason: search.explain(
                    &established,
                    &proposition.left_name,
                    &proposition.right_name,
                ),
            }),
        }
    }

    let explanations = FailedAssumptions::new(&search, &established, assumptions);
    for (index, assumption) in assumptions.iter().enumerate() {
        if !established(&assumption.name) {
            failures.push(Failure::Assumption {
                index,
                reason: explanations.explain(assumption),
            });
        }
    }

    if !failures.is_empty() {
        return Err(failures);
    }

    let mut base: Vec<String> = assumptions
        .iter()
        .filter(|a| a.kind == AssumptionKind::Base)
        .map(|a| a.name.clone())
        .collect();
    base.sort();
    Ok((
        Derivation {
            depths,
            base,
            conjectures,
        },
        proofs,
    ))
}

/// The least fixpoint: the depth of every assumption that can be established. A derived
/// assumption is tried again in each round until a round adds nothing, so the order of
/// `assumptions` has no effect. The conjectures on the paths found are added to
/// `conjectures`.
fn establish(
    search: &PathSearch,
    assumptions: &[Assumption],
    conjectures: &mut BTreeSet<String>,
) -> HashMap<String, usize> {
    let mut depths: HashMap<String, usize> = assumptions
        .iter()
        .filter(|a| a.kind == AssumptionKind::Base)
        .map(|a| (a.name.clone(), 0))
        .collect();
    loop {
        let pending: Vec<&Assumption> = assumptions
            .iter()
            .filter(|a| !depths.contains_key(&a.name))
            .collect();
        let mut changed = false;
        for assumption in pending {
            let established = |cited: &str| depths.contains_key(cited);
            let Some(proof) = search.find(
                &established,
                &assumption.name,
                &assumption.left_name,
                &assumption.right_name,
            ) else {
                continue;
            };
            // Depth uses the set at the moment of the search, which may already hold
            // assumptions established earlier in this round.
            let depth = 1 + proof
                .reductions()
                .map(|reduction| depths[reduction.assumption_name()])
                .max()
                .unwrap_or(0);
            conjectures.extend(conjecture_names(&proof));
            depths.insert(assumption.name.clone(), depth);
            changed = true;
        }
        if !changed {
            return depths;
        }
    }
}

fn conjecture_names<'p>(proof: &'p Proof) -> impl Iterator<Item = String> + 'p {
    proof
        .conjectures()
        .map(|c| format!("{} ~ {}", c.left_name().as_str(), c.right_name().as_str()))
}

/// A reduction on a path that cites an assumption that is not established.
struct Citation {
    cited: String,
    reduction: String,
}

struct PathSearch<'s, 'a> {
    instances: &'s [GameInstance],
    hops: &'s [GameHop<'a>],
}

impl<'a> PathSearch<'_, 'a> {
    /// A path from `left` to `right` whose reductions cite only assumptions for which
    /// `established` holds.
    fn find(
        &self,
        established: &dyn Fn(&str) -> bool,
        name: &str,
        left: &str,
        right: &str,
    ) -> Option<Proof<'a>> {
        Proof::try_new(
            self.instances,
            self.hops,
            |hop| {
                hop.as_reduction()
                    .is_none_or(|reduction| established(reduction.assumption_name()))
            },
            name.to_string(),
            left.to_string(),
            right.to_string(),
        )
    }

    /// The reductions that block the path from `left` to `right`: those on a path with every
    /// reduction allowed that cite an assumption that is not established. `None` if no path
    /// exists at all.
    fn blocking_citations(
        &self,
        established: &dyn Fn(&str) -> bool,
        left: &str,
        right: &str,
    ) -> Option<Vec<Citation>> {
        let proof = self.find(&|_| true, "", left, right)?;
        Some(
            proof
                .reductions()
                .filter(|reduction| !established(reduction.assumption_name()))
                .map(|reduction| Citation {
                    cited: reduction.assumption_name().to_string(),
                    reduction: format!(
                        "reduction {} ~ {} ({})",
                        reduction.left().construction_game_instance_name().as_str(),
                        reduction.right().construction_game_instance_name().as_str(),
                        reduction.assumption_name()
                    ),
                })
                .collect(),
        )
    }

    fn explain(
        &self,
        established: &dyn Fn(&str) -> bool,
        left: &str,
        right: &str,
    ) -> Unestablished {
        match self.blocking_citations(established, left, right) {
            None => no_path(left, right),
            Some(citations) => Unestablished::Needs(cited_names(&citations)),
        }
    }
}

fn no_path(left: &str, right: &str) -> Unestablished {
    Unestablished::NoPath {
        left: left.to_string(),
        right: right.to_string(),
    }
}

fn cited_names(citations: &[Citation]) -> Vec<String> {
    let names: BTreeSet<_> = citations.iter().map(|c| c.cited.clone()).collect();
    names.into_iter().collect()
}

/// The citation graph between the assumptions that are not established, for diagnostics
/// only. An edge `a -> b` means that the path of `a` needs `b`.
struct FailedAssumptions {
    /// `None` when the assumption has no path at all.
    edges: HashMap<String, Option<Vec<Citation>>>,
}

impl FailedAssumptions {
    fn new(
        search: &PathSearch,
        established: &dyn Fn(&str) -> bool,
        assumptions: &[Assumption],
    ) -> Self {
        let edges = assumptions
            .iter()
            .filter(|a| !established(&a.name))
            .map(|a| {
                let citations = search.blocking_citations(established, &a.left_name, &a.right_name);
                (a.name.clone(), citations)
            })
            .collect();
        Self { edges }
    }

    fn explain(&self, assumption: &Assumption) -> Unestablished {
        match &self.edges[&assumption.name] {
            None => no_path(&assumption.left_name, &assumption.right_name),
            Some(citations) => self
                .cycle_from(&assumption.name)
                .unwrap_or_else(|| Unestablished::Needs(cited_names(citations))),
        }
    }

    /// The first cycle that a depth-first walk from `start` finds.
    fn cycle_from(&self, start: &str) -> Option<Unestablished> {
        let mut stack: Vec<(&str, Option<&str>)> = vec![(start, None)];
        let mut visited = BTreeSet::new();
        self.walk(&mut stack, &mut visited)
    }

    /// `stack` holds the current walk: each assumption with the reduction that reached it.
    fn walk<'g>(
        &'g self,
        stack: &mut Vec<(&'g str, Option<&'g str>)>,
        visited: &mut BTreeSet<&'g str>,
    ) -> Option<Unestablished> {
        let (current, _) = *stack.last().unwrap();
        visited.insert(current);
        let citations = self.edges.get(current)?.as_ref()?;
        for citation in citations {
            let next = citation.cited.as_str();
            if let Some(position) = stack.iter().position(|(name, _)| *name == next) {
                let mut cycle: Vec<_> = stack[position..].to_vec();
                cycle.push((next, Some(&citation.reduction)));
                return Some(Unestablished::Cycle {
                    assumptions: cycle.iter().map(|(name, _)| name.to_string()).collect(),
                    reductions: cycle[1..]
                        .iter()
                        .map(|(_, reduction)| reduction.unwrap().to_string())
                        .collect(),
                });
            }
            if visited.contains(next) {
                continue;
            }
            stack.push((next, Some(&citation.reduction)));
            if let Some(cycle) = self.walk(stack, visited) {
                return Some(cycle);
            }
            stack.pop();
        }
        None
    }
}
