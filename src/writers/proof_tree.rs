// SPDX-License-Identifier: MIT OR Apache-2.0

//! The proof tree view of the `domino html` page.
//!
//! A proposition's path cites assumptions by its reductions. A cited assumption
//! is itself proved when it is `derived` (by the path that establishes it, see
//! [`Derivation::proof_of`]) or when a proposition of the theorem proves its
//! two games. Following these citations from the propositions gives a graph of
//! claims ([`ClaimGraph`]); the page draws it once per root, as a layered DAG
//! in inline SVG ([`render`]). Each edge `parent -> child` carries the indices
//! of the reductions on the parent's path that cite the child, so the parent's
//! advantage is bounded by the sum over the edges, and the root's by the leaves
//! with their multiplicities ([`bound`]).
//!
//! A base assumption that a proposition proves is drawn expanded, but the tool
//! still trusts it: only `derived` makes the tool check that the expansion is
//! well-founded. The tree shows a citation cycle as a dashed back edge.
//!
//! [`Derivation::proof_of`]: crate::derivation::Derivation::proof_of

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;

use crate::gamehops::reduction::{Assumption, AssumptionKind};
use crate::gamehops::GameHop;
use crate::parser::ast::Identifier as _;
use crate::proof::Proof;
use crate::theorem::Theorem;

use super::html::esc;

/// What a node of the proof tree stands for.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ClaimKind {
    /// A proposition, drawn as a root.
    Proposition,
    /// A derived assumption, expanded by the path that establishes it.
    Derived,
    /// A base assumption whose two games a proposition proves, expanded by that
    /// proposition's path. The tool still trusts it.
    ProvedByProposition,
    /// A base assumption that nothing in the theorem proves: a leaf.
    Base,
    /// A conjecture hop on a path: a leaf.
    Conjecture,
}

impl ClaimKind {
    fn class(self) -> &'static str {
        match self {
            ClaimKind::Proposition => "k-prop",
            ClaimKind::Derived => "k-derived",
            ClaimKind::ProvedByProposition => "k-proved",
            ClaimKind::Base => "k-base",
            ClaimKind::Conjecture => "k-conj",
        }
    }
}

/// One node of the proof tree.
#[derive(Debug)]
pub(crate) struct Claim {
    pub(crate) name: String,
    pub(crate) left: String,
    pub(crate) right: String,
    pub(crate) kind: ClaimKind,
    /// The page view with the path that proves the claim (`p:<proposition>` or
    /// `a:<assumption>`); `None` for a leaf.
    pub(crate) view: Option<String>,
    /// The proposition that proves a [`ClaimKind::ProvedByProposition`].
    pub(crate) proved_by: Option<String>,
    /// The derivation depth of a derived assumption.
    pub(crate) depth: Option<usize>,
    /// The claims the path cites, in path order (one entry per citation).
    pub(crate) cites: Vec<Citation>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Citation {
    pub(crate) claim: usize,
    /// The hybrid hop whose reduction cites the claim once per loop step.
    pub(crate) hybrid: Option<String>,
}

/// The claims of a theorem and how they cite each other.
#[derive(Debug)]
pub(crate) struct ClaimGraph {
    pub(crate) claims: Vec<Claim>,
    /// The claims nothing else cites, in file order: propositions first, then
    /// derived assumptions. Claims only reachable through a cycle are roots too.
    pub(crate) roots: Vec<usize>,
}

/// The claim graph of `theorem`; `derived` holds the establishing path of each
/// derived assumption, by name.
pub(crate) fn claim_graph(theorem: &Theorem, derived: &BTreeMap<String, Proof>) -> ClaimGraph {
    let mut builder = Builder {
        theorem,
        derived,
        claims: Vec::new(),
        ids: HashMap::new(),
    };
    let propositions: Vec<usize> = theorem
        .proofs
        .iter()
        .map(|proof| builder.proposition(proof))
        .collect();
    let derived_claims: Vec<usize> = theorem
        .assumptions
        .iter()
        .filter(|a| a.kind == AssumptionKind::Derived)
        .map(|a| builder.assumption(&a.name))
        .collect();
    let claims = builder.claims;

    let mut cited = vec![false; claims.len()];
    for claim in &claims {
        for citation in &claim.cites {
            cited[citation.claim] = true;
        }
    }
    // A proposition is drawn under the assumption it proves when that one is cited.
    let absorbed = |p: usize| {
        claims.iter().enumerate().any(|(c, claim)| {
            cited[c] && claim.proved_by.as_deref() == Some(claims[p].name.as_str())
        })
    };
    let mut roots: Vec<usize> = propositions
        .iter()
        .copied()
        .filter(|&p| !absorbed(p))
        .chain(derived_claims.iter().copied().filter(|&a| !cited[a]))
        .collect();

    // A claim that only a cycle reaches would be lost: make it a root too.
    let mut graph = ClaimGraph {
        claims,
        roots: Vec::new(),
    };
    for candidate in propositions.into_iter().chain(derived_claims) {
        let reached = graph.reachable(&roots);
        let shown = |c: usize| {
            reached[c]
                || graph.claims.iter().enumerate().any(|(a, claim)| {
                    reached[a] && claim.proved_by.as_deref() == Some(graph.claims[c].name.as_str())
                })
        };
        if !shown(candidate) {
            roots.push(candidate);
        }
    }
    graph.roots = roots;
    graph
}

struct Builder<'b, 't> {
    theorem: &'b Theorem<'t>,
    derived: &'b BTreeMap<String, Proof<'t>>,
    claims: Vec<Claim>,
    /// `p:<name>`, `a:<name>`, `c:<left>~<right>` -> claim index.
    ids: HashMap<String, usize>,
}

impl Builder<'_, '_> {
    /// Adds the claim, or returns it if it is there. The index is reserved
    /// before its citations are followed, so a cycle ends here.
    fn add(&mut self, key: String, claim: Claim) -> (usize, bool) {
        if let Some(&id) = self.ids.get(&key) {
            return (id, false);
        }
        let id = self.claims.len();
        self.claims.push(claim);
        self.ids.insert(key, id);
        (id, true)
    }

    fn proposition(&mut self, proof: &Proof) -> usize {
        let (id, new) = self.add(
            format!("p:{}", proof.name()),
            Claim {
                name: proof.name().to_string(),
                left: proof.left_name().to_string(),
                right: proof.right_name().to_string(),
                kind: ClaimKind::Proposition,
                view: Some(format!("p:{}", proof.name())),
                proved_by: None,
                depth: None,
                cites: Vec::new(),
            },
        );
        if new {
            self.claims[id].cites = self.cites(proof);
        }
        id
    }

    fn assumption(&mut self, name: &str) -> usize {
        let theorem = self.theorem;
        let assumption = theorem.assumptions.iter().find(|a| a.name == name);
        let derived = self.derived.get(name);
        let proposition = assumption.and_then(|a| proving_proposition(theorem, a));
        let kind = match (derived, proposition) {
            (Some(_), _) => ClaimKind::Derived,
            (None, Some(_)) => ClaimKind::ProvedByProposition,
            (None, None) => ClaimKind::Base,
        };
        let view = match (derived, proposition) {
            (Some(_), _) => Some(format!("a:{name}")),
            (None, Some(p)) => Some(format!("p:{}", p.name())),
            (None, None) => None,
        };
        let (id, new) = self.add(
            format!("a:{name}"),
            Claim {
                name: name.to_string(),
                left: assumption.map_or_else(String::new, |a| a.left_name.clone()),
                right: assumption.map_or_else(String::new, |a| a.right_name.clone()),
                kind,
                view,
                proved_by: proposition
                    .filter(|_| derived.is_none())
                    .map(|p| p.name().to_string()),
                depth: theorem.derivation.depth(name).filter(|_| derived.is_some()),
                cites: Vec::new(),
            },
        );
        if new {
            if let Some(proof) = derived.or(proposition) {
                self.claims[id].cites = self.cites(proof);
            }
        }
        id
    }

    fn conjecture(&mut self, left: &str, right: &str) -> usize {
        self.add(
            format!("c:{left}~{right}"),
            Claim {
                name: format!("conjecture {left} ~ {right}"),
                left: left.to_string(),
                right: right.to_string(),
                kind: ClaimKind::Conjecture,
                view: None,
                proved_by: None,
                depth: None,
                cites: Vec::new(),
            },
        )
        .0
    }

    /// One citation per reduction, hybrid hop and conjecture on the path.
    fn cites(&mut self, proof: &Proof) -> Vec<Citation> {
        let mut cites = Vec::new();
        for hop in proof.game_hops() {
            let (claim, hybrid) = match hop {
                GameHop::Reduction(red) => (self.assumption(red.assumption_name()), None),
                GameHop::Hybrid(hybrid) => (
                    self.assumption(hybrid.reduction().assumption_name()),
                    Some(hybrid.hybrid_name().as_str().to_string()),
                ),
                GameHop::Conjecture(conj) => (
                    self.conjecture(conj.left_name().as_str(), conj.right_name().as_str()),
                    None,
                ),
                GameHop::Equivalence(_) => continue,
            };
            cites.push(Citation { claim, hybrid });
        }
        cites
    }
}

/// The proposition that proves the two games of `assumption`, in either order.
pub(crate) fn proving_proposition<'p, 'a>(
    theorem: &'p Theorem<'a>,
    assumption: &Assumption,
) -> Option<&'p Proof<'a>> {
    let (l, r) = (
        assumption.left_name.as_str(),
        assumption.right_name.as_str(),
    );
    theorem.proofs.iter().find(|p| {
        (p.left_name(), p.right_name()) == (l, r) || (p.left_name(), p.right_name()) == (r, l)
    })
}

impl ClaimGraph {
    fn reachable(&self, roots: &[usize]) -> Vec<bool> {
        let mut seen = vec![false; self.claims.len()];
        let mut stack: Vec<usize> = roots.to_vec();
        while let Some(c) = stack.pop() {
            if std::mem::replace(&mut seen[c], true) {
                continue;
            }
            stack.extend(self.claims[c].cites.iter().map(|cite| cite.claim));
        }
        seen
    }
}

/// A coefficient of the bound: monomial (the hybrids whose loop counts
/// multiply, sorted) -> count.
type Coefficient = BTreeMap<Vec<String>, u64>;

/// The leaves under `root` with how often the bound counts each, in order of
/// first appearance, and whether a cycle was cut (then the bound is not sound).
pub(crate) fn bound(graph: &ClaimGraph, root: usize) -> (Vec<(usize, Coefficient)>, bool) {
    let mut cycle = false;
    let mut memo = HashMap::new();
    let leaves = leaves_of(graph, root, &mut Vec::new(), &mut memo, &mut cycle);
    (leaves, cycle)
}

fn leaves_of(
    graph: &ClaimGraph,
    claim: usize,
    stack: &mut Vec<usize>,
    memo: &mut HashMap<usize, Vec<(usize, Coefficient)>>,
    cycle: &mut bool,
) -> Vec<(usize, Coefficient)> {
    if let Some(leaves) = memo.get(&claim) {
        return leaves.clone();
    }
    let node = &graph.claims[claim];
    if node.view.is_none() {
        return vec![(claim, BTreeMap::from([(Vec::new(), 1)]))];
    }
    stack.push(claim);
    let mut sum: Vec<(usize, Coefficient)> = Vec::new();
    for citation in &node.cites {
        let child = if stack.contains(&citation.claim) {
            *cycle = true;
            vec![(citation.claim, BTreeMap::from([(Vec::new(), 1)]))]
        } else {
            leaves_of(graph, citation.claim, stack, memo, cycle)
        };
        for (leaf, coefficient) in child {
            let coefficient = match &citation.hybrid {
                Some(hybrid) => times_hybrid(&coefficient, hybrid),
                None => coefficient,
            };
            match sum.iter_mut().find(|(l, _)| *l == leaf) {
                Some((_, total)) => add(total, &coefficient),
                None => sum.push((leaf, coefficient)),
            }
        }
    }
    stack.pop();
    memo.insert(claim, sum.clone());
    sum
}

fn add(total: &mut Coefficient, more: &Coefficient) {
    for (monomial, count) in more {
        *total.entry(monomial.clone()).or_default() += count;
    }
}

fn times_hybrid(coefficient: &Coefficient, hybrid: &str) -> Coefficient {
    coefficient
        .iter()
        .map(|(monomial, &count)| {
            let mut monomial = monomial.clone();
            monomial.push(hybrid.to_string());
            monomial.sort();
            (monomial, count)
        })
        .collect()
}

/// `2·|H|·` before an advantage; empty for 1.
fn coefficient_html(coefficient: &Coefficient) -> String {
    let terms: Vec<String> = coefficient
        .iter()
        .map(|(monomial, &count)| {
            let mut factors: Vec<String> = Vec::new();
            if count != 1 || monomial.is_empty() {
                factors.push(count.to_string());
            }
            factors.extend(monomial.iter().map(|h| format!("|{}|", esc(h))));
            factors.join("·")
        })
        .collect();
    match terms.as_slice() {
        [one] if one == "1" => String::new(),
        [one] => format!("{one}·"),
        many => format!("({})·", many.join(" + ")),
    }
}

/// The proof tree view: an introduction, the legend, and one card per root.
pub(crate) fn render(graph: &ClaimGraph) -> String {
    let mut out = String::new();
    out.push_str(
        "<div class=\"treebody\"><p class=\"treehelp\">An edge parent → child means that the path \
         of the parent cites the child: R<sub>i</sub> is the i-th reduction on the path, and \
         an assumption cited more than once is one node with an edge ×k. \
         Click a proved node to see the game hops of its path.</p>\
         <div class=\"treelegend\">\
         <span><i class=\"sw k-prop\"></i>proposition</span>\
         <span><i class=\"sw k-derived\"></i>derived assumption (established by its path)</span>\
         <span><i class=\"sw k-proved\"></i>base assumption that a proposition proves</span>\
         <span><i class=\"sw k-base\"></i>base assumption (trusted)</span>\
         <span><i class=\"sw k-conj\"></i>conjecture</span>\
         <span><i class=\"sw heavy\"></i>cited more than once</span>\
         <span><i class=\"sw cyc\"></i>cycle</span></div>",
    );
    if graph.roots.is_empty() {
        out.push_str("<p class=\"treehelp\">The theorem has no propositions.</p>");
    }
    for &root in &graph.roots {
        let claim = &graph.claims[root];
        let (leaves, cycle) = bound(graph, root);
        let summands = leaves
            .iter()
            .map(|(leaf, coefficient)| {
                format!(
                    "{}Adv(<b>{}</b>)",
                    coefficient_html(coefficient),
                    esc(&graph.claims[*leaf].name)
                )
            })
            .collect::<Vec<_>>()
            .join(" + ");
        let warn = if cycle {
            "<div class=\"treewarn\">The citations form a cycle; this bound is not sound.</div>"
        } else {
            ""
        };
        let _ = write!(
            out,
            "<div class=\"treecard\"><h2><code>{}</code> <span>{} ~ {}</span></h2>\
             <div class=\"bound\">Adv({}) ≤ {}</div>{warn}<div class=\"treesvg\">{}</div></div>",
            esc(&claim.name),
            esc(&claim.left),
            esc(&claim.right),
            esc(&claim.name),
            if summands.is_empty() {
                "0".to_string()
            } else {
                summands
            },
            tree_svg(graph, root),
        );
    }
    out.push_str("</div>");
    out
}

/// One edge of a root's tree: all citations of `to` on the path of `from`.
struct TreeEdge {
    from: usize,
    to: usize,
    /// `(reduction index, hybrid)` per citation, 1-based.
    refs: Vec<(usize, Option<String>)>,
    /// `to` is on the walk from the root to `from`.
    back: bool,
}

impl TreeEdge {
    fn label(&self) -> String {
        let refs = self
            .refs
            .iter()
            .map(|(i, hybrid)| match hybrid {
                Some(h) => format!("R{i} (hybrid {h})"),
                None => format!("R{i}"),
            })
            .collect::<Vec<_>>()
            .join(", ");
        if self.back {
            format!("cycle: {refs}")
        } else if self.refs.len() > 1 {
            format!("×{} ({refs})", self.refs.len())
        } else {
            refs
        }
    }
}

/// The nodes under `root` in depth-first order (local index -> claim) and the
/// merged edges between them, in local indices.
fn subtree(graph: &ClaimGraph, root: usize) -> (Vec<usize>, Vec<TreeEdge>) {
    let mut nodes = Vec::new();
    let mut local: HashMap<usize, usize> = HashMap::new();
    let mut edges = Vec::new();
    visit(
        graph,
        root,
        &mut nodes,
        &mut local,
        &mut Vec::new(),
        &mut edges,
    );
    (nodes, edges)
}

fn visit(
    graph: &ClaimGraph,
    claim: usize,
    nodes: &mut Vec<usize>,
    local: &mut HashMap<usize, usize>,
    stack: &mut Vec<usize>,
    edges: &mut Vec<TreeEdge>,
) -> usize {
    let me = nodes.len();
    nodes.push(claim);
    local.insert(claim, me);
    stack.push(claim);
    let mut mine: Vec<TreeEdge> = Vec::new();
    for (i, citation) in graph.claims[claim].cites.iter().enumerate() {
        let r = (i + 1, citation.hybrid.clone());
        if let Some(edge) = mine.iter_mut().find(|e| nodes[e.to] == citation.claim) {
            edge.refs.push(r);
            continue;
        }
        let back = stack.contains(&citation.claim);
        let to = match local.get(&citation.claim) {
            Some(&to) => to,
            None => visit(graph, citation.claim, nodes, local, stack, edges),
        };
        mine.push(TreeEdge {
            from: me,
            to,
            refs: vec![r],
            back,
        });
    }
    stack.pop();
    edges.extend(mine);
    me
}

/// Approximate glyph widths of the monospace node text, in px.
const NAME_CHAR: f64 = 7.4;
const SUB_CHAR: f64 = 6.2;
const NAME_LINE: f64 = 16.0;
const SUB_LINE: f64 = 13.0;
const NODE_PAD: f64 = 8.0;
const NODE_GAP: f64 = 22.0;
const RANK_GAP: f64 = 62.0;
const MARGIN: f64 = 12.0;
/// How far a cycle's back edge bulges right of its nodes.
const BULGE: f64 = 70.0;

/// The text lines of a node: `(name lines, small lines)`.
fn node_lines(claim: &Claim) -> (Vec<String>, Vec<String>) {
    let name = match claim.kind {
        ClaimKind::Conjecture => "conjecture".to_string(),
        _ => claim.name.clone(),
    };
    let mut small = wrap(&claim.left, 34);
    let mut right = wrap(&claim.right, 32);
    if let Some(first) = right.first_mut() {
        *first = format!("~ {first}");
    }
    small.extend(right);
    match claim.kind {
        ClaimKind::Derived => small.push(format!(
            "derived{}",
            claim
                .depth
                .map_or(String::new(), |d| format!(", depth {d}"))
        )),
        ClaimKind::ProvedByProposition => {
            if let Some(p) = claim.proved_by.as_ref().filter(|p| **p != claim.name) {
                small.push(format!("proved by proposition {p}"));
            }
        }
        _ => {}
    }
    (wrap(&name, 28), small)
}

/// `text` in lines of at most `width` characters, broken after `_` where
/// possible.
fn wrap(text: &str, width: usize) -> Vec<String> {
    let mut lines: Vec<String> = Vec::new();
    let mut line = String::new();
    for part in text.split_inclusive('_') {
        if !line.is_empty() && line.chars().count() + part.chars().count() > width {
            lines.push(std::mem::take(&mut line));
        }
        line.push_str(part);
        while line.chars().count() > width {
            let rest: String = line.chars().skip(width).collect();
            lines.push(line.chars().take(width).collect());
            line = rest;
        }
    }
    if !line.is_empty() {
        lines.push(line);
    }
    lines
}

fn node_size(claim: &Claim) -> (f64, f64) {
    let (name, small) = node_lines(claim);
    let chars = |lines: &[String]| lines.iter().map(|l| l.chars().count()).max().unwrap_or(0);
    let w = (chars(&name) as f64 * NAME_CHAR).max(chars(&small) as f64 * SUB_CHAR) + 2.0 * NODE_PAD;
    let h = name.len() as f64 * NAME_LINE + small.len() as f64 * SUB_LINE + 2.0 * NODE_PAD - 2.0;
    (w.max(60.0), h)
}

/// A drawn vertex: a node of the tree, or a bend point of a long edge.
#[derive(Clone)]
struct Vertex {
    /// The local node; `None` for a bend point.
    node: Option<usize>,
    rank: usize,
    w: f64,
    h: f64,
    /// Left edge.
    x: f64,
}

/// The layered layout of one root's tree.
struct Layout {
    vertices: Vec<Vertex>,
    /// Per forward edge (index into the edges): the vertices it runs through.
    chains: Vec<Option<Vec<usize>>>,
    rank_top: Vec<f64>,
    rank_height: Vec<f64>,
}

impl Layout {
    fn top(&self, v: usize) -> f64 {
        self.rank_top[self.vertices[v].rank]
    }
    fn bottom(&self, v: usize) -> f64 {
        let vx = &self.vertices[v];
        match vx.node {
            Some(_) => self.top(v) + vx.h,
            None => self.top(v) + self.rank_height[vx.rank],
        }
    }
    fn center(&self, v: usize) -> f64 {
        self.vertices[v].x + self.vertices[v].w / 2.0
    }
}

/// Sugiyama-style: longest-path ranks, a bend point per rank a long edge
/// crosses, barycenter ordering, then x by averaging neighbours under the
/// order's separation constraints.
fn layout(sizes: &[(f64, f64)], edges: &[TreeEdge]) -> Layout {
    let n = sizes.len();
    // Ranks: longest path from the root over the forward edges (a DAG: the
    // back edges close every cycle of the depth-first walk).
    let mut rank = vec![0usize; n];
    let mut indegree = vec![0usize; n];
    for e in edges.iter().filter(|e| !e.back) {
        indegree[e.to] += 1;
    }
    let mut ready: Vec<usize> = (0..n).filter(|&v| indegree[v] == 0).collect();
    while let Some(v) = ready.pop() {
        for e in edges.iter().filter(|e| !e.back && e.from == v) {
            rank[e.to] = rank[e.to].max(rank[v] + 1);
            indegree[e.to] -= 1;
            if indegree[e.to] == 0 {
                ready.push(e.to);
            }
        }
    }
    let ranks = rank.iter().max().map_or(0, |r| r + 1);

    let mut vertices: Vec<Vertex> = (0..n)
        .map(|v| Vertex {
            node: Some(v),
            rank: rank[v],
            w: sizes[v].0,
            h: sizes[v].1,
            x: 0.0,
        })
        .collect();
    let mut chains = Vec::new();
    let mut segments: Vec<(usize, usize)> = Vec::new();
    for e in edges {
        if e.back {
            chains.push(None);
            continue;
        }
        let mut chain = vec![e.from];
        for r in rank[e.from] + 1..rank[e.to] {
            vertices.push(Vertex {
                node: None,
                rank: r,
                w: 6.0,
                h: 0.0,
                x: 0.0,
            });
            chain.push(vertices.len() - 1);
        }
        chain.push(e.to);
        segments.extend(chain.windows(2).map(|w| (w[0], w[1])));
        chains.push(Some(chain));
    }

    // Order within ranks: first appearance, then barycenter sweeps; keep the
    // order with the fewest crossings.
    let mut layers: Vec<Vec<usize>> = vec![Vec::new(); ranks];
    for (v, vx) in vertices.iter().enumerate() {
        layers[vx.rank].push(v);
    }
    let preds = |v: usize| segments.iter().filter(move |s| s.1 == v).map(|s| s.0);
    let succs = |v: usize| segments.iter().filter(move |s| s.0 == v).map(|s| s.1);
    let mut best = layers.clone();
    let mut best_crossings = crossings(&layers, &segments);
    for sweep in 0..16 {
        let down = sweep % 2 == 0;
        let order: Vec<usize> = if down {
            (1..ranks).collect()
        } else {
            (0..ranks.saturating_sub(1)).rev().collect()
        };
        for r in order {
            let neighbour_rank = if down { r - 1 } else { r + 1 };
            let pos: HashMap<usize, usize> = layers[neighbour_rank]
                .iter()
                .enumerate()
                .map(|(i, &v)| (v, i))
                .collect();
            let mut keyed: Vec<(f64, usize)> = layers[r]
                .iter()
                .enumerate()
                .map(|(i, &v)| {
                    let ps: Vec<usize> = if down {
                        preds(v).collect()
                    } else {
                        succs(v).collect()
                    };
                    let key = if ps.is_empty() {
                        i as f64
                    } else {
                        ps.iter().map(|p| pos[p] as f64).sum::<f64>() / ps.len() as f64
                    };
                    (key, v)
                })
                .collect();
            keyed.sort_by(|a, b| a.0.total_cmp(&b.0));
            layers[r] = keyed.into_iter().map(|(_, v)| v).collect();
        }
        let c = crossings(&layers, &segments);
        if c < best_crossings {
            best_crossings = c;
            best = layers.clone();
        }
    }
    let layers = best;

    // x: pack left, then pull each vertex towards the mean of its neighbours.
    for layer in &layers {
        let mut x = 0.0;
        for &v in layer {
            vertices[v].x = x;
            x += vertices[v].w + NODE_GAP;
        }
    }
    for sweep in 0..24 {
        let down = sweep % 2 == 0;
        let order: Vec<usize> = if down {
            (1..ranks).collect()
        } else {
            (0..ranks.saturating_sub(1)).rev().collect()
        };
        for r in order {
            let desired: Vec<f64> = layers[r]
                .iter()
                .map(|&v| {
                    let ns: Vec<usize> = if down {
                        preds(v).collect()
                    } else {
                        succs(v).collect()
                    };
                    if ns.is_empty() {
                        return vertices[v].x;
                    }
                    let c = ns
                        .iter()
                        .map(|&u| vertices[u].x + vertices[u].w / 2.0)
                        .sum::<f64>()
                        / ns.len() as f64;
                    c - vertices[v].w / 2.0
                })
                .collect();
            let widths: Vec<f64> = layers[r].iter().map(|&v| vertices[v].w).collect();
            for (&v, x) in layers[r].iter().zip(separate(&desired, &widths)) {
                vertices[v].x = x;
            }
        }
    }
    let min_x = vertices.iter().map(|v| v.x).fold(f64::MAX, f64::min);
    for v in &mut vertices {
        v.x += MARGIN - min_x;
    }

    let mut rank_height = vec![0.0f64; ranks];
    for v in vertices.iter().filter(|v| v.node.is_some()) {
        rank_height[v.rank] = rank_height[v.rank].max(v.h);
    }
    let mut rank_top = Vec::with_capacity(ranks);
    let mut y = MARGIN;
    for h in &rank_height {
        rank_top.push(y);
        y += h + RANK_GAP;
    }
    Layout {
        vertices,
        chains,
        rank_top,
        rank_height,
    }
}

/// Edge crossings between neighbouring ranks.
fn crossings(layers: &[Vec<usize>], segments: &[(usize, usize)]) -> usize {
    // vertex -> (rank, position in rank)
    let pos: HashMap<usize, (usize, usize)> = layers
        .iter()
        .enumerate()
        .flat_map(|(r, layer)| layer.iter().enumerate().map(move |(i, &v)| (v, (r, i))))
        .collect();
    let mut count = 0;
    for (i, a) in segments.iter().enumerate() {
        for b in &segments[i + 1..] {
            let ((ra, a0), (_, a1)) = (pos[&a.0], pos[&a.1]);
            let ((rb, b0), (_, b1)) = (pos[&b.0], pos[&b.1]);
            if ra == rb && (a0 < b0 && a1 > b1 || a0 > b0 && a1 < b1) {
                count += 1;
            }
        }
    }
    count
}

/// The left edges closest (least squares) to `desired` that keep the order and
/// `NODE_GAP` between neighbours: overlapping runs are merged into blocks
/// placed at their mean.
fn separate(desired: &[f64], widths: &[f64]) -> Vec<f64> {
    // (first member, members, sum of desired minus offset in block, span)
    let mut blocks: Vec<(usize, usize, f64, f64)> = Vec::new();
    for (i, (&d, &w)) in desired.iter().zip(widths).enumerate() {
        blocks.push((i, 1, d, w));
        while blocks.len() > 1 {
            let cur = blocks[blocks.len() - 1];
            let prev = blocks[blocks.len() - 2];
            let x = |b: (usize, usize, f64, f64)| b.2 / b.1 as f64;
            if x(prev) + prev.3 + NODE_GAP <= x(cur) {
                break;
            }
            // `cur`'s members sit `shift` right of the merged block's left edge.
            let shift = prev.3 + NODE_GAP;
            blocks.pop();
            *blocks.last_mut().expect("two blocks") = (
                prev.0,
                prev.1 + cur.1,
                prev.2 + cur.2 - shift * cur.1 as f64,
                shift + cur.3,
            );
        }
    }
    let mut xs = Vec::with_capacity(desired.len());
    for (first, members, sum, _) in blocks {
        let mut x = sum / members as f64;
        for w in &widths[first..first + members] {
            xs.push(x);
            x += w + NODE_GAP;
        }
    }
    xs
}

/// One root's tree as inline SVG.
fn tree_svg(graph: &ClaimGraph, root: usize) -> String {
    let (nodes, edges) = subtree(graph, root);
    let sizes: Vec<(f64, f64)> = nodes.iter().map(|&c| node_size(&graph.claims[c])).collect();
    let lay = layout(&sizes, &edges);

    // Ports: a vertex's out-edges leave its bottom in the order of their
    // targets, in-edges enter its top in the order of their sources.
    let mut out_ports: HashMap<(usize, usize), f64> = HashMap::new();
    let mut in_ports: HashMap<(usize, usize), f64> = HashMap::new();
    let segments: Vec<(usize, usize)> = lay
        .chains
        .iter()
        .flatten()
        .flat_map(|chain| chain.windows(2).map(|w| (w[0], w[1])))
        .collect();
    for v in 0..lay.vertices.len() {
        let vx = &lay.vertices[v];
        for (outgoing, ports) in [(true, &mut out_ports), (false, &mut in_ports)] {
            let mut ends: Vec<(usize, usize)> = segments
                .iter()
                .copied()
                .filter(|&(a, b)| if outgoing { a == v } else { b == v })
                .collect();
            ends.sort_by(|a, b| {
                let other = |s: &(usize, usize)| if outgoing { s.1 } else { s.0 };
                lay.center(other(a)).total_cmp(&lay.center(other(b)))
            });
            ends.dedup();
            let k = ends.len() as f64;
            for (i, seg) in ends.into_iter().enumerate() {
                let x = match vx.node {
                    Some(_) => vx.x + vx.w * (i as f64 + 1.0) / (k + 1.0),
                    None => lay.center(v),
                };
                ports.insert(seg, x);
            }
        }
    }

    let mut width: f64 = 0.0;
    let mut height: f64 = 0.0;
    let mut body = String::new();
    for (e, edge) in edges.iter().enumerate() {
        let heavy = edge.refs.len() > 1;
        let class = if edge.back {
            "tedge cyc"
        } else if heavy {
            "tedge heavy"
        } else {
            "tedge"
        };
        let marker = if edge.back {
            "tarrow-cyc"
        } else if heavy {
            "tarrow-heavy"
        } else {
            "tarrow"
        };
        let label = edge.label();
        let (path, (lx, ly)) = match &lay.chains[e] {
            Some(chain) => {
                let mut d = String::new();
                let mut label_at = (0.0, 0.0);
                for (i, seg) in chain.windows(2).enumerate() {
                    let (a, b) = (seg[0], seg[1]);
                    let (x0, y0) = (out_ports[&(a, b)], lay.bottom(a));
                    let (x1, y1) = (in_ports[&(a, b)], lay.top(b));
                    let dy = (y1 - y0) / 2.0;
                    if i == 0 {
                        let _ = write!(d, "M{x0:.1},{y0:.1}");
                        label_at = ((x0 + x1) / 2.0 + 5.0, (y0 + y1) / 2.0 + 3.0);
                    } else {
                        let _ = write!(d, " L{x0:.1},{y0:.1}");
                    }
                    let _ = write!(
                        d,
                        " C{x0:.1},{:.1} {x1:.1},{:.1} {x1:.1},{y1:.1}",
                        y0 + dy,
                        y1 - dy
                    );
                }
                (d, label_at)
            }
            None => {
                // A cycle: from the right side of `from` up to the right side
                // of `to`, bulging right.
                let (a, b) = (edge.from, edge.to);
                let (xa, ya) = (
                    lay.vertices[a].x + lay.vertices[a].w,
                    lay.top(a) + lay.vertices[a].h / 2.0,
                );
                let (xb, yb) = (
                    lay.vertices[b].x + lay.vertices[b].w,
                    lay.top(b) + lay.vertices[b].h / 2.0,
                );
                let bulge = xa.max(xb) + BULGE;
                width = width.max(bulge + MARGIN);
                (
                    format!(
                        "M{xa:.1},{ya:.1} C{bulge:.1},{ya:.1} {bulge:.1},{yb:.1} {xb:.1},{yb:.1}"
                    ),
                    (bulge - BULGE / 2.0, (ya + yb) / 2.0),
                )
            }
        };
        let _ = write!(
            body,
            "<path class=\"{class}\" d=\"{path}\" marker-end=\"url(#{marker})\"/>\
             <text class=\"tlabel{}\" x=\"{lx:.1}\" y=\"{ly:.1}\">{}</text>",
            if edge.back {
                " cyc"
            } else if heavy {
                " heavy"
            } else {
                ""
            },
            esc(&label),
        );
        width = width.max(lx + label.chars().count() as f64 * SUB_CHAR + MARGIN);
    }

    for (v, vx) in lay.vertices.iter().enumerate() {
        let Some(local) = vx.node else { continue };
        let claim = &graph.claims[nodes[local]];
        let (x, y) = (vx.x, lay.top(v));
        width = width.max(x + vx.w + MARGIN);
        height = height.max(y + vx.h + MARGIN);
        let (name, small) = node_lines(claim);
        let title = node_title(claim);
        let goto = claim.view.as_ref().map_or(String::new(), |view| {
            format!(" data-goto=\"{}\"", esc(view))
        });
        let _ = write!(
            body,
            "<g class=\"tnode {}{}{}\"{goto}><title>{}</title>\
             <rect x=\"{x:.1}\" y=\"{y:.1}\" width=\"{:.1}\" height=\"{:.1}\" rx=\"6\"/>",
            claim.kind.class(),
            if claim.view.is_some() { " link" } else { "" },
            if local == 0 { " root" } else { "" },
            esc(&title),
            vx.w,
            vx.h,
        );
        let cx = x + vx.w / 2.0;
        let mut ty = y + NODE_PAD + 11.0;
        for line in &name {
            let _ = write!(
                body,
                "<text class=\"tname\" x=\"{cx:.1}\" y=\"{ty:.1}\">{}</text>",
                esc(line)
            );
            ty += NAME_LINE;
        }
        ty -= 2.0;
        for line in &small {
            let _ = write!(
                body,
                "<text class=\"tsub\" x=\"{cx:.1}\" y=\"{ty:.1}\">{}</text>",
                esc(line)
            );
            ty += SUB_LINE;
        }
        body.push_str("</g>");
    }

    let marker = |id: &str, class: &str| {
        format!(
            "<marker id=\"{id}\" viewBox=\"0 0 10 10\" refX=\"10\" refY=\"5\" markerWidth=\"7\" \
             markerHeight=\"7\" orient=\"auto-start-reverse\"><path d=\"M0,0 L10,5 L0,10 z\" \
             class=\"{class}\"/></marker>"
        )
    };
    format!(
        "<svg class=\"tree\" width=\"{width:.0}\" height=\"{height:.0}\" \
         viewBox=\"0 0 {width:.1} {height:.1}\" xmlns=\"http://www.w3.org/2000/svg\">\
         <defs>{}{}{}</defs>{body}</svg>",
        marker("tarrow", "thead"),
        marker("tarrow-heavy", "thead heavy"),
        marker("tarrow-cyc", "thead cyc"),
    )
}

fn node_title(claim: &Claim) -> String {
    let games = format!("{} ~ {}", claim.left, claim.right);
    match claim.kind {
        ClaimKind::Proposition => {
            format!("proposition {}: {games}\nclick for its game hops", claim.name)
        }
        ClaimKind::Derived => format!(
            "derived assumption {}: {games}\nclick for the path that establishes it",
            claim.name
        ),
        ClaimKind::ProvedByProposition => format!(
            "base assumption {}: {games}\nproved by proposition {} (the tool trusts the \
             assumption; mark it `derived` to have it checked)\nclick for the proposition's game hops",
            claim.name,
            claim.proved_by.as_deref().unwrap_or("?"),
        ),
        ClaimKind::Base => format!("base assumption {}: {games}\ntrusted", claim.name),
        ClaimKind::Conjecture => format!("conjecture {games}\nnot checked by the tool"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrap_breaks_after_underscores() {
        assert_eq!(
            wrap("PRF_Unique_Input_Assumption_DPRF_Ideal_Output", 20),
            vec!["PRF_Unique_Input_", "Assumption_DPRF_", "Ideal_Output"]
        );
        assert_eq!(wrap("abcdefgh", 3), vec!["abc", "def", "gh"]);
        assert_eq!(wrap("", 3), Vec::<String>::new());
    }

    #[test]
    fn separate_keeps_order_and_gap() {
        let xs = separate(&[0.0, 0.0, 0.0], &[10.0, 10.0, 10.0]);
        assert_eq!(xs.len(), 3);
        for pair in xs.windows(2) {
            assert!((pair[1] - pair[0] - (10.0 + NODE_GAP)).abs() < 1e-9);
        }
        // Centred on the common desired position.
        assert!((xs[1] - 0.0).abs() < 1e-9);
        // Far apart stays put.
        assert_eq!(separate(&[0.0, 100.0], &[10.0, 10.0]), vec![0.0, 100.0]);
    }

    #[test]
    fn coefficients_print_counts_and_hybrids() {
        let one = BTreeMap::from([(Vec::new(), 1)]);
        assert_eq!(coefficient_html(&one), "");
        let two = BTreeMap::from([(Vec::new(), 2)]);
        assert_eq!(coefficient_html(&two), "2·");
        assert_eq!(coefficient_html(&times_hybrid(&two, "H")), "2·|H|·");
        let mut mixed = one.clone();
        add(&mut mixed, &times_hybrid(&one, "H"));
        assert_eq!(coefficient_html(&mixed), "(1 + |H|)·");
    }
}
