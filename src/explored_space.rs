use crate::RequirementKind;

use itertools::Itertools;
use petgraph::graph::{DiGraph, EdgeReference, NodeIndex};
use petgraph::prelude::{Bfs, EdgeRef};
use petgraph::visit::DfsPostOrder;
use petgraph::Direction;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{HashMap, HashSet};
use std::fmt::Formatter;
use std::hash::Hash;
use std::rc::Rc;

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Node<TCandidate> {
    Root,
    Candidate(TCandidate),
    NotFound,
}

#[derive(Clone)]
struct Edge<TRequirement> {
    requirement: TRequirement,
    kind: RequirementKind,
    status: EdgeStatus,
}

impl<TRequirement> Edge<TRequirement> {
    fn healthy(requirement: TRequirement, kind: RequirementKind) -> Self {
        Self {
            requirement,
            kind,
            status: EdgeStatus::Healthy,
        }
    }

    fn conflict(requirement: TRequirement, kind: RequirementKind) -> Self {
        Self {
            requirement,
            kind,
            status: EdgeStatus::Conflict,
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
enum EdgeStatus {
    Conflict,
    Healthy,
}

pub struct DisplayRequirement {
    name: String,
    candidates: DisplayCandidates,
    installable: bool,
}

enum DisplayCandidates {
    Candidates(Vec<DisplayCandidate>),
    Conflict,
    Missing,
}

impl DisplayRequirement {
    fn new(name: String, candidates: DisplayCandidates) -> Self {
        let installable = match &candidates {
            DisplayCandidates::Candidates(candidates)
                if candidates.iter().any(|c| c.installable) =>
            {
                true
            }
            _ => false,
        };

        Self {
            name,
            installable,
            candidates,
        }
    }
}

pub struct DisplayCandidate {
    name: String,
    version: String,
    node_id: NodeIndex,
    requirements: Vec<DisplayRequirement>,
    installable: bool,
}

struct MergedCandidate {
    versions: Vec<String>,
    ids: Vec<NodeIndex>,
}

pub struct DisplayError {
    root_requirements: Vec<DisplayRequirement>,
    merged_candidates: FxHashMap<NodeIndex, Rc<MergedCandidate>>,
}

impl std::fmt::Display for DisplayError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut reported: FxHashSet<NodeIndex> = HashSet::default();

        pub enum DisplayOp<'a> {
            Requirement(&'a DisplayRequirement),
            Candidate(&'a DisplayCandidate),
        }

        writeln!(f, "The following packages are incompatible")?;

        let mut stack = self
            .root_requirements
            .iter()
            .sorted_by_key(|r| r.installable)
            .map(|r| (DisplayOp::Requirement(r), 0))
            .collect::<Vec<_>>();
        while let Some((node, depth)) = stack.pop() {
            let indent = " ".repeat(depth * 4);

            match node {
                DisplayOp::Requirement(requirement) => {
                    let installable = requirement.installable;
                    let req = &requirement.name;

                    if let DisplayCandidates::Missing = requirement.candidates {
                        // No candidates for requirement
                        if depth == 0 {
                            writeln!(
                                f,
                                "{indent}|-- No candidates where found for {}.",
                                requirement.name
                            )?;
                        } else {
                            writeln!(
                                f,
                                "{indent}|-- {}, for which no candidates where found.",
                                requirement.name
                            )?;
                        }
                    } else if installable {
                        // Package can be installed (only mentioned for top-level requirements)
                        if depth == 0 {
                            writeln!(f, "|-- {req} will be installed;")?;
                        }
                    } else {
                        // Package cannot be installed
                        match &requirement.candidates {
                            DisplayCandidates::Candidates(candidates) => {
                                // The conflicting requirement is further down the tree
                                if depth == 0 {
                                    writeln!(f, "|-- {req} cannot be installed because:")?;
                                } else {
                                    writeln!(
                                        f,
                                        "{indent}|-- {req}, which cannot be installed because:"
                                    )?;
                                }

                                stack.extend(
                                    candidates
                                        .iter()
                                        .map(|c| (DisplayOp::Candidate(c), depth + 1)),
                                );
                            }
                            DisplayCandidates::Conflict => {
                                // We have reached the conflicting requirement
                                if depth == 0 {
                                    writeln!(f, "|-- {req} cannot be installed, because it conflicts with the versions reported above.")?;
                                } else {
                                    writeln!(f, "{indent}|-- {req}, which conflicts with the already selected version.")?;
                                }
                            }
                            DisplayCandidates::Missing => unreachable!(),
                        }
                    }
                }
                DisplayOp::Candidate(candidate) if !reported.contains(&candidate.node_id) => {
                    let version =
                        if let Some(merged) = self.merged_candidates.get(&candidate.node_id) {
                            reported.extend(&merged.ids);
                            merged.versions.join(" | ")
                        } else {
                            candidate.version.clone()
                        };

                    if candidate.requirements.is_empty() {
                        writeln!(f, "{indent}|-- {} {version}", candidate.name)?;
                    } else {
                        writeln!(f, "{indent}|-- {} {version} would require", candidate.name)?;
                    }

                    stack.extend(
                        candidate
                            .requirements
                            .iter()
                            .map(|r| (DisplayOp::Requirement(r), depth + 1)),
                    );
                }
                _ => {}
            }
        }

        Ok(())
    }
}

enum GetDisplayCandidateResult {
    Missing,
    Conflict,
    Candidate(DisplayCandidate),
}

impl GetDisplayCandidateResult {
    fn installable(&self) -> bool {
        match self {
            GetDisplayCandidateResult::Missing | GetDisplayCandidateResult::Conflict => false,
            GetDisplayCandidateResult::Candidate(c) => c.installable,
        }
    }
}

#[derive(Clone)]
pub struct ExploredSpace<TRequirement, TCandidate> {
    node_ids: FxHashMap<Node<TCandidate>, NodeIndex>,
    graph: DiGraph<Node<TCandidate>, Edge<TRequirement>>,
}

impl<TRequirement, TCandidate> ExploredSpace<TRequirement, TCandidate>
where
    TRequirement: Hash + Eq + Clone,
    TCandidate: Hash + Eq + Clone,
{
    pub(crate) fn new() -> Self {
        Self {
            node_ids: HashMap::default(),
            graph: DiGraph::new(),
        }
    }

    pub(crate) fn get_or_add_node(&mut self, node: Node<TCandidate>) -> NodeIndex {
        *self
            .node_ids
            .entry(node.clone())
            .or_insert_with(|| self.graph.add_node(node))
    }

    pub(crate) fn track_requirement(
        &mut self,
        node1: NodeIndex,
        node2: NodeIndex,
        requirement: TRequirement,
        kind: RequirementKind,
    ) {
        self.graph
            .add_edge(node1, node2, Edge::healthy(requirement, kind));
    }

    pub(crate) fn track_conflict(
        &mut self,
        node1: NodeIndex,
        node2: NodeIndex,
        requirement: TRequirement,
        kind: RequirementKind,
    ) {
        self.graph
            .add_edge(node1, node2, Edge::conflict(requirement, kind));
    }

    pub(crate) fn track_missing(
        &mut self,
        node1: NodeIndex,
        requirement: TRequirement,
        kind: RequirementKind,
    ) {
        let node2 = self.get_or_add_node(Node::NotFound);
        self.graph
            .add_edge(node1, node2, Edge::healthy(requirement, kind));
    }

    pub fn print_user_friendly_error<K1: Ord, K2: Ord>(
        &self,
        display_candidate_name: impl Fn(TCandidate) -> String,
        display_candidate_version: impl Fn(TCandidate) -> String,
        sort_candidate_version: impl Fn(&TCandidate) -> K1,
        display_requirement: impl Fn(TRequirement) -> String,
        sort_requirement: impl Fn(&TRequirement) -> K2,
    ) -> DisplayError {
        // Build a tree from the root requirements to the conflicts
        let root_node = self.node_ids[&Node::Root];
        let mut root_requirements = Vec::new();
        let top_level_edges = self
            .graph
            .edges(root_node)
            .group_by(|e| e.weight().requirement.clone());

        let mut path = FxHashSet::default();
        for (requirement, candidates) in top_level_edges.into_iter() {
            let req = self.get_display_requirement(
                &mut path,
                &display_candidate_name,
                &display_candidate_version,
                &display_requirement,
                display_requirement(requirement),
                candidates.collect(),
            );
            root_requirements.push(req);
        }

        // Gather information about nodes that can be merged
        let mut maybe_merge = FxHashMap::default();
        for node_id in self.graph.node_indices() {
            let candidate = match &self.graph[node_id] {
                Node::Root | Node::NotFound => continue,
                Node::Candidate(c) => c,
            };

            if self
                .graph
                .edges_directed(node_id, Direction::Incoming)
                .any(|e| e.weight().status == EdgeStatus::Conflict)
            {
                // Nodes that are the target of a conflict should never be merged
                continue;
            }

            let predecessors: Vec<_> = self
                .graph
                .edges_directed(node_id, Direction::Incoming)
                .map(|e| e.source())
                .sorted_unstable()
                .collect();
            let successors: Vec<_> = self
                .graph
                .edges(node_id)
                .map(|e| (e.target(), &e.weight().requirement))
                .sorted_unstable_by_key(|&(target_node, requirement)| {
                    (target_node, sort_requirement(requirement))
                })
                .collect();

            let name = display_candidate_name(candidate.clone());

            let entry = maybe_merge
                .entry((name.clone(), predecessors, successors))
                .or_insert((Vec::new(), Vec::new()));

            entry.0.push(node_id);
            entry.1.push(candidate.clone());
        }

        let mut merged_candidates = HashMap::default();
        for mut m in maybe_merge.into_values() {
            if m.0.len() > 1 {
                m.1.sort_unstable_by_key(&sort_candidate_version);
                let m = Rc::new(MergedCandidate {
                    ids: m.0,
                    versions: m
                        .1
                        .into_iter()
                        .map(|c| display_candidate_version(c))
                        .collect(),
                });
                for id in &m.ids {
                    merged_candidates.insert(id.clone(), m.clone());
                }
            }
        }

        DisplayError {
            root_requirements,
            merged_candidates,
        }
    }

    fn get_display_requirement(
        &self,
        path: &mut FxHashSet<NodeIndex>,
        display_candidate_name: &impl Fn(TCandidate) -> String,
        display_candidate_version: &impl Fn(TCandidate) -> String,
        display_requirement: &impl Fn(TRequirement) -> String,
        name: String,
        candidate_edges: Vec<EdgeReference<Edge<TRequirement>>>,
    ) -> DisplayRequirement {
        let mut candidates = candidate_edges
            .into_iter()
            .map(|edge| {
                self.get_display_candidate(
                    path,
                    display_candidate_name,
                    display_candidate_version,
                    display_requirement,
                    edge,
                )
            })
            .collect::<Vec<_>>();

        candidates.sort_by_key(|c| c.installable());

        let candidates = if candidates
            .iter()
            .all(|c| matches!(c, GetDisplayCandidateResult::Missing))
        {
            DisplayCandidates::Missing
        } else if candidates
            .iter()
            .all(|c| matches!(c, GetDisplayCandidateResult::Conflict))
        {
            DisplayCandidates::Conflict
        } else {
            DisplayCandidates::Candidates(
                candidates
                    .into_iter()
                    .flat_map(|c| match c {
                        GetDisplayCandidateResult::Missing
                        | GetDisplayCandidateResult::Conflict => None,
                        GetDisplayCandidateResult::Candidate(c) => Some(c),
                    })
                    .collect(),
            )
        };

        DisplayRequirement::new(name, candidates)
    }

    fn get_display_candidate(
        &self,
        path: &mut FxHashSet<NodeIndex>,
        display_candidate_name: &impl Fn(TCandidate) -> String,
        display_candidate_version: &impl Fn(TCandidate) -> String,
        display_requirement: &impl Fn(TRequirement) -> String,
        edge_to_candidate: EdgeReference<Edge<TRequirement>>,
    ) -> GetDisplayCandidateResult {
        if edge_to_candidate.weight().status == EdgeStatus::Conflict {
            return GetDisplayCandidateResult::Conflict;
        }

        match &self.graph[edge_to_candidate.target()] {
            Node::Candidate(c) => {
                let name = display_candidate_name(c.clone());
                let version = display_candidate_version(c.clone());
                let node_id = edge_to_candidate.target();

                // If already visited, return the same candidate, but without requirements
                if path.contains(&node_id) {
                    return GetDisplayCandidateResult::Candidate(DisplayCandidate {
                        name,
                        version,
                        node_id,
                        requirements: vec![],
                        installable: true,
                    });
                }

                path.insert(node_id);

                let candidate_dependencies = self
                    .graph
                    .edges(edge_to_candidate.target())
                    .group_by(|e| e.weight().requirement.clone());

                let mut reqs = Vec::new();
                for (requirement, edges) in candidate_dependencies.into_iter() {
                    reqs.push(self.get_display_requirement(
                        path,
                        display_candidate_name,
                        display_candidate_version,
                        display_requirement,
                        display_requirement(requirement),
                        edges.collect(),
                    ));
                }

                path.remove(&node_id);

                GetDisplayCandidateResult::Candidate(DisplayCandidate {
                    name,
                    version,
                    node_id,
                    installable: edge_to_candidate.weight().status == EdgeStatus::Healthy
                        && reqs.iter().all(|r| r.installable),
                    requirements: reqs,
                })
            }
            Node::NotFound => GetDisplayCandidateResult::Missing,
            _ => unreachable!(),
        }
    }

    pub fn graphviz(
        &self,
        display_candidate: impl Fn(TCandidate) -> String,
        display_requirement: impl Fn(TRequirement) -> String,
        only_conflicting_paths: bool,
    ) -> String {
        let root_node = self.node_ids[&Node::Root];
        let mut bfs = Bfs::new(&self.graph, root_node);

        let mut interesting_nodes: FxHashSet<NodeIndex> = FxHashSet::default();
        if only_conflicting_paths {
            let mut dfs = DfsPostOrder::new(&self.graph, root_node);
            while let Some(nx) = dfs.next(&self.graph) {
                // Two kinds of interesting nodes:
                // * Nodes that have an edge to an existing interesting node
                // * Nodes that have incoming conflict edges
                if self
                    .graph
                    .edges(nx)
                    .any(|e| interesting_nodes.contains(&e.target()))
                    || self
                        .graph
                        .edges_directed(nx, Direction::Incoming)
                        .any(|e| e.weight().status == EdgeStatus::Conflict)
                {
                    interesting_nodes.insert(nx);
                }
            }
            if let Some(nx) = self.node_ids.get(&Node::NotFound) {
                interesting_nodes.insert(nx.clone());
            }
        }

        let mut buf = String::new();
        buf.push_str("digraph {\n");
        while let Some(nx) = bfs.next(&self.graph) {
            if only_conflicting_paths && !interesting_nodes.contains(&nx) {
                continue;
            }

            // The node itself
            let node1 = self.graph.node_weight(nx).unwrap();
            let node1_name = match node1 {
                Node::Root => "root".to_string(),
                Node::Candidate(c) => (display_candidate)(c.clone()),
                Node::NotFound => "not_found".to_string(),
            };

            for edge in self.graph.edges(nx) {
                let neighbor = edge.target();

                if only_conflicting_paths && !interesting_nodes.contains(&neighbor) {
                    continue;
                }

                let node2 = self.graph.node_weight(neighbor).unwrap();
                let node2_name = match node2 {
                    Node::Root => "root".to_string(),
                    Node::Candidate(c) => (display_candidate)(c.clone()),
                    Node::NotFound => "not_found".to_string(),
                };

                let label = (display_requirement)(edge.weight().requirement.clone());
                let color =
                    if edge.weight().status == EdgeStatus::Conflict || node2_name == "not_found" {
                        "red"
                    } else {
                        "black"
                    };

                let line =
                    format!(r#""{node1_name}" -> "{node2_name}"[color={color}, label="{label}"];"#);
                buf.push_str(&line);
                buf.push('\n');
            }
        }
        buf.push('}');

        buf
    }
}
