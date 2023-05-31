use crate::RequirementKind;

use itertools::Itertools;
use petgraph::graph::{DiGraph, EdgeReference, NodeIndex};
use petgraph::prelude::{Bfs, EdgeRef};
use rustc_hash::FxHashMap;
use std::collections::HashMap;
use std::fmt::Formatter;
use std::hash::Hash;

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
    requirements: Vec<DisplayRequirement>,
    installable: bool,
}

pub struct DisplayError {
    root_requirements: Vec<DisplayRequirement>,
}

impl std::fmt::Display for DisplayError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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
                DisplayOp::Candidate(candidate) => {
                    if candidate.requirements.is_empty() {
                        writeln!(f, "{indent}|-- {}", candidate.name)?;
                    } else {
                        writeln!(f, "{indent}|-- {} would require", candidate.name)?;
                    }
                    stack.extend(
                        candidate
                            .requirements
                            .iter()
                            .map(|r| (DisplayOp::Requirement(r), depth + 1)),
                    );
                }
            }
        }

        Ok(())
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

    pub fn print_user_friendly_error(
        &self,
        display_candidate: impl Fn(TCandidate) -> String,
        display_requirement: impl Fn(TRequirement) -> String,
    ) -> DisplayError {
        let root_node = self.node_ids[&Node::Root];
        let mut error = DisplayError {
            root_requirements: Vec::new(),
        };
        let top_level_edges = self
            .graph
            .edges(root_node)
            .group_by(|e| e.weight().requirement.clone());

        for (requirement, candidates) in top_level_edges.into_iter() {
            let req = self.get_display_requirement(
                &display_candidate,
                &display_requirement,
                display_requirement(requirement),
                candidates.collect(),
            );
            error.root_requirements.push(req);
        }

        error
    }

    fn get_display_requirement(
        &self,
        display_candidate: &impl Fn(TCandidate) -> String,
        display_requirement: &impl Fn(TRequirement) -> String,
        name: String,
        candidate_edges: Vec<EdgeReference<Edge<TRequirement>>>,
    ) -> DisplayRequirement {
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

        let mut candidates = candidate_edges
            .into_iter()
            .map(|edge| {
                if edge.weight().status == EdgeStatus::Conflict {
                    GetDisplayCandidateResult::Conflict
                } else {
                    match self.get_display_candidate(display_candidate, display_requirement, edge) {
                        None => GetDisplayCandidateResult::Missing,
                        Some(c) => GetDisplayCandidateResult::Candidate(c),
                    }
                }
            })
            .collect::<Vec<_>>();

        candidates.sort_by_key(|c| c.installable());

        let candidates = if candidates.iter().all(|c| matches!(c, GetDisplayCandidateResult::Missing)) {
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
                        GetDisplayCandidateResult::Missing | GetDisplayCandidateResult::Conflict => None,
                        GetDisplayCandidateResult::Candidate(c) => Some(c),
                    })
                    .collect(),
            )
        };

        DisplayRequirement::new(name, candidates)
    }

    fn get_display_candidate(
        &self,
        display_candidate: &impl Fn(TCandidate) -> String,
        display_requirement: &impl Fn(TRequirement) -> String,
        edge_to_candidate: EdgeReference<Edge<TRequirement>>,
    ) -> Option<DisplayCandidate> {
        match &self.graph[edge_to_candidate.target()] {
            Node::Candidate(c) => {
                let candidate_dependencies = self
                    .graph
                    .edges(edge_to_candidate.target())
                    .group_by(|e| e.weight().requirement.clone());

                let mut reqs = Vec::new();
                for (requirement, edges) in candidate_dependencies.into_iter() {
                    reqs.push(self.get_display_requirement(
                        display_candidate,
                        display_requirement,
                        display_requirement(requirement),
                        edges.collect(),
                    ));
                }

                Some(DisplayCandidate {
                    name: display_candidate(c.clone()),
                    installable: edge_to_candidate.weight().status == EdgeStatus::Healthy
                        && reqs.iter().all(|r| r.installable),
                    requirements: reqs,
                })
            }
            Node::NotFound => None,
            _ => unreachable!(),
        }
    }

    pub fn graphviz(
        &self,
        display_candidate: impl Fn(TCandidate) -> String,
        display_requirement: impl Fn(TRequirement) -> String,
    ) -> String {
        let root_node = self.node_ids[&Node::Root];
        let mut bfs = Bfs::new(&self.graph, root_node);

        let mut buf = String::new();
        buf.push_str("digraph {\n");
        while let Some(nx) = bfs.next(&self.graph) {
            // The node itself
            let node1 = self.graph.node_weight(nx).unwrap();
            let node1_name = match node1 {
                Node::Root => "root".to_string(),
                Node::Candidate(c) => (display_candidate)(c.clone()),
                Node::NotFound => "not_found".to_string(),
            };

            for edge in self.graph.edges(nx) {
                let neighbor = edge.target();

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
