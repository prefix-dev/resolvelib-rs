use crate::RequirementKind;

use itertools::Itertools;
use petgraph::graph::{DiGraph, EdgeIndex, EdgeReference, NodeIndex};
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
    candidates: Vec<DisplayCandidate>,
    installable: bool,
}

impl DisplayRequirement {
    fn new(name: String, candidates: Vec<DisplayCandidate>) -> Self {
        Self {
            name,
            installable: candidates.iter().any(|c| c.installable),
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
            NoCandidates(&'a DisplayRequirement),
        }

        writeln!(f, "The following packages are incompatible")?;

        let mut stack = self
            .root_requirements
            .iter()
            .sorted_by_key(|r| r.installable)
            .map(|r| (DisplayOp::Requirement(r), 0))
            .collect::<Vec<_>>();
        while let Some((node, depth)) = stack.pop() {
            let indent = " ".repeat(depth * 3 + 1);

            match node {
                DisplayOp::Requirement(requirement) => {
                    let installable = requirement.installable;
                    let req = &requirement.name;

                    if requirement.candidates.is_empty() {
                        stack.push((DisplayOp::NoCandidates(requirement), depth + 1));
                    } else if requirement.candidates.len() == 1 {
                        // This is a leaf in the graph
                        if installable {
                            if depth == 0 {
                                writeln!(f, "|-- {req} is installable;")?;
                            } else {
                                writeln!(f, "{indent}|-- {req}, which can be installed;")?;
                            }
                        } else {
                            if depth == 0 {
                                writeln!(f, "|-- {req} is non-installable, because it conflicts with any installable versions previously reported.")?;
                            } else {
                                writeln!(f, "{indent}|-- {req}, which conflicts with any installable versions previously reported.")?;
                            }
                        }
                    } else {
                        // This node has children
                        if depth == 0 {
                            if installable {
                                writeln!(f, "|-- {req} is installable with the potential options")?;
                            } else {
                                writeln!(f, "|-- {req} is non-installable because there are no viable options")?;
                            }
                        } else {
                            if installable {
                                writeln!(f, "{indent}|-- {req}, which is installable with the potential options")?;
                            } else {
                                writeln!(f, "{indent}|-- {req}, which is non-installable because there are no viable options")?;
                            }
                        }

                        stack.extend(
                            requirement
                                .candidates
                                .iter()
                                .map(|c| (DisplayOp::Candidate(c), depth + 1)),
                        );
                    }
                }
                DisplayOp::Candidate(candidate) => {
                    writeln!(f, "{indent}|-- {} would require", candidate.name)?;
                    stack.extend(
                        candidate
                            .requirements
                            .iter()
                            .map(|r| (DisplayOp::Requirement(r), depth + 1)),
                    );
                }
                DisplayOp::NoCandidates(requirement) => {
                    writeln!(
                        f,
                        "{indent}|-- {}, for which no candidates where found",
                        requirement.name
                    )?;
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
        // ---
        // Step 1: Propagate conflict information up the graph, storing the resulting info in
        // `edges_with_conflicts`
        // ---
        let mut edges_with_conflicts = FxHashMap::default();

        enum Op<T> {
            CheckPackage(T),
            DetectConflicts(T),
        }

        let missing = self.node_ids.get(&Node::NotFound).cloned();
        let root_node = self.node_ids[&Node::Root];
        let mut stack = self
            .graph
            .edges(root_node)
            .map(Op::CheckPackage)
            .collect::<Vec<_>>();

        while let Some(op) = stack.pop() {
            match op {
                Op::CheckPackage(edge) => {
                    // Schedule a DetectConflicts step after the dependencies have been checked
                    stack.push(Op::DetectConflicts(edge));

                    // Check this package's dependencies
                    let node = edge.target();
                    for edge in self.graph.edges(node) {
                        let requirement = edge.weight();
                        let child_id = edge.target();

                        if requirement.status == EdgeStatus::Conflict || Some(child_id) == missing {
                            // Reached a conflict, no need to recurse further down this path
                            edges_with_conflicts.insert(edge.id(), edge);
                        } else {
                            // No conflict found yet, check the dependencies
                            stack.extend(self.graph.edges(node).map(Op::CheckPackage));
                        }
                    }
                }
                Op::DetectConflicts(edge) => {
                    let node = edge.target();
                    let grouped_edges =
                        self.graph.edges(node).group_by(|e| &e.weight().requirement);
                    for (_, mut group) in &grouped_edges {
                        // If no edges are installable, then the package is not installable
                        if group.all(|edge| edges_with_conflicts.contains_key(&edge.id())) {
                            edges_with_conflicts.insert(edge.id(), edge);
                        }
                    }
                }
            }
        }

        // Don't forget to add the root edges themselves, if they are conflicting
        edges_with_conflicts.extend(
            self.graph
                .edges(root_node)
                .filter(|e| e.weight().status == EdgeStatus::Conflict)
                .map(|edge| (edge.id(), edge)),
        );

        if edges_with_conflicts.is_empty() {
            panic!("No errors!");
        }

        // ---
        // Step 2: collect the results in a tree for easy formatting
        // ---
        let mut error = DisplayError {
            root_requirements: Vec::new(),
        };
        let top_level_edges = self
            .graph
            .edges(root_node)
            .group_by(|e| e.weight().requirement.clone());

        for (requirement, candidates) in top_level_edges.into_iter() {
            let req = self.get_display_requirement(
                &|edge| edges_with_conflicts.contains_key(&edge),
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
        has_conflict: &impl Fn(EdgeIndex) -> bool,
        display_candidate: &impl Fn(TCandidate) -> String,
        display_requirement: &impl Fn(TRequirement) -> String,
        name: String,
        candidate_edges: Vec<EdgeReference<Edge<TRequirement>>>,
    ) -> DisplayRequirement {
        let mut candidates = candidate_edges
            .into_iter()
            .flat_map(|edge| {
                self.get_display_candidate(
                    has_conflict,
                    display_candidate,
                    display_requirement,
                    edge,
                )
            })
            .collect::<Vec<_>>();

        candidates.sort_by_key(|c| c.installable);

        DisplayRequirement::new(name, candidates)
    }

    fn get_display_candidate(
        &self,
        has_conflict: &impl Fn(EdgeIndex) -> bool,
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
                        has_conflict,
                        display_candidate,
                        display_requirement,
                        display_requirement(requirement),
                        edges.collect(),
                    ));
                }

                Some(DisplayCandidate {
                    name: display_candidate(c.clone()),
                    installable: !has_conflict(edge_to_candidate.id()),
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
                    format!(r#"{node1_name} -> {node2_name}[color={color}, label="{label}"];"#);
                buf.push_str(&line);
                buf.push('\n');
            }
        }
        buf.push('}');

        buf
    }
}