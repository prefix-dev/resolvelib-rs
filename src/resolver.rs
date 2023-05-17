use petgraph::graphmap::DiGraphMap;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use thiserror::Error;

use crate::provider::Provider;

pub struct ResolutionResult<TRequirement, TCandidate, TIdentifier> {
    pub mapping: HashMap<TIdentifier, TCandidate>,
    pub graph: DiGraphMap<Option<TIdentifier>, ()>,
    pub criteria: HashMap<TIdentifier, Criterion<TRequirement, TCandidate>>,
}

#[derive(Clone)]
pub struct Criterion<TRequirement, TCandidate> {
    pub candidates: Vec<TCandidate>,
    pub information: Vec<RequirementInformation<TRequirement, TCandidate>>,
    pub incompatibilities: Vec<TCandidate>,
}

impl<TRequirement, TCandidate> Default for Criterion<TRequirement, TCandidate> {
    fn default() -> Self {
        Self {
            candidates: Vec::new(),
            information: Vec::new(),
            incompatibilities: Vec::new(),
        }
    }
}

impl<TRequirement, TCandidate> Criterion<TRequirement, TCandidate>
where
    TRequirement: Copy,
    TCandidate: Copy,
{
    fn iter_requirement(&self) -> impl Iterator<Item = TRequirement> + '_ {
        self.information.iter().map(|i| i.requirement)
    }

    fn iter_parent(&self) -> impl Iterator<Item = Option<TCandidate>> + '_ {
        self.information.iter().map(|i| i.parent)
    }
}

#[derive(Error, Debug)]
pub enum ResolutionError<TRequirement, TCandidate> {
    #[error("resolution impossible")]
    ResolutionImpossible(Vec<RequirementInformation<TRequirement, TCandidate>>),
    #[error("resolution too deep")]
    ResolutionTooDeep(u64),
}

#[derive(Default, Clone)]
pub struct ResolutionState<TRequirement, TCandidate, TIdentifier> {
    mapping: HashMap<TIdentifier, TCandidate>,
    pinned_candidate_stack: Vec<TIdentifier>,
    criteria: HashMap<TIdentifier, Criterion<TRequirement, TCandidate>>,
    backtrack_causes: Vec<RequirementInformation<TRequirement, TCandidate>>,
}

impl<TRequirement, TCandidate, TIdentifier> ResolutionState<TRequirement, TCandidate, TIdentifier>
where
    TRequirement: Copy,
    TCandidate: Copy,
    TIdentifier: Copy + Hash + Ord,
{
    fn build_result<P>(
        mut self,
        provider: &P,
    ) -> ResolutionResult<TRequirement, TCandidate, TIdentifier>
    where
        P: Provider<Requirement = TRequirement, Candidate = TCandidate, Identifier = TIdentifier>,
    {
        let mut graph = DiGraphMap::new();
        graph.add_node(None);

        // It looks like each criterion represents a single resolved package
        let mut connected = HashSet::new();
        connected.insert(None);

        for (&key, criterion) in &self.criteria {
            // Skip the criterion if it cannot be traced back to the root
            if !Self::has_route_to_root(provider, &self.criteria, Some(key), &mut connected) {
                continue;
            }

            // Add the current node if it isn't part of the graph yet
            if !graph.contains_node(Some(key)) {
                graph.add_node(Some(key));
            }

            // Add the parents of the node
            for p in criterion.iter_parent() {
                let p_id = p.map(|p| provider.identify_candidate(p));
                if !graph.contains_node(p_id) {
                    graph.add_node(p_id);
                }

                graph.add_edge(p_id, Some(key), ());
            }
        }

        self.mapping.retain(|&k, _| connected.contains(&Some(k)));

        ResolutionResult {
            mapping: self.mapping,
            graph,
            criteria: self.criteria,
        }
    }

    fn has_route_to_root<P>(
        provider: &P,
        criteria: &HashMap<TIdentifier, Criterion<TRequirement, TCandidate>>,
        key: Option<TIdentifier>,
        connected: &mut HashSet<Option<TIdentifier>>,
    ) -> bool
    where
        P: Provider<Requirement = TRequirement, Candidate = TCandidate, Identifier = TIdentifier>,
    {
        if connected.contains(&key) {
            return true;
        }

        // If the key was None, it would be considered connected
        let key = key.unwrap();

        if let Some(criterion) = criteria.get(&key) {
            for p in criterion.iter_parent() {
                let parent_id = p.map(|parent| provider.identify_candidate(parent));
                if connected.contains(&parent_id)
                    || Self::has_route_to_root(provider, criteria, parent_id, connected)
                {
                    connected.insert(Some(key));
                    return true;
                }
            }
        }

        false
    }
}

pub struct Resolution<P: Provider> {
    state: ResolutionState<P::Requirement, P::Candidate, P::Identifier>,
    states: Vec<ResolutionState<P::Requirement, P::Candidate, P::Identifier>>,
    provider: P,
}

impl<P: Provider> Resolution<P>
where
    P::Requirement: Copy,
    P::Candidate: Copy,
    P::Identifier: Copy + Hash + Eq,
{
    fn new(provider: P) -> Self {
        Self {
            state: ResolutionState {
                mapping: HashMap::new(),
                criteria: HashMap::new(),
                backtrack_causes: Vec::new(),
                pinned_candidate_stack: Vec::new(),
            },
            states: Vec::new(),
            provider,
        }
    }

    fn resolve(
        mut self,
        requirements: Vec<P::Requirement>,
        max_rounds: u64,
    ) -> Result<
        (
            P,
            ResolutionState<P::Requirement, P::Candidate, P::Identifier>,
        ),
        ResolutionError<P::Requirement, P::Candidate>,
    > {
        // Initialize the root state
        for r in requirements {
            Resolution::add_to_criteria(&self.provider, &mut self.state.criteria, r, None)
                .map_err(|criterion| {
                    ResolutionError::ResolutionImpossible(
                        criterion
                            .iter_requirement()
                            .map(|r| RequirementInformation {
                                requirement: r,
                                parent: None,
                            })
                            .collect(),
                    )
                })?;
        }

        // The root state is saved as a sentinel so the first ever pin can have
        // something to backtrack to if it fails. The root state is basically
        // pinning the virtual "root" package in the graph.
        self.push_new_state();

        for _ in 0..max_rounds {
            let unsatisfied_names: HashSet<_> = self
                .state
                .criteria
                .iter()
                .filter(|(id, criterion)| !self.is_current_pin_satisfying(id, criterion))
                .map(|(&id, _)| id)
                .collect();

            // All criteria are accounted for. Nothing more to pin, we are done!
            if unsatisfied_names.is_empty() {
                return Ok((self.provider, self.state));
            }

            // Keep track of satisfied names to calculate diff after pinning
            let satisfied_names = self
                .state
                .criteria
                .keys()
                .cloned()
                .filter(|name| !unsatisfied_names.contains(name))
                .collect::<HashSet<_>>();

            // Choose the most preferred unpinned criterion to try.
            let &name = unsatisfied_names
                .iter()
                .min_by_key(|&&x| self.get_preference(x))
                .unwrap();

            let result = self.attempt_to_pin_criterion(name);
            if let Err(failure_causes) = result {
                let causes: Vec<_> = failure_causes
                    .iter()
                    .flat_map(|c| &c.information)
                    .cloned()
                    .collect();

                // Backjump if pinning fails. The backjump process puts us in
                // an unpinned state, so we can work on it in the next round.
                // It will return an error if there are dead ends everywhere,
                // in which case we give up.
                let success = self.backjump(&causes)?;
                self.state.backtrack_causes = causes;

                if !success {
                    return Err(ResolutionError::ResolutionImpossible(
                        self.state.backtrack_causes.clone(),
                    ));
                }
            } else {
                // discard as information sources any invalidated names
                // (unsatisfied names that were previously satisfied)
                let newly_unsatisfied_names = self
                    .state
                    .criteria
                    .iter()
                    .filter(|(k, v)| {
                        satisfied_names.contains(k) && !self.is_current_pin_satisfying(k, v)
                    })
                    .map(|(&k, _)| k)
                    .collect();

                Resolution::remove_information_from_criteria(
                    &self.provider,
                    &mut self.state.criteria,
                    &newly_unsatisfied_names,
                );

                // Pinning was successful. Push a new state to do another pin.
                self.push_new_state()
            }
        }

        Err(ResolutionError::ResolutionTooDeep(max_rounds))
    }

    fn remove_information_from_criteria(
        provider: &P,
        criteria: &mut HashMap<P::Identifier, Criterion<P::Requirement, P::Candidate>>,
        parents: &HashSet<P::Identifier>,
    ) {
        // Remove information from parents of criteria.
        //
        // Concretely, removes all values from each criterion's ``information``
        // field that have one of ``parents`` as provider of the requirement.
        //
        // :param criteria: The criteria to update.
        // :param parents: Identifiers for which to remove information from all criteria.
        if parents.is_empty() {
            return;
        }

        for criterion in criteria.values_mut() {
            criterion.information.retain(|information| {
                information.parent.map_or(true, |parent| {
                    let id = provider.identify_candidate(parent);
                    !parents.contains(&id)
                })
            })
        }
    }

    /// Adds the provided requirement to the criteria
    ///
    /// If a criterion already exists for the package identified by the requirement, it will be
    /// updated to include the new requirement. If no criterion exists yet, it will be created.
    ///
    /// The candidate list of the criterion becomes the result of [`Provider::find_matches`]
    fn add_to_criteria(
        provider: &P,
        criteria: &mut HashMap<P::Identifier, Criterion<P::Requirement, P::Candidate>>,
        requirement: P::Requirement,
        parent: Option<P::Candidate>,
    ) -> Result<(), Criterion<P::Requirement, P::Candidate>> {
        let identifier = provider.identify_requirement(requirement);

        let mut all_requirements: HashMap<_, _> = criteria
            .iter()
            .map(|(&id, criterion)| (id, criterion.iter_requirement().collect()))
            .collect();
        all_requirements
            .entry(identifier)
            .or_insert(Vec::new())
            .push(requirement);

        let mut all_incompatibilities: HashMap<_, _> = criteria
            .iter()
            .map(|(&id, criterion)| (id, criterion.incompatibilities.clone()))
            .collect();
        all_incompatibilities
            .entry(identifier)
            .or_insert(Vec::new());

        let candidates = provider.find_matches(identifier, all_requirements, all_incompatibilities);

        // Update the criterion in the map, with the new information and candidates
        let criterion = criteria.entry(identifier).or_insert(Criterion::default());
        criterion.candidates = candidates;
        criterion.information.push(RequirementInformation {
            requirement,
            parent,
        });

        if criterion.candidates.is_empty() {
            Err(criterion.clone())
        } else {
            Ok(())
        }
    }

    /// Push a new state into history
    ///
    /// This new state will be used to hold resolution results of the next coming round
    fn push_new_state(&mut self) {
        // The new state is based off the current one
        let new_state = self.state.clone();

        // Push the current state into history (the new state will now be the working state)
        let old_state = std::mem::replace(&mut self.state, new_state);
        self.states.push(old_state);
    }

    /// Restore a state from history
    fn restore_state(&mut self) {
        self.state = self.states.last().unwrap().clone();
    }

    fn is_current_pin_satisfying(
        &self,
        id: &P::Identifier,
        criterion: &Criterion<P::Requirement, P::Candidate>,
    ) -> bool {
        if let Some(&current_pin) = self.state.mapping.get(id) {
            criterion
                .iter_requirement()
                .all(|r| self.provider.is_satisfied_by(r, current_pin))
        } else {
            false
        }
    }

    fn get_preference(&self, id: P::Identifier) -> u64 {
        self.provider.get_preference(
            id,
            &self.state.mapping,
            &self.state.criteria,
            &self.state.backtrack_causes,
        )
    }

    /// Attempts to find a suitable candidate for the package identified by `id`
    ///
    /// If a candidate is found, update the state and return `Ok`. Otherwise, return
    /// an `Err` with the criteria that caused candidates to be discarded
    fn attempt_to_pin_criterion(
        &mut self,
        id: P::Identifier,
    ) -> Result<(), Vec<Criterion<P::Requirement, P::Candidate>>> {
        let criterion = &self.state.criteria[&id];

        let mut causes = Vec::new();
        for &candidate in &criterion.candidates {
            let mut updated_criteria = self.state.criteria.clone();
            let result =
                Resolution::update_criteria(&self.provider, &mut updated_criteria, candidate);
            if let Err(e) = result {
                causes.push(e);
                continue;
            }

            // Check the newly-pinned candidate actually works. This should
            // always pass under normal circumstances, but in the case of a
            // faulty provider, we will raise an error to notify the implementer
            // to fix find_matches() and/or is_satisfied_by().
            let mut unsatisfied = Vec::new();
            for r in criterion.iter_requirement() {
                if !self.provider.is_satisfied_by(r, candidate) {
                    unsatisfied.push(r);
                }
            }
            if !unsatisfied.is_empty() {
                self.provider
                    .on_inconsistent_candidate(candidate, unsatisfied);
                panic!("inconsistent candidate");
            }

            // Add/update criteria
            for (id, criterion) in updated_criteria {
                self.state.criteria.insert(id, criterion);
            }

            // Put newly-pinned candidate at the end. This is essential because
            // backtracking looks at this mapping to get the last pin.
            self.state.pinned_candidate_stack.push(id);

            // Keep track of the chosen candidates
            self.state.mapping.insert(id, candidate);

            return Ok(());
        }

        Err(causes)
    }

    /// Constrains the criteria to satisfy the candidate's dependencies
    ///
    /// If the result is unsatisfiable, returns an `Err` containing the first criterion that had no
    /// candidates left after being constrained
    fn update_criteria(
        provider: &P,
        criteria: &mut HashMap<P::Identifier, Criterion<P::Requirement, P::Candidate>>,
        candidate: P::Candidate,
    ) -> Result<(), Criterion<P::Requirement, P::Candidate>> {
        for requirement in provider.get_dependencies(candidate) {
            Resolution::add_to_criteria(provider, criteria, requirement, Some(candidate))?;
        }

        Ok(())
    }

    fn backjump(
        &mut self,
        causes: &[RequirementInformation<P::Requirement, P::Candidate>],
    ) -> Result<bool, ResolutionError<P::Requirement, P::Candidate>> {
        // When we enter here, the stack is like this::
        //
        //     [ state Z ]
        //     [ state Y ]
        //     [ state X ]
        //     .... earlier states are irrelevant.
        //
        // 1. No pins worked for Z, so it does not have a pin.
        // 2. We want to reset state Y to unpinned, and pin another candidate.
        // 3. State X holds what state Y was before the pin, but does not
        //    have the incompatibility information gathered in state Y.
        //
        // Each iteration of the loop will:
        //
        // 1.  Identify Z. The incompatibility is not always caused by the latest
        //     state. For example, given three requirements A, B and C, with
        //     dependencies A1, B1 and C1, where A1 and B1 are incompatible: the
        //     last state might be related to C, so we want to discard the
        //     previous state.
        // 2.  Discard Z.
        // 3.  Discard Y but remember its incompatibility information gathered
        //     previously, and the failure we're dealing with right now.
        // 4.  Push a new state Y' based on X, and apply the incompatibility
        //     information from Y to Y'.
        // 5a. If this causes Y' to conflict, we need to backtrack again. Make Y'
        //     the new Z and go back to step 2.
        // 5b. If the incompatibilities apply cleanly, end backtracking.
        let incompatible_candidates = causes
            .iter()
            .flat_map(|c| c.parent)
            .map(|c| self.provider.identify_candidate(c));

        let incompatible_reqs = causes
            .iter()
            .map(|c| self.provider.identify_requirement(c.requirement));

        let incompatible_deps: HashSet<_> =
            incompatible_candidates.chain(incompatible_reqs).collect();

        // Note: 1 less than in the Python code, because we are tracking the current state in its own field
        while self.states.len() >= 2 {
            // Ensure to backtrack to a state that caused the incompatibility
            let (broken_state, candidate_id, broken_candidate) = loop {
                // Retrieve the last candidate pin and known incompatibilities.
                if let Some(mut broken_state) = self.states.pop() {
                    if let Some(candidate_id) = broken_state.pinned_candidate_stack.pop() {
                        let candidate = broken_state.mapping[&candidate_id];
                        let mut current_dependencies = self
                            .provider
                            .get_dependencies(candidate)
                            .into_iter()
                            .map(|dep| self.provider.identify_requirement(dep));

                        let incompatible_state =
                            current_dependencies.any(|dep| incompatible_deps.contains(&dep));
                        if incompatible_state {
                            break (broken_state, candidate_id, candidate);
                        }

                        continue;
                    }
                }

                // Unable to backtrack anymore
                return Err(ResolutionError::ResolutionImpossible(causes.to_vec()));
            };

            let mut incompatibilities_from_broken: HashMap<_, _> = broken_state
                .criteria
                .into_iter()
                .map(|(key, value)| (key, value.incompatibilities))
                .collect();
            incompatibilities_from_broken
                .entry(candidate_id)
                .or_insert(Vec::new())
                .push(broken_candidate);

            self.restore_state();
            let success = self.patch_criteria(&incompatibilities_from_broken);

            // It works! Let's work on this new state.
            if success {
                return Ok(true);
            }
        }

        Ok(false)
    }

    fn patch_criteria<'a>(
        &mut self,
        incompatibilities_from_broken: &HashMap<P::Identifier, Vec<P::Candidate>>,
    ) -> bool
    where
        P::Candidate: 'a,
    {
        for (&k, incompatibilities) in incompatibilities_from_broken {
            if incompatibilities.is_empty() {
                continue;
            }

            let criterion = match self.state.criteria.get(&k) {
                Some(c) => c,
                None => continue,
            };

            // TODO: can we call find_matches without allocating?
            let requirements = self
                .state
                .criteria
                .iter()
                .map(|(&id, criterion)| (id, criterion.iter_requirement().collect::<Vec<_>>()))
                .collect();

            let mut all_incompatibilities: HashMap<_, _> = self
                .state
                .criteria
                .iter()
                .map(|(&id, criterion)| (id, criterion.incompatibilities.clone()))
                .collect();
            all_incompatibilities
                .entry(k)
                .or_insert(Vec::new())
                .extend(incompatibilities);

            let candidates = self
                .provider
                .find_matches(k, requirements, all_incompatibilities);
            if candidates.is_empty() {
                return false;
            }

            let incompatibilities = incompatibilities
                .iter()
                .cloned()
                .chain(criterion.incompatibilities.iter().cloned())
                .collect();

            // Now update the criterion with relevant incompatibilities and the resulting set of
            // candidates
            let criterion = self.state.criteria.get_mut(&k).unwrap();
            criterion.candidates = candidates;
            criterion.incompatibilities = incompatibilities;
        }

        true
    }
}

pub struct Resolver<P: Provider> {
    provider: P,
}

impl<P: Provider> Resolver<P>
where
    P::Requirement: Copy,
    P::Candidate: Copy,
    P::Identifier: Copy + Hash + Eq + Ord,
{
    pub fn new(provider: P) -> Self {
        Self { provider }
    }

    pub fn resolve(
        self,
        requirements: Vec<P::Requirement>,
    ) -> Result<
        ResolutionResult<P::Requirement, P::Candidate, P::Identifier>,
        ResolutionError<P::Requirement, P::Candidate>,
    > {
        self.resolve_bounded(requirements, 100)
    }

    pub fn resolve_bounded(
        self,
        requirements: Vec<P::Requirement>,
        max_rounds: u64,
    ) -> Result<
        ResolutionResult<P::Requirement, P::Candidate, P::Identifier>,
        ResolutionError<P::Requirement, P::Candidate>,
    > {
        let resolution = Resolution::new(self.provider);
        let (provider, state) = resolution.resolve(requirements, max_rounds)?;
        Ok(state.build_result(&provider))
    }
}

#[derive(Clone, Debug)]
pub struct RequirementInformation<TRequirement, TCandidate> {
    pub requirement: TRequirement,
    pub parent: Option<TCandidate>,
}
