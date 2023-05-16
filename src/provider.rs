use std::collections::HashMap;
use std::hash::Hash;

use crate::resolver::{Criterion, RequirementInformation};

pub trait Provider {
    type Candidate: Copy;
    type Requirement: Copy;
    type Identifier: Copy + Hash + Eq;

    /// Retrieve the identifier of a candidate
    fn identify_candidate(&self, candidate: Self::Candidate) -> Self::Identifier;

    /// Retrieve the identifier of a requirement
    fn identify_requirement(&self, requirement: Self::Requirement) -> Self::Identifier;

    /// Produce a sort key for the given requirement (identified by `identifier`).
    ///
    /// The lower the return value, the more preferred the requirement is (i.e. it will be resolved
    /// before less-preferred requirements).
    ///
    /// This method provides loads of information, in case you need it to determine the
    /// requirement's preference. There is no need to actually use all information, though. In fact,
    /// the default implementation determines preference purely based on the amount of candidates
    /// for the requirement.
    fn get_preference(
        &self,
        identifier: Self::Identifier,
        _resolutions: &HashMap<Self::Identifier, Self::Candidate>,
        criteria: &HashMap<Self::Identifier, Criterion<Self::Requirement, Self::Candidate>>,
        _backtrack_causes: &[RequirementInformation<Self::Requirement, Self::Candidate>],
    ) -> u64 {
        criteria[&identifier].candidates.len() as u64
    }

    /// Produce a vector of candidates that should be considered when resolving the given
    /// requirement (identified by `identifier`).
    ///
    /// This method provides loads of information, in case you need it to determine the
    /// requirement's candidates. There is no need to actually use all information, though. It is
    /// often enough to have a look only at the requirements and incompatibilities associated to the
    /// provided identifier (e.g. `requirements[&identifier]` and `incompatibilities[&identifier]`),
    /// without taking the rest into account.
    fn find_matches(
        &self,
        identifier: Self::Identifier,
        requirements: HashMap<Self::Identifier, Vec<Self::Requirement>>,
        incompatibilities: HashMap<Self::Identifier, Vec<Self::Candidate>>,
    ) -> Vec<Self::Candidate>;

    /// Whether the candidate satisfies the requirement
    fn is_satisfied_by(&self, requirement: Self::Requirement, candidate: Self::Candidate) -> bool;

    /// Produce a vector of requirements that represent a candidate's dependencies
    fn get_dependencies(&self, candidate: Self::Candidate) -> Vec<Self::Requirement>;
}
