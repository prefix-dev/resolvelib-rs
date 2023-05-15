use std::collections::HashMap;

use crate::resolver::Criterion;

#[derive(Clone, Debug)]
pub struct RequirementInformation<TRequirement, TCandidate> {
    pub requirement: TRequirement,
    pub parent: Option<TCandidate>,
}

pub struct Matches<TCandidate> {
    pub candidates: Vec<TCandidate>,
}

impl<TCandidate> Matches<TCandidate>
where
    TCandidate: Copy,
{
    pub fn iter(&self) -> impl Iterator<Item = TCandidate> + '_ {
        self.candidates.iter().copied()
    }
}

pub trait Provider {
    type Candidate: Copy;
    type Requirement: Copy;
    type Identifier: Copy;

    fn identify_candidate(&self, candidate: Self::Candidate) -> Self::Identifier;
    fn identify_requirement(&self, requirement: Self::Requirement) -> Self::Identifier;
    fn get_preference(
        &self,
        identifier: Self::Identifier,
        resolutions: &HashMap<Self::Identifier, Self::Candidate>,
        candidates: &HashMap<Self::Identifier, Criterion<Self::Requirement, Self::Candidate>>,
        backtrack_causes: &[RequirementInformation<Self::Requirement, Self::Candidate>],
    ) -> u64;
    fn find_matches(
        &self,
        identifier: Self::Identifier,
        requirements: HashMap<Self::Identifier, Vec<Self::Requirement>>,
        incompatibilities: HashMap<Self::Identifier, Vec<Self::Candidate>>,
    ) -> Matches<Self::Candidate>;
    fn is_satisfied_by(&self, requirement: Self::Requirement, candidate: Self::Candidate) -> bool;
    fn get_dependencies(&self, candidate: Self::Candidate) -> Vec<Self::Requirement>;
}
