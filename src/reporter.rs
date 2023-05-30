use crate::resolver::ResolutionState;
use crate::RequirementInformation;
use std::marker::PhantomData;

pub trait Reporter {
    type Requirement;
    type Candidate;
    type Identifier;

    /// Called before the resolution starts
    fn starting(&self) {}

    /// Called before each resolution round
    fn starting_round(&self, _index: u64) {}

    /// Called after each resolution round, except in the last round (use [`Reporter::ending`] for that)
    fn ending_round(&self, _index: u64) {}

    /// Called after resolution ends successfully
    fn ending(
        &self,
        _state: &ResolutionState<Self::Requirement, Self::Candidate, Self::Identifier>,
    ) {
    }

    /// Called when adding a new requirement to the resolve criteria
    fn adding_requirement(
        &self,
        _requirement: &RequirementInformation<Self::Requirement, Self::Candidate>,
    ) {
    }

    /// Called when starting an attempt at resolving conflicts
    fn resolving_conflicts(
        &self,
        _causes: &[RequirementInformation<Self::Requirement, Self::Candidate>],
    ) {
    }

    fn backtracked(&self, _steps: u64) {}

    /// Called when adding a candidate to the potential solution
    fn pinning(&self, _candidate: Self::Candidate) {}
}

pub struct NoOpReporter<TRequirement, TCandidate, TIdentifier> {
    phantom: PhantomData<(TRequirement, TCandidate, TIdentifier)>,
}

impl<TRequirement, TCandidate, TIdentifier> Default
    for NoOpReporter<TRequirement, TCandidate, TIdentifier>
{
    fn default() -> Self {
        Self {
            phantom: PhantomData::default(),
        }
    }
}

impl<TRequirement, TCandidate, TIdentifier> Reporter
    for NoOpReporter<TRequirement, TCandidate, TIdentifier>
{
    type Requirement = TRequirement;
    type Candidate = TCandidate;
    type Identifier = TIdentifier;
}
