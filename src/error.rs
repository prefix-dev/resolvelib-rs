use crate::explored_space::ExploredSpace;
use crate::RequirementInformation;
use thiserror::Error;

#[derive(Error)]
pub enum ResolutionError<TRequirement, TCandidate> {
    #[error("resolution impossible")]
    ResolutionImpossible(ResolutionImpossible<TRequirement, TCandidate>),
    #[error("resolution too deep")]
    ResolutionTooDeep(u64),
}

pub struct ResolutionImpossible<TRequirement, TCandidate> {
    graph: ExploredSpace<TRequirement, TCandidate>,
    unsatisfied: Vec<RequirementInformation<TRequirement, TCandidate>>,
}

impl<TRequirement, TCandidate> ResolutionImpossible<TRequirement, TCandidate> {
    pub(crate) fn new(
        graph: ExploredSpace<TRequirement, TCandidate>,
        unsatisfied: Vec<RequirementInformation<TRequirement, TCandidate>>,
    ) -> Self {
        Self { graph, unsatisfied }
    }

    pub fn unsatisfied_requirements(&self) -> &[RequirementInformation<TRequirement, TCandidate>] {
        &self.unsatisfied
    }

    pub fn graph(&self) -> &ExploredSpace<TRequirement, TCandidate> {
        &self.graph
    }
}
