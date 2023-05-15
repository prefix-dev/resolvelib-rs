mod provider;
mod resolver;

pub use provider::{Matches, Provider, RequirementInformation};
pub use resolver::{Criterion, ResolutionError, ResolutionResult, Resolver};
