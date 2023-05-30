mod error;
mod explored_space;
mod provider;
mod reporter;
mod resolver;

pub use error::{ResolutionError, ResolutionImpossible};
pub use provider::{FindMatchesError, Provider};
pub use reporter::{NoOpReporter, Reporter};
pub use resolver::{
    Criterion, RequirementInformation, RequirementKind, ResolutionResult, Resolver,
};
