use std::collections::{HashMap, HashSet};
use std::ops::Range;

use resolvelib_rs::{Criterion, Provider, RequirementInformation, ResolutionError, Resolver};

#[derive(Debug, PartialEq, Eq)]
struct Candidate {
    package_name: String,
    version: u64,
    deps: Vec<Requirement>,
}

#[derive(Debug, PartialEq, Eq)]
struct Requirement {
    package_name: String,
    specifier: Range<u64>,
}

#[derive(Default)]
struct InMemoryProvider<'a> {
    candidates: HashMap<(&'a str, u64), &'a Candidate>,
    requirements: Vec<&'a Requirement>,
}

impl<'a> InMemoryProvider<'a> {
    fn from_requirements_and_candidates(
        requirements: &'a [Requirement],
        candidates: &'a [Candidate],
    ) -> Self {
        InMemoryProvider {
            requirements: requirements.iter().collect(),
            candidates: candidates
                .iter()
                .map(|c| ((c.package_name.as_str(), c.version), c))
                .collect(),
        }
    }

    fn register_candidate(&mut self, candidate: &'a Candidate) {
        self.candidates.insert(
            (candidate.package_name.as_str(), candidate.version),
            candidate,
        );
    }

    fn register_requirement(&mut self, requirement: &'a Requirement) {
        self.requirements.push(requirement);
    }
}

impl<'a> Provider for InMemoryProvider<'a> {
    type Candidate = &'a Candidate;
    type Requirement = &'a Requirement;
    type Identifier = &'a str;

    fn identify_candidate(&self, candidate: Self::Candidate) -> Self::Identifier {
        &candidate.package_name
    }

    fn identify_requirement(&self, requirement: Self::Requirement) -> Self::Identifier {
        &requirement.package_name
    }

    fn get_preference(
        &self,
        _identifier: Self::Identifier,
        _resolutions: &HashMap<Self::Identifier, Self::Candidate>,
        criteria: &HashMap<Self::Identifier, Criterion<Self::Requirement, Self::Candidate>>,
        _backtrack_causes: &[RequirementInformation<Self::Requirement, Self::Candidate>],
    ) -> u64 {
        // Requirements with less candidates are picked to be resolved first
        criteria.len() as u64
    }

    fn find_matches(
        &self,
        identifier: Self::Identifier,
        requirements: HashMap<Self::Identifier, Vec<Self::Requirement>>,
        incompatibilities: HashMap<Self::Identifier, Vec<Self::Candidate>>,
    ) -> Vec<Self::Candidate> {
        // Find all possible candidates that satisfy the given constraints
        let requirements = &requirements[&identifier];

        // For each requirement, derive candidates
        let mut candidates = Vec::new();
        for requirement in requirements {
            let incompatibilities = &incompatibilities[requirement.package_name.as_str()];
            let incompatible_versions: HashSet<_> =
                incompatibilities.iter().map(|i| i.version).collect();

            // Consider only candidates that actually exist and that are not incompatible
            let new_candidates = requirement
                .specifier
                .clone()
                .rev() // Highest versions come first so they are preferred (the returned candidates should be ordered by preference)
                .filter_map(|version| {
                    self.candidates
                        .get(&(requirement.package_name.as_str(), version))
                })
                .filter(|candidate| !incompatible_versions.contains(&candidate.version));

            candidates.extend(new_candidates);
        }

        candidates
    }

    fn is_satisfied_by(&self, requirement: Self::Requirement, candidate: Self::Candidate) -> bool {
        // The candidate is guaranteed to have been generated from the requirement, so we
        // only need to check the version specifier
        assert_eq!(requirement.package_name, candidate.package_name);
        requirement.specifier.contains(&candidate.version)
    }

    fn get_dependencies(&self, candidate: Self::Candidate) -> Vec<Self::Requirement> {
        candidate.deps.iter().collect()
    }
}

#[test]
fn resolve_empty() {
    let p = InMemoryProvider::default();
    let resolver = Resolver::new(p);
    let result = resolver.resolve(Vec::new()).unwrap();

    assert_eq!(result.mapping.len(), 0);
    assert_eq!(result.criteria.len(), 0);
    assert_eq!(result.graph.node_count(), 1);
}

#[test]
fn resolve_single() -> anyhow::Result<()> {
    // What the user wants to install
    let req = Requirement {
        package_name: "python".to_string(),
        specifier: 5..10,
    };

    // Available packages
    let p1 = Candidate {
        package_name: "python".to_string(),
        version: 9,
        deps: Vec::new(),
    };
    let p2 = Candidate {
        package_name: "python".to_string(),
        version: 10,
        deps: Vec::new(),
    };

    // Register them in the provider
    let mut p = InMemoryProvider::default();
    p.register_requirement(&req);
    p.register_candidate(&p1);
    p.register_candidate(&p2);

    // Resolve!
    let resolver = Resolver::new(p);
    let result = resolver.resolve(vec![&req]).unwrap();

    // Assert
    assert_eq!(result.mapping.len(), 1);

    let found_candidate = result.mapping["python"];
    assert_eq!(found_candidate.package_name, "python");
    assert_eq!(found_candidate.version, 9);

    Ok(())
}

#[test]
fn resolve_non_existent() {
    let req = Requirement {
        package_name: "python".to_string(),
        specifier: 0..10,
    };

    let mut p = InMemoryProvider::default();
    p.register_requirement(&req);

    let resolver = Resolver::new(p);
    let result = resolver.resolve(vec![&req]);

    assert!(result.is_err());
    let err = result.err().unwrap();

    if let ResolutionError::ResolutionImpossible(candidates) = err {
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].parent, None);
        assert_eq!(candidates[0].requirement.package_name, "python");
        assert_eq!(candidates[0].requirement.specifier, 0..10);
    } else {
        panic!("Wrong error type")
    }
}

#[test]
fn resolve_unsatisfiable_root() {
    let req = Requirement {
        package_name: "python".to_string(),
        specifier: 0..10,
    };

    let package = Candidate {
        package_name: "python".to_string(),
        version: 42,
        deps: Vec::new(),
    };

    let mut p = InMemoryProvider::default();
    p.register_requirement(&req);
    p.register_candidate(&package);

    let resolver = Resolver::new(p);
    let result = resolver.resolve(vec![&req]);

    assert!(result.is_err());
    let err = result.err().unwrap();

    if let ResolutionError::ResolutionImpossible(candidates) = err {
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].parent, None);
        assert_eq!(candidates[0].requirement.package_name, "python");
        assert_eq!(candidates[0].requirement.specifier, 0..10);
    } else {
        panic!("Wrong error type")
    }
}

#[test]
fn resolve_unsatisfiable_dep() {
    let req = Requirement {
        package_name: "python".to_string(),
        specifier: 0..10,
    };

    let package = Candidate {
        package_name: "python".to_string(),
        version: 8,
        deps: vec![Requirement {
            package_name: "foo".to_string(),
            specifier: 2..4,
        }],
    };

    let mut p = InMemoryProvider::default();
    p.register_requirement(&req);
    p.register_candidate(&package);

    let resolver = Resolver::new(p);
    let result = resolver.resolve(vec![&req]);

    assert!(result.is_err());
    let err = result.err().unwrap();

    if let ResolutionError::ResolutionImpossible(candidates) = err {
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].parent.unwrap(), &package);
        assert_eq!(candidates[0].requirement.package_name, "foo");
        assert_eq!(candidates[0].requirement.specifier, 2..4);
    } else {
        panic!("Wrong error type")
    }
}

#[test]
fn resolve_complex() {
    let reqs = vec![
        Requirement {
            package_name: "python".to_string(),
            specifier: 0..10,
        },
        Requirement {
            package_name: "some-lib".to_string(),
            specifier: 12..15,
        },
    ];

    let packages = vec![
        // Available versions of python
        Candidate {
            package_name: "python".to_string(),
            version: 6,
            deps: vec![Requirement {
                package_name: "foo".to_string(),
                specifier: 2..3,
            }],
        },
        Candidate {
            package_name: "python".to_string(),
            version: 8,
            deps: vec![Requirement {
                package_name: "foo".to_string(),
                specifier: 2..4,
            }],
        },
        // Available versions of foo
        Candidate {
            package_name: "foo".to_string(),
            version: 2,
            deps: Vec::new(),
        },
        Candidate {
            package_name: "foo".to_string(),
            version: 3,
            deps: Vec::new(),
        },
        // Available versions of some-lib
        Candidate {
            package_name: "some-lib".to_string(),
            version: 12,
            deps: vec![Requirement {
                package_name: "python".to_string(),
                specifier: 5..7,
            }],
        },
        Candidate {
            package_name: "some-lib".to_string(),
            version: 15,
            deps: vec![Requirement {
                package_name: "python".to_string(),
                specifier: 8..10,
            }],
        },
    ];

    let p = InMemoryProvider::from_requirements_and_candidates(&reqs, &packages);
    let resolver = Resolver::new(p);
    let result = resolver.resolve(reqs.iter().collect());
    let result = result.unwrap();

    assert_eq!(result.mapping.len(), 3);
    assert_eq!(result.criteria.len(), 3);
    assert_eq!(result.graph.node_count(), 4);

    // Expected mappings
    assert_eq!(result.mapping["python"].version, 6);
    assert_eq!(result.mapping["foo"].version, 2);
    assert_eq!(result.mapping["some-lib"].version, 12);

    // Python criterion
    let python_c = &result.criteria["python"];
    assert_eq!(python_c.candidates.len(), 1);
    assert_eq!(python_c.information.len(), 2);
    assert_eq!(
        python_c.information[0]
            .parent
            .map(|p| p.package_name.as_str()),
        None
    );
    assert_eq!(
        python_c.information[1]
            .parent
            .map(|p| p.package_name.as_str()),
        Some("some-lib")
    );
    assert_eq!(python_c.incompatibilities.len(), 0);

    // Graph, topologically sorted (installation order would be from right to left)
    let topo_sorted = petgraph::algo::toposort(&result.graph, None).unwrap();
    assert_eq!(
        topo_sorted,
        &[None, Some("some-lib"), Some("python"), Some("foo")]
    );
}
