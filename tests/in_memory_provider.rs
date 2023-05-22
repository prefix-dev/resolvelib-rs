use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Range;

use resolvelib_rs::{Provider, Reporter, ResolutionError, ResolutionResult, Resolver};

#[derive(Debug, PartialEq, Eq, Hash)]
struct Candidate {
    package_name: String,
    version: u64,
    deps: Vec<Requirement>,
    constraints: Vec<Requirement>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct Requirement {
    package_name: String,
    specifier: Range<u64>,
}

fn pkg(package_name: &str, version: u64, deps: Vec<Requirement>) -> Candidate {
    Candidate {
        package_name: package_name.to_string(),
        version,
        deps,
        constraints: Vec::new(),
    }
}

fn pkg2(
    package_name: &str,
    version: u64,
    deps: Vec<Requirement>,
    constraints: Vec<Requirement>,
) -> Candidate {
    Candidate {
        package_name: package_name.to_string(),
        version,
        deps,
        constraints,
    }
}

fn req(package_name: &str, specifier: Range<u64>) -> Requirement {
    Requirement {
        package_name: package_name.to_string(),
        specifier,
    }
}

struct TrackingReporter<'a> {
    operations: RefCell<Vec<Operation<'a>>>,
}

impl TrackingReporter<'_> {
    fn new() -> Self {
        Self {
            operations: RefCell::new(Vec::new()),
        }
    }
}

impl<'a> Reporter for TrackingReporter<'a> {
    type Requirement = &'a Requirement;
    type Candidate = &'a Candidate;
    type Identifier = &'a str;

    fn backtracked(&self, steps: u64) {
        self.operations
            .borrow_mut()
            .push(Operation::Backtrack(steps));
    }

    fn pinning(&self, candidate: Self::Candidate) {
        self.operations
            .borrow_mut()
            .push(Operation::PinCandidate(candidate));
    }
}

#[derive(Debug)]
enum Operation<'a> {
    PinCandidate(&'a Candidate),
    Backtrack(u64),
}

impl<'a> ToString for Operation<'a> {
    fn to_string(&self) -> String {
        use Operation::*;
        match self {
            Backtrack(steps) => format!("backtrack {steps}"),
            PinCandidate(candidate) => {
                format!("pin {}={}", candidate.package_name, candidate.version)
            }
        }
    }
}

#[derive(Default)]
struct InMemoryProvider<'a> {
    candidates: HashMap<(&'a str, u64), &'a Candidate>,
}

impl<'a> InMemoryProvider<'a> {
    fn from_candidates(candidates: &'a [Candidate]) -> Self {
        InMemoryProvider {
            candidates: candidates
                .iter()
                .map(|c| ((c.package_name.as_str(), c.version), c))
                .collect(),
        }
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

    fn find_matches(
        &self,
        identifier: Self::Identifier,
        requirements: &HashMap<Self::Identifier, Vec<Self::Requirement>>,
        incompatibilities: &HashMap<Self::Identifier, Vec<Self::Candidate>>,
    ) -> Vec<Self::Candidate> {
        // Find all possible candidates that satisfy the given constraints
        let requirements = &requirements[&identifier];

        // For each requirement, derive candidates
        let mut all_candidates = HashSet::new();
        let mut first_requirement = true;
        for requirement in requirements {
            let incompatibilities = &incompatibilities[requirement.package_name.as_str()];
            let incompatible_versions: HashSet<_> =
                incompatibilities.iter().map(|i| i.version).collect();

            // Consider only candidates that actually exist and that are not incompatible
            let new_candidates: HashSet<_> = requirement
                .specifier
                .clone()
                .rev() // Highest versions come first so they are preferred (the returned candidates should be ordered by preference)
                .filter_map(|version| {
                    self.candidates
                        .get(&(requirement.package_name.as_str(), version))
                })
                .filter(|candidate| !incompatible_versions.contains(&candidate.version))
                .cloned()
                .collect();

            if first_requirement {
                all_candidates = new_candidates;
            } else {
                all_candidates.retain(|c| new_candidates.contains(c));
            }

            first_requirement = false;
        }

        let mut all_candidates: Vec<_> = all_candidates.into_iter().collect();
        all_candidates.sort_by(|c1, c2| c2.version.cmp(&c1.version));

        println!("find_matches for {identifier}");
        println!("requirements:");
        for requirement in requirements {
            println!(
                " {} {}..{}",
                requirement.package_name, requirement.specifier.start, requirement.specifier.end
            );
        }
        println!("candidates:");
        for candidate in &all_candidates {
            println!(" {} {}", candidate.package_name, candidate.version)
        }

        let incompatibilities = &incompatibilities[&identifier];
        if !incompatibilities.is_empty() {
            println!("incompatible:");
            for candidate in incompatibilities {
                println!(" {} {}", candidate.package_name, candidate.version);
            }
        }

        all_candidates
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

    fn get_constraints(&self, candidate: Self::Candidate) -> Vec<Self::Requirement> {
        candidate.constraints.iter().collect()
    }

    fn on_inconsistent_candidate(
        &self,
        candidate: Self::Candidate,
        requirements: Vec<Self::Requirement>,
    ) {
        panic!("Inconsistent candidate: {candidate:?} does not satisfy {requirements:?}");
    }
}

fn resolve<'a>(
    reqs: &'a [Requirement],
    pkgs: &'a [Candidate],
) -> (
    ResolutionResult<&'a Requirement, &'a Candidate, &'a str>,
    Vec<Operation<'a>>,
) {
    let (result, operations) = try_resolve_and_report(reqs, pkgs);
    (result.unwrap(), operations)
}

fn try_resolve<'a>(
    reqs: &'a [Requirement],
    pkgs: &'a [Candidate],
) -> Result<
    ResolutionResult<&'a Requirement, &'a Candidate, &'a str>,
    ResolutionError<&'a Requirement, &'a Candidate>,
> {
    let (result, _) = try_resolve_and_report(reqs, pkgs);
    result
}

fn try_resolve_and_report<'a>(
    reqs: &'a [Requirement],
    pkgs: &'a [Candidate],
) -> (
    Result<
        ResolutionResult<&'a Requirement, &'a Candidate, &'a str>,
        ResolutionError<&'a Requirement, &'a Candidate>,
    >,
    Vec<Operation<'a>>,
) {
    let p = InMemoryProvider::from_candidates(pkgs);
    let r = TrackingReporter::new();
    let resolver = Resolver::new(&p, &r);
    let result = resolver.resolve(reqs.iter().collect());
    (result, r.operations.into_inner())
}

#[test]
fn resolve_empty() {
    let (result, ops) = resolve(&[], &[]);

    assert_eq!(ops.len(), 0);
    assert_eq!(result.mapping.len(), 0);
    assert_eq!(result.criteria.len(), 0);
    assert_eq!(result.graph.node_count(), 1);
}

#[test]
fn resolve_single() -> anyhow::Result<()> {
    let reqs = vec![req("python", 5..10)];
    let pkgs = vec![pkg("python", 9, vec![]), pkg("python", 10, vec![])];

    let (result, ops) = resolve(&reqs, &pkgs);

    // Operations
    check_ops(
        &ops,
        r"
        pin python=9
    ",
    );

    // Outcome
    assert_eq!(result.mapping.len(), 1);

    let found_candidate = result.mapping["python"];
    assert_eq!(found_candidate.package_name, "python");
    assert_eq!(found_candidate.version, 9);

    Ok(())
}

#[test]
fn resolve_non_existent() {
    let reqs = vec![req("python", 0..10)];
    let result = try_resolve(&reqs, &[]);

    assert!(result.is_err());
    let err = result.err().unwrap();

    if let ResolutionError::ResolutionImpossible(err) = err {
        let unsatisfied = err.unsatisfied_requirements();
        assert_eq!(unsatisfied.len(), 1);
        assert_eq!(unsatisfied[0].parent, None);
        assert_eq!(unsatisfied[0].requirement.package_name, "python");
        assert_eq!(unsatisfied[0].requirement.specifier, 0..10);
    } else {
        panic!("Wrong error type")
    }
}

#[test]
fn resolve_unsatisfiable_root() {
    let reqs = vec![req("python", 0..10)];
    let pkgs = vec![pkg("python", 42, vec![])];
    let result = try_resolve(&reqs, &pkgs);

    assert!(result.is_err());
    let err = result.err().unwrap();

    if let ResolutionError::ResolutionImpossible(err) = err {
        let unsatisfied = err.unsatisfied_requirements();
        assert_eq!(unsatisfied.len(), 1);
        assert_eq!(unsatisfied[0].parent, None);
        assert_eq!(unsatisfied[0].requirement.package_name, "python");
        assert_eq!(unsatisfied[0].requirement.specifier, 0..10);
    } else {
        panic!("Wrong error type")
    }
}

#[test]
fn resolve_unsatisfiable_dep() {
    let reqs = vec![req("python", 0..10)];
    let pkgs = vec![pkg("python", 8, vec![req("foo", 2..4)])];
    let (result, ops) = try_resolve_and_report(&reqs, &pkgs);

    assert_eq!(ops.len(), 0);
    assert!(result.is_err());
    let err = result.err().unwrap();

    if let ResolutionError::ResolutionImpossible(err) = err {
        let unsatisfied = err.unsatisfied_requirements();
        assert_eq!(unsatisfied.len(), 1);
        assert_eq!(unsatisfied[0].parent.unwrap(), &pkgs[0]);
        assert_eq!(unsatisfied[0].requirement.package_name, "foo");
        assert_eq!(unsatisfied[0].requirement.specifier, 2..4);
    } else {
        panic!("Wrong error type")
    }
}

#[test]
fn resolve_complex() {
    let reqs = vec![req("python", 0..10), req("some-lib", 12..15)];

    let pkgs = vec![
        // Available versions of python
        pkg("python", 6, vec![req("foo", 2..3)]),
        pkg("python", 8, vec![req("foo", 2..4)]),
        // Available versions of foo
        pkg("foo", 2, vec![]),
        pkg("foo", 3, vec![]),
        // Available versions of some-lib
        pkg("some-lib", 12, vec![req("python", 5..7)]),
        pkg("some-lib", 15, vec![req("python", 8..10)]),
    ];

    let (result, ops) = resolve(&reqs, &pkgs);
    check_ops(
        &ops,
        r"
        pin some-lib=12
        pin python=6
        pin foo=2
    ",
    );

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

#[test]
fn resolve_with_inactive_constraints() {
    let reqs = vec![req("A", 0..10)];

    let pkgs = vec![
        pkg("A", 5, vec![req("B", 0..10)]),
        pkg2("B", 2, vec![], vec![req("C", 0..10)]),
        pkg("C", 42, vec![]),
    ];

    // Package C is not required, so it won't be resolved
    let (result, _) = resolve(&reqs, &pkgs);
    assert_eq!(result.mapping["A"].version, 5);
    assert_eq!(result.mapping["B"].version, 2);
    assert!(!result.mapping.contains_key("C"));
}

#[test]
fn resolve_with_active_constraints() {
    let reqs = vec![req("A", 0..10)];

    let pkgs = vec![
        pkg("A", 5, vec![req("B", 0..10), req("C", 9..15)]),
        pkg2("B", 2, vec![], vec![req("C", 0..10)]),
        pkg("C", 12, vec![]),
        pkg("C", 9, vec![]),
    ];

    // Package C is required, so it will be constrained to 0..10
    let (result, _) = resolve(&reqs, &pkgs);
    assert_eq!(result.mapping["A"].version, 5);
    assert_eq!(result.mapping["B"].version, 2);
    assert_eq!(result.mapping["C"].version, 9);
}

#[test]
fn resolve_backtrack() {
    // This is the dependency tree:
    //
    //     A
    //    / \
    //   B   C
    //   |   |
    //   E   E
    //
    // B prefers the latest version of E, which will be picked first
    // C requires an older version of E, so it will cause a backtrack

    let reqs = vec![req("A", 0..10)];

    let packages = vec![
        // A
        pkg("A", 6, vec![req("B", 0..10), req("C", 0..10)]),
        // B
        pkg("B", 9, vec![req("E", 9..10)]),
        pkg("B", 8, vec![req("E", 8..9)]),
        // C
        pkg("C", 9, vec![req("E", 0..9)]),
        pkg("C", 8, vec![req("E", 0..9)]),
        pkg("C", 7, vec![req("E", 0..9)]),
        // E
        pkg("E", 9, vec![]),
        pkg("E", 8, vec![]),
    ];

    let (solution, ops) = resolve(&reqs, &packages);

    // Operations
    check_ops(
        &ops,
        r"
        pin A=6
        pin B=9
        pin E=9
        backtrack 2
        pin B=8
        pin E=8
        pin C=9
    ",
    );

    // Solution
    assert_eq!(solution.mapping["A"].version, 6);
    assert_eq!(solution.mapping["B"].version, 8);
    assert_eq!(solution.mapping["C"].version, 9);
    assert_eq!(solution.mapping["E"].version, 8);
}

fn check_ops(ops: &[Operation], expected: &str) {
    let expected: Vec<_> = expected
        .lines()
        .map(|l| l.trim())
        .filter(|l| !l.is_empty())
        .collect();
    for (op, &line) in ops.into_iter().zip(&expected) {
        let op_str = op.to_string();
        assert_eq!(op_str, line);
    }

    if expected.len() > ops.len() {
        panic!(
            "Expected {}, but found {} actual operations!",
            expected.len(),
            ops.len()
        );
    } else if expected.len() < ops.len() {
        panic!(
            "Operations match, but there are {} more actual operations. The next one is {}",
            ops.len() - expected.len(),
            ops[expected.len()].to_string()
        );
    }
}
