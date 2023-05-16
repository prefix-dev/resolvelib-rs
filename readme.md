# resovelib-rs

Rust port of [resolvelib](https://github.com/sarugaku/resolvelib). Props to the authors who wrote
such clear and concise code!

This library provides two data types:

* `Resolver`: a struct that drives dependency resolution
* `Provider`: a trait with methods to retrieve information about dependencies

Note that this library is a low-level building block. You will need to create a custom provider to
use it in a real-world scenario. Check out [in_memory_provider.rs](tests/in_memory_provider.rs) for
an example.

## Terminology

* Candidate: a concrete description of a package that can be installed (e.g. libfoo 2.3)
* Requirement: an abstract description of a package that should be resolved (e.g. any version of libfoo)
* Identifier: the name that identifies both a requirement and the candidate (e.g. libfoo)
