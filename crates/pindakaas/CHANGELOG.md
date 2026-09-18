# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.6.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.5.1...pindakaas-v0.6.0) - 2026-09-18

### Added

- [**breaking**] encode an aggregated constraint with a single encoder
- [**breaking**] add the polynomial watchdog encoding
- add generalized n-level modulo totalizer encoding
- recognise literals counted into an integer
- keep a linear constraint over literals in its literals
- ask an integer variable for the literals of its values
- encode a ternary inequality with the adder where it pays
- build a dense coefficient's product instead of carrying it
- make the sorting network's encoder reachable
- say once that an integer holds a value of its domain
- create and constrain integer variables from Python
- write linear expressions over integers as well as literals
- make the integer constraint interface public
- encode sorting networks over integer variables
- aggregate linear constraints into integer ones
- break linear constraints apart over integer terms
- encode pseudo-Boolean constraints as integer ones
- read a pseudo-Boolean group as the integer it already encodes
- decompose coefficients into shifts and adders
- encode linear constraints over integer variables
- add integer variables holding several Boolean encodings
- add product encoding for at-most-one constraints
- use declared bounds of log encodings during aggregation
- apply greatest common divisor during linear aggregation
- *(external-propagation)* streamline allocation in ExternalPropagation API

### Fixed

- read updated WCNF format
- pair a direct walk's literals with their values in any order
- release a domain borrow before splitting a variable
- decide a constraint by its bounds before decomposing it
- decide a linear constraint by the bounds of its whole sum
- pick the modulo totalizer's base by CaDiCaL cost, not clause count
- encode a count with any of the linear encodings
- read a direct-encoded term against the bound it was given
- leave a sorting network's comparators alone by default
- define the integer linear encoder over ternary constraints
- imply upper bound for groups of mutually exclusive terms
- re-enable already working testcases
- C robustness issues

### Other

- enumerate models through one helper
- return the value of an expression, not a Result
- [**breaking**] name LinExp::terms for the terms it returns
- borrow an integer variable's domain instead of cloning it
- [**breaking**] one handle for what a variable has already encoded
- reject a watchdog constraint its bounds already rule out
- let mixed radix share the short-constraint shortcut
- encode a short constraint as the addition it is
- share configuration and helpers between linear encoders
- skip formatting integer variable labels without tracing
- reuse existing helpers for bit widths and weights
- pair direct-encoding values with their literals
- avoid copying terms in LinExp arithmetic
- fix Sinz citation pages and encoder module doc
- cargo +nightly item-sort
- cargo +nightly fmt
- tighten Rust and Python API documentation
- cap a merge intermediate at the bound above it
- take the sum of two contiguous domains without enumerating it
- walk a ternary constraint in nested loops, not by recursion
- reuse one buffer for the literals of a clause
- add encoding cost and encoding quality benchmarks
- clarify encoding APIs and expand library documentation
- count literals into an integer under the name for it
- name the linear constraint module for what it holds
- measure the named encoder on cardinality constraints too
- cut the documentation back and fill in what was missing
- drop `Term` as a type and fix the constant in aggregation
- keep an integer's products with the integer
- move the cardinality constraint in beside the others
- separate the integer encoder from the constraint it takes
- give each linear encoding its own module
- give each at-most-one encoding its own module
- separate the Tseitin encoding from the formulas it encodes
- put the aggregator where the encoders are
- separate the sorting network from the constraint it encodes
- move the integer decisions in beside the Boolean ones
- give the Boolean decisions a module of their own
- let the integer encoder be an encoder
- name which encoders take a cardinality constraint
- drop the dead normalised Boolean linear constraint
- measure what the integer encodings cost
- generalise the adder circuits over constant bits
- tie the product encoding's selectors to their literals
- drop the fixed literals from the ladder encoding
- clean up linear aggregation
- *(external-propagation)* remove ReasonBuilder
- update itertools from 0.14 to 0.15

## [0.5.1](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.5.0...pindakaas-v0.5.1) - 2026-06-09

### Added

- *(external-propagation)* clone solvers with external propagator

### Removed

- *(external-propagation)* remove `Cadical::is_observed`; variable observation is now handled when cloning a solver through the new `Cadical::shallow_clone_with_propagator` method.

### Other

- update dependencies
- *(deps)* update rangelist requirement from 0.3.1 to 0.4.0
- *(deps)* update libloading requirement from 0.8 to 0.9

## [0.5.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.4.1...pindakaas-v0.5.0) - 2026-04-17

### Other

- Remove hidden `emitted_vars` methods from `Cadical` and `Kissat`, now that they're no longer required for the Python package.

## [0.4.1](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.4.0...pindakaas-v0.4.1) - 2026-02-21

### Other

- updated the following local packages: pindakaas-cadical, pindakaas-kissat

## [0.4.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.3.0...pindakaas-v0.4.0) - 2026-02-10

### Added

- update CaDiCaL to version 3.0.0

### Fixed

- [**breaking**] replace broken `with_conditions` with `encode_implied`
- propagation failure during linear simplication ([#184](https://github.com/pindakaashq/pindakaas/pull/184))

### Other

- [**breaking**] update default encoder choices
- set default propagation consistency to None
- remove unnecessary `use` ([#179](https://github.com/pindakaashq/pindakaas/pull/179))

## [0.3.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.2.3...pindakaas-v0.3.0) - 2025-11-26

### Added

- update CaDiCaL to version 2.2.0
- updated Kissat to version 4.0.4

### Changed

- `Propagator::notify_assignments` is now named `Propagator::notify_assignment`.
- `ProofTracer::add_derived_clause` now has an additional `witness` parameter.

### Other

- add citation to the documentation

## [0.2.3](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.2.2...pindakaas-v0.2.3) - 2025-11-04

### Fixed

- *(pindakaas)* impl `AsDynClauseDatabase` for dyn with any lifetime

## [0.2.2](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.2.1...pindakaas-v0.2.2) - 2025-09-30

### Other

- updated the following local packages: pindakaas-cadical

## [0.2.1](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.2.0...pindakaas-v0.2.1) - 2025-09-29

### Changed

- `VarRange::len` and `VarRange::is_empty` are now `const`.

## [0.2.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.1.0...pindakaas-v0.2.0) - 2025-09-25

### Added

- add `phase` and `unphase` to `ExternalPropagation`
- add bindings to CaDiCaL's `ProofTracer` interface
- allow the separate `PersistentAssignmentListener`

### Changed

- redesign the way that IPASIR solvers are defined in pindakaas

### Other

- add OPTIMA acknowledgements ([#156](https://github.com/pindakaashq/pindakaas/pull/156))
- naming of `Cnf` and `WCnf` information methods
- remove `iset` dependency
- reconsider the naming of solver related traits

## [0.1.0](https://github.com/pindakaashq/pindakaas/releases/tag/pindakaas-cadical-v0.1.0) - 2025-07-09

### Added

- Initial release of the `pindakaas` crate, which helps encode pseudo-Boolean
  constraints into CNF and interact with SAT solvers.
