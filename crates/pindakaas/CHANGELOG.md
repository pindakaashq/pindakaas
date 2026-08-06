# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.6.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.5.1...pindakaas-v0.6.0) - 2026-08-06

### Added

- use declared bounds of log encodings during aggregation
- apply greatest common divisor during linear aggregation
- *(external-propagation)* streamline allocation in ExternalPropagation API

### Fixed

- re-enable already working testcases
- C robustness issues

### Other

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
