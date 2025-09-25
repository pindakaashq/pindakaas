# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

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
