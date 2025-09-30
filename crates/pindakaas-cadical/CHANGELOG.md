# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.1](https://github.com/pindakaashq/pindakaas/compare/pindakaas-cadical-v0.2.0...pindakaas-cadical-v0.2.1) - 2025-09-30

### Fixed

- package unistd.h for windows release

## [0.2.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-cadical-v0.1.0...pindakaas-cadical-v0.2.0) - 2025-09-25

### Added

- add bindings to CaDiCaL's proof tracer interface
- allow the separate PersistentAssignmentListener
- redesign the way that IPASIR solvers are defined in pindakaas

## [0.1.0](https://github.com/pindakaashq/pindakaas/releases/tag/pindakaas-cadical-v0.1.0) - 2025-07-09

### Added

- Initial release of the `pindakaas-cadical` crate, which provides Rust bindings
  to the [CaDiCaL](https://github.com/arminbiere/cadical) SAT solver for
  `pindakaas`.
