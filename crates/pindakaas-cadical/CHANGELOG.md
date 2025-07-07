# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.0.1](https://github.com/pindakaashq/pindakaas/releases/tag/pindakaas-cadical-v0.0.1) - 2025-07-07

### Added

- *(pyndakaas)* add initial encoding and solving interface

### Fixed

- correct cargo metadata for releasing crates
- suppress unused result warnings in build scripts

### Other

- add release-plz configuration to help with releasing packages
- remove `pindakaas-build-macros` crate
- Experimental proof logging interface for CaDiCaL ([#94](https://github.com/pindakaashq/pindakaas/pull/94))
- Allow PropagatingCadical to be cloned if the propagator is Clone
- Add pindakaas-cadical `tracing` feature
- Fix files included with the solver crates
- Update CaDiCaL to version 2.1.3
- Update CaDiCaL to version 2.1.2
- Update Cadical to version 2.1.0
- Enable additional (stricter) clippy lints and resolve conflicts
- Signal restarts in notify_backtrack IPASIR-UP callbacks
- Disable assertions in C solvers when compiling in release mode
- Change the IPASIR UP implementation to directly use C callback functions
- Add additional Cadical patches for IPASIR-UP usage
- Update CaDiCaL to work on Windows
- Update CaDiCaL to pre-release 2.0.0 to fix a problem
- Fix missing source file in pindakaas-cadical
- Update CaDiCaL to v1.9.5
- Add ability to clone solver
- Add initial Rust interface for IPASIR UP
- Add initial building of the CaDiCaL IPASIR-UP interface
- Update CaDiCaL to v1.9.4
- Update CaDiCaL to v1.9.3
- Update CaDiCaL to v1.9.2
- Update CaDiCaL to version 1.9.0
- Resolve issues when linking two IPASIR libraries
- Add initial Intel SAT interface
- Add initial CaDiCaL interface
