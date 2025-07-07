# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.0.1](https://github.com/pindakaashq/pindakaas/releases/tag/pindakaas-intel-sat-v0.0.1) - 2025-07-07

### Fixed

- correct cargo metadata for releasing crates
- suppress unused result warnings in build scripts

### Other

- add release-plz configuration to help with releasing packages
- remove `pindakaas-build-macros` crate
- Fix files included with the solver crates
- Enable additional (stricter) clippy lints and resolve conflicts
- Disable assertions in C solvers when compiling in release mode
- Update intel-sat repository and disable compilation warnings
- Fix intel sat build
- Update intel sat solver
- Add initial Kissat interface
- Resolve issues when linking two IPASIR libraries
- Add initial Intel SAT interface
