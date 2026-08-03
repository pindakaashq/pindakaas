# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.5.2](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.5.1...pyndakaas-v0.5.2) - 2026-08-03

### Fixed

- C robustness issues

### Other

- *(pyndakaas)* build a single abi3 wheel per platform
- update itertools from 0.14 to 0.15
- *(deps)* update pyo3 requirement from 0.28.3 to 0.29.0

## [0.5.1](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.5.0...pyndakaas-v0.5.1) - 2026-06-09

### Other

- update dependencies

## [0.5.0](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.4.1...pyndakaas-v0.5.0) - 2026-04-17

### Added

- Use custom `Result` object, implemented in Rust, for solver implementations originating from the Rust Pindakaas library.

### Added

- Fix a `solver.CaDiCaL` error that was caused by `MapResult` creation accessing literals that are meant to only be accessed by CaDiCaL itself.

### Removed

- Remove `solver.MapResult` after it became unused for internal `solver.Solver` implementations.

## [0.4.1](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.4.0...pyndakaas-v0.4.1) - 2026-02-21

### Added

- _set_option for CaDiCaL ([#195](https://github.com/pindakaashq/pindakaas/pull/195))
- Windows ARM compatibility

## [0.4.0](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.3.0...pyndakaas-v0.4.0) - 2026-02-10

### Fixed

- replace broken `with_conditions` with `encode_implied`

### Other

- [**breaking**] update default encoder choices

## [0.3.0](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.2.3...pyndakaas-v0.3.0) - 2025-11-26

### Other

- updated the following local packages: pindakaas
- add citation to the documentation

## [0.2.3](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.2.2...pyndakaas-v0.2.3) - 2025-11-04

### Other

- updated the following local packages: pindakaas

## [0.2.2](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.2.1...pyndakaas-v0.2.2) - 2025-09-30

### Other

- add pyproject metadata
- updated the following local packages: pindakaas

## [0.2.1](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.2.0...pyndakaas-v0.2.1) - 2025-09-29

### Fixed

- consistent `new_var_range` returns for solvers

## [0.1.1](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.1.0...pyndakaas-v0.1.1) - 2025-09-25

### Added

- add support for Kissat solver
- add clause and variable iteration for CNF and WCNF
- implementation default `ClauseDatabase.add_encoding`

### Fixed

- python `failed` call ([#135](https://github.com/pindakaashq/pindakaas/pull/135))

### Other

- resolve build problems for Python documentation
- update `pyo3` requirement from 0.24.0 to 0.26.0
- remove `Mutex` wrapper for `CaDiCaLInner`

## [0.1.0](https://github.com/pindakaashq/pindakaas/releases/tag/pyndakaas-v0.1.0) - 2025-07-08

### Added

- Initial release of the `pyndakaas` crate, which provides Python bindings
  for the `pindakaas` crate.
