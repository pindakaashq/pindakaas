# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.6.0](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.5.1...pyndakaas-v0.6.0) - 2026-09-18

### Added

- expose the product at-most-one encoding to Python
- [**breaking**] encode an aggregated constraint with a single encoder
- [**breaking**] add the polynomial watchdog encoding
- add generalized n-level modulo totalizer encoding
- ask an integer variable for the literals of its values
- create and constrain integer variables from Python
- write linear expressions over integers as well as literals
- aggregate linear constraints into integer ones
- add product encoding for at-most-one constraints

### Fixed

- read updated WCNF format
- encode a count with any of the linear encodings
- read the ends of a variable range from the range itself
- C robustness issues

### Other

- report an unsupported encoder without a lock
- [**breaking**] one handle for what a variable has already encoded
- cargo +nightly item-sort
- cargo +nightly fmt
- tighten Rust and Python API documentation
- clarify encoding APIs and expand library documentation
- name the linear constraint module for what it holds
- cut the documentation back and fill in what was missing
- drop `Term` as a type and fix the constant in aggregation
- move the cardinality constraint in beside the others
- separate the integer encoder from the constraint it takes
- give each linear encoding its own module
- give each at-most-one encoding its own module
- separate the Tseitin encoding from the formulas it encodes
- put the aggregator where the encoders are
- move the integer decisions in beside the Boolean ones
- *(pyndakaas)* build a single abi3 wheel per platform
- update itertools from 0.14 to 0.15
- *(deps)* update pyo3 requirement from 0.28.3 to 0.29.0

## [0.5.1](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.5.0...pyndakaas-v0.5.1) - 2026-06-09

### Other

- update dependencies

## [0.5.0](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.4.1...pyndakaas-v0.5.0) - 2026-04-17

### Added

- Use custom `Result` object, implemented in Rust, for solver implementations originating from the Rust Pindakaas library.

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
