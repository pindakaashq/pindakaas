# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.7.0](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.6.1...pyndakaas-v0.7.0) - 2026-10-29

### Added

- [**breaking**] return the clauses and counts of an aggregation instead of adding them
- [**breaking**] make every IntVar handle an affine view of its variable

### Other

- *(pyndakaas)* update pyo3 to 0.30.1 and ship type stubs

### Added

- Type stubs for the compiled module, and a `py.typed` marker.
- Wheels for free-threaded CPython 3.14.
- `IntVar` supports subtraction from the left, as in `5 - x`.

### Changed

- [**breaking**] Arithmetic of an `IntVar` with an integer gives an `IntVar`, a view of the same variable.
- Update pyo3 from 0.29.0 to 0.30.1.

## [0.6.1](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.6.0...pyndakaas-v0.6.1) - 2026-10-19

### Added

- `add_encoding` takes encoder options as keyword arguments, such as `strategy` for `Encoder.SORTING_NETWORK` and `sorting_networks` for `Encoder.WATCHDOG`. An option the encoder does not take raises `InvalidEncoder`.

### Changed

- `Encoder.SORTING_NETWORK` leaves the order consistency constraint out of intermediate sums by default, which makes the network smaller. `consistency=True` keeps it.

### Fixed

- A custom `ClauseDatabase` raised a `TypeError` when `add_encoding` was called without conditions, or with a generator of literals.
- The encoding fixes of pindakaas 0.6.1 apply, among them `Unsatisfiable` instead of a `PanicException` for a constraint that its bounds rule out, such as `-x <= 0` with `x` in {-2, -1}.

## [0.6.0](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.5.1...pyndakaas-v0.6.0) - 2026-10-13

### Added

- Integer variables: `IntVar` and `Domain`, created with `ClauseDatabase.new_int_var` or on existing literals with `int_var_from_order_literals`, `int_var_from_direct_literals`, and `int_var_from_binary_literals`.
- Linear expressions and constraints over integer variables as well as literals.
- `Encoder.WATCHDOG`, `Encoder.MIXED_RADIX`, and `Encoder.PRODUCT`.
- `Encoder.SORTING_NETWORK` now takes weighted linear constraints.
- `ClauseDatabase.add_clause` accepts constant Boolean values.

### Changed

- [**breaking**] `Encoder.SORTED_WEIGHT_COUNTER` is now `Encoder.SEQUENTIAL_COUNTER`.
- [**breaking**] The default encoders change: pseudo-Boolean, cardinality, and count constraints take the totalizer, integer linear constraints take mixed radix, and at-most-one constraints take the product encoding.
- Build a single abi3 wheel per platform for CPython 3.9 and later. PyPy installs from the source distribution.
- Update pyo3 from 0.28.3 to 0.29.0.

### Fixed

- Read the updated WCNF format, including hard clauses marked `h` in a file without a header.
- An encoder that allocates a variable range through a database written in Python no longer panics.

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
