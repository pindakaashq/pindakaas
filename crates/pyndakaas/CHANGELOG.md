# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

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
