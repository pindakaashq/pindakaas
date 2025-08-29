# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.1](https://github.com/pindakaashq/pindakaas/compare/pyndakaas-v0.1.0...pyndakaas-v0.1.1) - 2025-08-29

### Added

- *(pyndakaas)* add support for kissat solver
- *(pyndakaas)* add clause and variable iteration for CNF and WCNF
- *(pyndakaas)* implementation default `ClauseDatabase.add_encoding`
- add bindings to CaDiCaL's proof tracer interface
- redesign the way that IPASIR solvers are defined in pindakaas

### Fixed

- *(pindakaas)* reintroduce `?Sized` removed by mistake
- *(pyndakaas)* python `failed` call ([#135](https://github.com/pindakaashq/pindakaas/pull/135))

### Other

- *(pyndakaas)* remove `Mutex` wrapper for `CaDiCaLInner`
- *(pindakaas)* reconsider the naming of solver related traits
- update pyo3 requirement from 0.24.0 to 0.25.1 ([#129](https://github.com/pindakaashq/pindakaas/pull/129))

## [0.1.0](https://github.com/pindakaashq/pindakaas/releases/tag/pyndakaas-v0.1.0) - 2025-07-08

### Added

- Initial release of the `pyndakaas` crate, which provides Python bindings
  for the `pindakaas` crate.
