# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.0.1](https://github.com/pindakaashq/pindakaas/releases/tag/pindakaas-derive-v0.0.1) - 2025-07-07

### Added

- *(pyndakaas)* add initial encoding and solving interface
- *(pindakaas-derive)* Implement `Send` for solvers derived from IPASIR

### Fixed

- correct cargo metadata for releasing crates

### Other

- add release-plz configuration to help with releasing packages
- Remove unnecessary macro `emit_clauses!`
- Allow creation of `&dyn ClauseDatabase`
- Make `solve` methods return solution/fail (reference) objects
- Simplify the variable management and add `new_lits` convenience feature
- Simplify the Valuation trait
- Split out `external-propagation` feature
- Reorganize to simplify the structure of the code base
- Update Cadical to version 2.1.0
- Fix handling of empty clauses
- Enable additional (stricter) clippy lints and resolve conflicts
- Update testing infrastructure to use Cadical and expect_test
- Change the IPASIR UP implementation to directly use C callback functions
- Add FFIPointer helper type to manage Rust types exposed to C
- fix SolverAction implementation
- Update CaDiCaL to work on Windows
- Resolve one level of dispatch for IPASIR UP callbacks
- Resolve one level of dispatch for IPASIR callbacks
- Store solver callbacks in the solver struct
- Update IPASIR callback wrappers to use Box::leak instead of mem::forget
- Fix a problem where callbacks given to IPASIR solver where dropped early
- Add initial support for general propositional logic encoding
- Fix invalid coercion
- Expose propagator from the solution object when deriving IPASIR-UP
- Make solvers expose specific value and fail objects rather that &dyn
- Add trait for creating VarRange objects
- Give (mutable) access to the set external propagator
- add From<Cnf> implementation to Ipasir based solvers
- Add IPASIR-UP feature and small test case
- Make new_var return a Var object
- Add initial Rust interface for IPASIR UP
- Change Ipasir traint implementations using proc macro
