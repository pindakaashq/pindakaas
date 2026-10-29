# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.7.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.6.1...pindakaas-v0.7.0) - 2026-10-29

### Added

- [**breaking**] return the clauses and counts of an aggregation instead of adding them
- [**breaking**] make every IntVar handle an affine view of its variable

### Added

- Arithmetic of an `IntVar` with a constant (`x + k`, `k + x`, `x - k`, `x * c`, `c * x`, and `-x`) gives a view of the same variable, see `decision::integer`. `with_order_encoding` and `with_direct_encoding` read their literals over the values of a view.
- `x + y` and `x - y` of two `IntVar`s, or of an `IntVar` and a `LinExp`, give a `LinExp`.
- `Linear::new` takes anything that converts into a `LinExp`, such as an `IntVar`.

### Changed

- [**breaking**] `IntVar::domain` returns the domain by value instead of borrowed.
- [**breaking**] `IntVar * Coeff` gives an `IntVar` instead of a `LinExp`.
- [**breaking**] `IntVar::mirrored` is removed: write `-x + (x.min() + x.max())`.
- [**breaking**] `NormalizedIntLinear::terms` returns an iterator instead of a slice, and `NormalizedIntLinear::new` panics on a term whose least value is not zero.
- [**breaking**] `LinAggregator::aggregate` takes no database and returns an `Aggregation`: the clauses a linear constraint implies on its own, the counts it sorts literals into, and the specialised form of the rest.
- [**breaking**] `LinAggregator::sort_same_coefficients` takes only the minimum number of literals. `LinearEncoder` encodes the counts with its variant encoder, as `LinVariant::Count`.
- [**breaking**] `IntVar::from_binary_encoding`, `IntVar::from_direct_encoding`, and `IntVar::from_order_encoding` no longer take a database argument and return an unwrapped `IntVar`.

## [0.6.1](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.6.0...pindakaas-v0.6.1) - 2026-10-19

### Added

- `WatchdogEncoder::with_sorting_networks` counts each digit with a sorting network, which is PBLib's binary merge.

### Changed

- `SortingNetworkEncoder` leaves the order consistency constraint out of an intermediate sum by default where its merges already state every value, which makes the network smaller. `with_consistency(true)` keeps it.
- The adder, decision diagram, mixed radix, and sorting network encoders emit fewer clauses and variables, and no clause that always holds. A two-valued integer shares one literal between its encodings.

### Fixed

- A linear constraint that its bounds rule out, such as `-x <= 0` with `x` in {-2, -1}, panicked with most encoders instead of returning `Unsatisfiable`. So did a `Count` whose bound stays below zero.
- `SortingNetworkEncoder` admitted a count whose bound is below zero, or panicked on it, and left the bound free in a count over no literals.
- `SortingNetworkEncoder` panicked in debug builds on some weighted constraints whose terms reach past the bound.
- `BitwiseEncoder` failed on an at-most-one over no literals: it panicked in debug builds and tried to allocate a huge signal range in release builds.
- `DecisionDiagramEncoder` failed on a sum of integers bounded by zero, such as `x + y + z <= 0`.
- When propagation emptied a domain, encoding returned `Unsatisfiable` without adding the empty clause, so the formula stayed satisfiable.
- Aggregation panicked when the database refused a clause, instead of returning `Unsatisfiable`.

## [0.6.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.5.1...pindakaas-v0.6.0) - 2026-10-13

### Added

- Integer variables: an `IntVar` owns its domain and holds up to three channelled Boolean encodings (direct, order, and binary), created on demand. `IntVar::from_*_encoding` and `with_*_encoding` build a variable on literals the caller already has.
- Linear constraints over integer variables: a `LinExp` mixes literals and `IntVar`s, and every linear encoder takes integer terms.
- `Count`, a constraint that counts literals into an integer variable, taken by every linear encoder.
- `WatchdogEncoder`, the polynomial watchdog encoding in its global and local forms.
- `MixedRadixEncoder`, the generalized n-level modulo totalizer encoding.
- `ProductEncoder`, the product encoding for at-most-one constraints.
- `SortingNetworkEncoder` now takes weighted linear constraints as well as cardinality constraints.
- Linear aggregation divides the coefficients by their greatest common divisor, and uses the declared bounds of binary encodings.
- The crate documentation tabulates every encoder, the constraints it takes, and the published encodings it covers.

### Changed

- [**breaking**] The public items move into the `constraint`, `decision`, and `encoder` modules, with one module per constraint and per encoding.
- [**breaking**] Encoders are named after their mechanism: `BddEncoder` is now `DecisionDiagramEncoder`, and `SwcEncoder` is now `SequentialCounterEncoder`.
- [**breaking**] `BoolLinear`, `BoolLinExp`, `BoolLinAggregator`, and `BoolLinVariant` are now `Linear`, `LinExp`, `LinAggregator`, and `LinVariant`.
- [**breaking**] `LinearEncoder` takes a single encoder: `LinearEncoder::<TotalizerEncoder>` works directly, `new` takes only the encoder, and `StaticLinEncoder` is only needed to mix encoders.
- [**breaking**] The default encoders change: pseudo-Boolean, cardinality, and count constraints take the totalizer, integer linear constraints take mixed radix, and at-most-one constraints take the product encoding.
- [**breaking**] `LinExp::terms` is now `LinExp::bool_terms`, and `LinExp::value` returns the value instead of a `Result`.
- [**breaking**] Learn and terminate callbacks must be `Send`.
- [**breaking**] *(external-propagation)* Propagators write clauses into a solver-owned `ClauseBuilder` instead of returning a `Vec`. `add_reason` is now `explain_propagation`, `add_external_clause` is now `provide_clause`, `PropagatorDefinition` and `ProofTracerDefinition` are now `PropagatorConfig` and `ProofTracerConfig`, and `check_solution` takes a borrowed `Solution`.
- `LadderEncoder` no longer creates literals for the fixed ends of the ladder.
- The `from_*` encoding constructors check their literal counts with `assert!` instead of `debug_assert!`.

### Removed

- [**breaking**] Remove the SPLR solver.
- [**breaking**] Remove `Consistency`; `with_propagation` takes a `bool` instead.
- [**breaking**] Remove `LinExp::add_constant`, `LinExp::add_lit`, `Linear::set_cmp`, and `DerefMut for PosCoeff`.

### Fixed

- Read the updated WCNF format, including hard clauses marked `h` in a file without a header.
- An `=` constraint over a group of mutually exclusive terms no longer loses solutions with the decision diagram, sequential counter, and totalizer encoders.
- Linear aggregation scales the constant of an expression by its multiplier.
- Callback pointers stay valid when the solver moves the boxed closure.

## [0.5.1](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.5.0...pindakaas-v0.5.1) - 2026-06-09

### Added

- *(external-propagation)* clone solvers with external propagator

### Removed

- *(external-propagation)* remove `Cadical::is_observed`; variable observation is now handled when cloning a solver through the new `Cadical::shallow_clone_with_propagator` method.

### Other

- update dependencies
- *(deps)* update rangelist requirement from 0.3.1 to 0.4.0
- *(deps)* update libloading requirement from 0.8 to 0.9

## [0.5.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.4.1...pindakaas-v0.5.0) - 2026-04-17

### Other

- Remove hidden `emitted_vars` methods from `Cadical` and `Kissat`, now that they're no longer required for the Python package.

## [0.4.1](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.4.0...pindakaas-v0.4.1) - 2026-02-21

### Other

- updated the following local packages: pindakaas-cadical, pindakaas-kissat

## [0.4.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.3.0...pindakaas-v0.4.0) - 2026-02-10

### Added

- update CaDiCaL to version 3.0.0

### Fixed

- [**breaking**] replace broken `with_conditions` with `encode_implied`
- propagation failure during linear simplication ([#184](https://github.com/pindakaashq/pindakaas/pull/184))

### Other

- [**breaking**] update default encoder choices
- set default propagation consistency to None
- remove unnecessary `use` ([#179](https://github.com/pindakaashq/pindakaas/pull/179))

## [0.3.0](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.2.3...pindakaas-v0.3.0) - 2025-11-26

### Added

- update CaDiCaL to version 2.2.0
- updated Kissat to version 4.0.4

### Changed

- `Propagator::notify_assignments` is now named `Propagator::notify_assignment`.
- `ProofTracer::add_derived_clause` now has an additional `witness` parameter.

### Other

- add citation to the documentation

## [0.2.3](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.2.2...pindakaas-v0.2.3) - 2025-11-04

### Fixed

- *(pindakaas)* impl `AsDynClauseDatabase` for dyn with any lifetime

## [0.2.2](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.2.1...pindakaas-v0.2.2) - 2025-09-30

### Other

- updated the following local packages: pindakaas-cadical

## [0.2.1](https://github.com/pindakaashq/pindakaas/compare/pindakaas-v0.2.0...pindakaas-v0.2.1) - 2025-09-29

### Changed

- `VarRange::len` and `VarRange::is_empty` are now `const`.

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
