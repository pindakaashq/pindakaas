# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.0](https://github.com/pindakaashq/pindakaas/releases/tag/pyndakaas-v0.1.0) - 2025-07-07

### Added

- *(pyndakaas)* support conditional constraint encoding ([#102](https://github.com/pindakaashq/pindakaas/pull/102))
- *(pyndakaas)* add reflected operators for `BoolExp`, `Formula`, and `Lit` ([#100](https://github.com/pindakaashq/pindakaas/pull/100))
- *(pyndakaas)* add initial encoding and solving interface

### Fixed

- correct cargo metadata for releasing crates
- *(pyndakaas)* raise exception instead of rust panics ([#103](https://github.com/pindakaashq/pindakaas/pull/103))
- *(pyndakaas)* export exceptions so users can catch them ([#101](https://github.com/pindakaashq/pindakaas/pull/101))

### Other

- add release-plz configuration to help with releasing packages
- *(pyndakaas)* add initial sphinx documentation ([#109](https://github.com/pindakaashq/pindakaas/pull/109))
- *(pyndakaas)* simplify internal encoder/constraint matching ([#105](https://github.com/pindakaashq/pindakaas/pull/105))
- Allow creation of `&dyn ClauseDatabase`
- Disambiguate linear from Boolean linear
- Reorganize to simplify the structure of the code base
- Enable additional (stricter) clippy lints and resolve conflicts
- Make new_var return a Var object
- Add ClauseDatabase::encode method
- Add initial CaDiCaL interface
- Make `Lit` its own type
- Resolve feature conditional import warnings
- New start for the Python library
- Disable labeling
- Support variable labels (in debug mode)
- Restructure library for all encoders to be structs
- Update maturin configuration
- Add README and update authors ([#2](https://github.com/pindakaashq/pindakaas/pull/2))
- Add totalizer encoder with support for constrained literal groups ([#1](https://github.com/pindakaashq/pindakaas/pull/1))
- Add initial function to Python interface
- Update descriptions of interfacing crates
