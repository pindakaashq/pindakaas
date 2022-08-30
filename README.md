# Pindakaas

[![crate](https://img.shields.io/crates/v/pindakaas.svg)](https://crates.io/crates/pindakaas)
[![documentation](https://docs.rs/pindakaas/badge.svg)](https://docs.rs/pindakaas)

A library to transform pseudo-Boolean and integer constraints into conjunctive normal form.

## Supported Constraints

- At most one
  - **TODO encoding**
- At most _K_
  - **TODO encoding**
- Boolean linear
  - **TODO encoding**
- Integer linear
  - **TODO encoding**

## Installation and usage

Although the main pindakaas library is written in rust, it is also available from Python and C(++).

### Rust

```bash
cargo add pindakaas
```

### Python

**TODO**

```bash
pip install pindakaas
```

### C/C++

**TODO**

## Acknowledgements

The encoding algorithms implemented in this library are based partially on the following academic research.

- **TODO**

This library is also heavily inspired by PBLib, an earlier library containing different encoding algorithms for pseudo-Boolean constraints. More information about PBLib can be found in its [accompanying publication](https://doi.org/10.1007/978-3-319-24318-4_2), and the source code for the library can be found on [GitHub](https://github.com/RealPete/PBLib)

This research was partially funded by the Australian Government through the Australian Research Council Industrial Transformation Training Centre in Optimisation Technologies, Integrated Methodologies, and Applications ([OPTIMA](https://optima.org.au)), Project ID IC200100009

## License

This library is made available under the [MPL-2.0](https://choosealicense.com/licenses/mpl-2.0/) license.
