<p align="center">
  <img
    src="./assets/logo.svg"
    alt="pindakaas logo"
    height="300">

  <p align="center">
    A library to transform pseudo-Boolean and integer constraints into conjunctive normal form.
    <br />
    <br />
    <a href="https://crates.io/crates/pindakaas"><img src="https://img.shields.io/crates/v/pindakaas.svg"></a>
    <a href="https://crates.io/crates/pindakaas"><img src="https://docs.rs/pindakaas/badge.svg"></a>
  </p>
</p>


## Supported Constraints

- At most one (AMO)
  - Bitwise encoding
  - Ladder encoding
  - Pairwise encoding
- Cardinality constraints
  - Sorting Network encoding
- Boolean linear
  - Adder encoding
  - BDD encoding
  - Sequential Weight Counter encoding
  - Totalizer encoding
- Integer (linear)
  - Direct / Domain / Unary encoding
  - Order encoding
  - Binary encoding

## Installation and usage

Although the main Pindakaas library is written in rust, it is also available from Python.

### Rust

```bash
cargo add pindakaas
```

For more information about the Rust library, please visit the [official documentation](https://docs.rs/pindakaas).

### Python

```bash
pip install pindakaas
```

For more information about the Python library, please visit the [official documentation](https://pindakaas.readthedocs.io/en/latest/).

## Acknowledgements

This research was partially funded by the Australian Government through the Australian Research Council Industrial Transformation Training Centre in Optimisation Technologies, Integrated Methodologies, and Applications ([OPTIMA](https://optima.org.au)), Project ID IC200100009

## License

This library is made available under the [MPL-2.0](https://choosealicense.com/licenses/mpl-2.0/) license.
