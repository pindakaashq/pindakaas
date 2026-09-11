//! The encodings a constraint can be translated into.
//!
//! Each submodule holds one encoding. The constraint they take is under
//! [`constraint`](crate::constraint), which re-exports them.

pub mod adder;
pub mod aggregate;
pub mod bitwise;
pub mod decision_diagram;
pub mod int_ternary;
pub mod ladder;
pub mod mixed_radix;
pub mod pairwise;
pub mod product;
pub mod sequential_counter;
pub mod sorting_network;
pub mod totalizer;
pub mod tseitin;
pub mod watchdog;
