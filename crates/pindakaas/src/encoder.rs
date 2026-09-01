//! The encodings a constraint can be translated into.
//!
//! Each submodule holds one encoding. The constraint they take is under
//! [`constraint`](crate::constraint), which re-exports them.

pub mod adder;
pub mod aggregate;
pub mod bdd;
pub mod bitwise;
pub mod int_lin;
pub mod ladder;
pub mod pairwise;
pub mod product;
pub mod sorted;
pub mod sorting_network;
pub mod swc;
pub mod totalizer;
pub mod tseitin;
