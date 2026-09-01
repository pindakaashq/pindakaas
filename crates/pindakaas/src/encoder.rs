//! The encodings a constraint can be translated into.
//!
//! Each submodule holds one encoding. The constraint they take is under
//! [`constraint`](crate::constraint), which re-exports them.

pub mod aggregate;
pub mod bitwise;
pub mod ladder;
pub mod pairwise;
pub mod product;
pub mod sorted;
pub mod tseitin;
