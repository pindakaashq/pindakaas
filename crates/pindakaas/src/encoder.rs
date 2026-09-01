//! The encodings a constraint can be translated into.
//!
//! Each submodule holds one encoding. The constraint they take is under
//! [`constraint`](crate::constraint), which re-exports them.

pub mod aggregate;
pub mod sorted;
