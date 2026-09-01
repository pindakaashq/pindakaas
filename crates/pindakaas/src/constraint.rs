//! The constraints this library can encode.
//!
//! Each submodule holds one kind of constraint, and re-exports the
//! [`Encoder`](crate::Encoder)s that take it.

pub mod linear;
pub mod sorted;
