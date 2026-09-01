//! The constraints this library can encode.
//!
//! Each submodule holds one kind of constraint, and re-exports the
//! [`Encoder`](crate::Encoder)s that take it.

pub mod bool_linear;
pub mod cardinality;
pub mod cardinality_one;
pub mod int_linear;
pub mod linear;
pub mod propositional_logic;
pub mod sorted;
