//! The constraints this library can encode.
//!
//! Each submodule holds one kind of constraint, and re-exports the
//! [`Encoder`](crate::Encoder)s that take it.

pub mod bool_linear;
pub mod cardinality;
pub mod cardinality_one;
pub mod count;
pub mod int_linear;
pub mod int_ternary;
pub mod linear;
pub mod propositional_logic;
