//! The constraints this library can encode.
//!
//! Each submodule holds a constraint and re-exports its encoders.
//! [`linear::Linear`] accepts general expressions; aggregation selects a
//! narrower constraint before encoding.

pub mod bool_linear;
pub mod cardinality;
pub mod cardinality_one;
pub mod count;
pub mod int_linear;
pub mod int_ternary;
pub mod linear;
pub mod propositional_logic;
