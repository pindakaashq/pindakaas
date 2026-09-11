//! Boolean and integer decision variables.
//!
//! [`boolean`] holds literals and constant Boolean values. [`integer`] holds
//! domains and their lazily created Boolean views, allowing constraints to
//! share a variable across encodings.

pub mod boolean;
pub mod integer;
