//! The encodings a constraint can be translated into.
//!
//! Each submodule holds one encoding. The constraint types under
//! [`constraint`](crate::constraint) re-export their encoders. Algorithm
//! rationale and references live in the encoding modules.

//!
//! Domain consistency means unit propagation removes every unsupported value;
//! consistency-checking detects infeasibility but may leave unsupported values.
//! These are properties of the emitted clauses, distinct from domain pruning
//! performed while building an encoding. Published propagation guarantees
//! assume the documented representation: selecting binary views through a
//! cutoff can weaken them without changing the solutions.
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
