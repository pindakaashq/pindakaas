//! `x + y ≷ z` over integer terms, and the encoder for it.
//!
//! Every decomposition strategy in
//! [`int_linear`](crate::constraint::int_linear) breaks a longer constraint
//! into these, so this is the one shape that is encoded directly rather than
//! broken up further.

use crate::constraint::{
	int_linear::{IntLinear, Term},
	linear::Comparator,
};
pub use crate::encoder::int_ternary::{IntTernaryConfig, IntTernaryEncoder};

/// A linear constraint over three integer terms, `x + y ≷ z`.
///
/// Decompositions differ in the shape of their intermediate sums, but all emit
/// this same step. Unlike
/// [`NormalizedIntLinear`](crate::constraint::int_linear::NormalizedIntLinear),
/// `z` remains on the other side of the comparison; moving it would require a
/// reversed view of the variable.
#[derive(Clone, Debug)]
pub struct IntTernary {
	pub(crate) x: Term,
	pub(crate) y: Term,
	pub(crate) cmp: Comparator,
	pub(crate) z: Term,
}

impl From<&IntTernary> for IntLinear {
	/// A term over a variable of one value is what it is worth, so it belongs
	/// with the constant rather than among the terms.
	fn from(con: &IntTernary) -> Self {
		let (mut terms, mut k) = (Vec::new(), 0);
		for (term, sign) in [(&con.x, 1), (&con.y, 1), (&con.z, -1)] {
			if term.1.card() == 1 {
				k -= sign * term.0 * term.1.min();
			} else {
				terms.push((sign * term.0, term.1.clone()));
			}
		}
		Self::new(terms, con.cmp, k)
	}
}

impl IntTernary {
	/// The comparator of the constraint.
	pub fn cmp(&self) -> Comparator {
		self.cmp
	}

	/// Construct the constraint `x + y ≷ z`.
	///
	/// # Examples
	///
	/// ```rust
	/// use pindakaas::{
	///     constraint::{int_ternary::{IntTernary, IntTernaryEncoder}, linear::Comparator},
	///     decision::integer::IntVar, Cnf, Encoder,
	/// };
	///
	/// let (x, y, z) = (
	///     IntVar::new(0..=5), IntVar::new(0..=5), IntVar::new(0..=10),
	/// );
	/// let constraint = IntTernary::new((1, x), (1, y), Comparator::Equal, (1, z));
	/// IntTernaryEncoder::default().encode(&mut Cnf::default(), &constraint)?;
	/// # Ok::<(), pindakaas::Unsatisfiable>(())
	/// ```
	pub fn new(x: Term, y: Term, cmp: Comparator, z: Term) -> Self {
		Self { x, y, cmp, z }
	}
}
