//! A linear constraint over literals alone, `Σ cᵢ·litᵢ ≷ k`.
//!
//! What a [`Linear`](super::linear::Linear) mentioning no integer variable
//! aggregates to. The same shape as a
//! [`NormalizedIntLinear`], but left in
//! the literals it was written in, so that an encoder working in them is not
//! handed integers to take apart again.

pub use crate::encoder::adder::AdderEncoder;
use crate::{
	constraint::{
		int_linear::{lit_terms, NormalizedIntLinear},
		linear::{LimitComp, PosCoeff},
	},
	ClauseDatabase, Coeff, Lit, Result, Unsatisfiable,
};

/// A linear constraint over literals alone, as aggregation leaves it.
///
/// Terms remain literals so Boolean encoders need not unpack integer views.
#[derive(Clone, Debug)]
pub struct NormalizedBoolLinear {
	pub(crate) terms: Vec<(Lit, PosCoeff)>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

impl NormalizedBoolLinear {
	/// Read the constraint as the integer linear constraint it is.
	///
	/// Only for an encoder that works in integers; one that works in literals
	/// should take this constraint as it stands.
	pub(crate) fn as_int_linear<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<NormalizedIntLinear, Unsatisfiable> {
		let terms = lit_terms(db, self.terms.iter().copied())?;
		Ok(NormalizedIntLinear::new(terms, self.cmp, self.k))
	}

	/// Returns the constraint's comparator, which is never `≥`.
	pub fn cmp(&self) -> LimitComp {
		self.cmp
	}

	/// Returns the non-negative constant the sum is compared against.
	pub fn k(&self) -> Coeff {
		*self.k
	}

	/// Construct the constraint `Σ cᵢ·litᵢ ≷ k`.
	pub fn new(
		terms: impl IntoIterator<Item = (Lit, PosCoeff)>,
		cmp: LimitComp,
		k: PosCoeff,
	) -> Self {
		Self {
			terms: terms.into_iter().collect(),
			cmp,
			k,
		}
	}

	/// The terms of the sum, each with a positive coefficient.
	pub fn terms(&self) -> &[(Lit, PosCoeff)] {
		&self.terms
	}
}
