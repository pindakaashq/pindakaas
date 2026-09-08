//! A linear constraint over literals alone, `Σ cᵢ·litᵢ ≷ k`.
//!
//! What a [`Linear`](super::linear::Linear) mentioning no integer variable
//! aggregates to. The same shape as a
//! [`NormalizedIntLinear`], but left in
//! the literals it was written in, so that an encoder working in them is not
//! handed integers to take apart again.

use rangelist::RangeList;

pub use crate::encoder::adder::AdderEncoder;
use crate::{
	constraint::{
		int_linear::NormalizedIntLinear,
		linear::{LimitComp, PosCoeff},
	},
	decision::integer::IntVar,
	ClauseDatabase, Coeff, Lit, Result, Unsatisfiable,
};

/// A linear constraint over literals alone, as aggregation leaves it.
///
/// Every coefficient is positive and the comparison is never `≥`, as for a
/// [`NormalizedIntLinear`], but the terms are still literals. Aggregation keeps
/// them that way where a constraint mentions no integer variable, so that an
/// encoder working in literals is not handed integers to take apart again.
#[derive(Clone, Debug)]
pub struct NormalizedBoolLinear {
	pub(crate) terms: Vec<(Lit, PosCoeff)>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

impl NormalizedBoolLinear {
	/// Returns the constraint's comparator, which is never `≥`.
	pub fn cmp(&self) -> LimitComp {
		self.cmp.clone()
	}

	/// Returns the non-negative constant the sum is compared against.
	pub fn k(&self) -> Coeff {
		*self.k
	}

	/// The constraint `Σ cᵢ·litᵢ ≷ k`.
	///
	/// Every guarantee the type makes is carried by the arguments: a
	/// [`LimitComp`] cannot be `≥`, and a [`PosCoeff`] cannot be negative.
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

	/// Read the constraint as the integer linear constraint it is.
	///
	/// A literal is an integer worth its coefficient when it holds and nothing
	/// when it does not, which is a direct encoding of the two values already.
	/// Only for an encoder that works in integers; one that works in literals
	/// should take this constraint as it stands.
	pub(crate) fn as_int_linear<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<NormalizedIntLinear, Unsatisfiable> {
		let terms = self
			.terms
			.iter()
			.enumerate()
			.map(|(i, &(lit, coef))| {
				let domain = RangeList::from_elements([0, *coef]);
				IntVar::from_direct_encoding(db, domain, &[!lit, lit])
					.map(|x| (PosCoeff::new(1), x.with_label(format!("x{i}"))))
			})
			.collect::<Result<Vec<_>, _>>()?;
		Ok(NormalizedIntLinear::new(terms, self.cmp(), self.k))
	}

	/// The terms of the sum, each with a positive coefficient.
	pub fn terms(&self) -> &[(Lit, PosCoeff)] {
		&self.terms
	}
}
