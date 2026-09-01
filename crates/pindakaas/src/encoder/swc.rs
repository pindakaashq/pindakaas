//! Encoding a linear constraint as a chain of running totals.
//!
//! One intermediate per term, each the sum so far, so the shape is a line
//! rather than a tree.

use itertools::Itertools;

use crate::{
	cardinality::Cardinality,
	constraint::{bool_linear::Comparator, cardinality_one::CardinalityOne},
	decision::integer::{Consistency, IntVar},
	int_linear::{
		Decompose, IntLinConfig, IntLinEncoder, NormalizedIntLinear, Term, TernaryIntLinear,
	},
	ClauseDatabase, Coeff, Encoder, Result, Unsatisfiable,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight
/// Counter (SWC)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SwcEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<Coeff>,
}

impl Default for SwcEncoder {
	/// Narrowing the domains before encoding is worth doing: it is what keeps
	/// the intermediate sums of a decomposition small, and turning it off can
	/// cost several times the clauses.
	fn default() -> Self {
		Self {
			add_consistency: false,
			add_propagation: Consistency::Bounds,
			cutoff: None,
		}
	}
}

impl SwcEncoder {
	/// The encoder of the pieces this one decomposes a constraint into.
	fn encoder(&self) -> IntLinEncoder {
		IntLinEncoder::with_config(IntLinConfig {
			propagate: self.add_propagation != Consistency::None,
			cutoff: self.cutoff,
		})
	}

	/// Set whether to add consistency constraints on the intermediate integer
	/// variables.
	pub fn with_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}

	/// Set the largest domain size for which the intermediate integer variables
	/// are encoded using order encoding.
	pub fn with_cutoff(&mut self, c: Option<Coeff>) -> &mut Self {
		self.cutoff = c;
		self
	}

	/// Set whether to perform additional propagation of the linear constraint
	/// before encoding the constraint into CNF.
	pub fn with_propagation(&mut self, c: Consistency) -> &mut Self {
		self.add_propagation = c;
		self
	}
}

impl Decompose for SwcEncoder {
	/// Carry a running total along the terms, one at a time.
	///
	/// Each step passes on what is left of the bound after the term it sees, so
	/// the totals telescope: adding the steps together leaves the first total
	/// against the last, which is the constraint. Counting down from nothing to
	/// minus the bound keeps every total within it.
	fn decompose<Db: ClauseDatabase + ?Sized>(
		&self,
		_db: &mut Db,
		con: &NormalizedIntLinear,
	) -> Result<Vec<TernaryIntLinear>, Unsatisfiable> {
		// Two terms or fewer are already as small as the chain would make them.
		if con.terms().len() <= 2 {
			return Ok(vec![con.into()]);
		}
		let (cmp, k, n) = (Comparator::from(con.cmp()), con.k(), con.terms().len());
		let totals = (0..=n)
			.map(|i| {
				// The ends are fixed, so that what the chain proves between
				// them is the constraint itself.
				let domain = match i {
					0 => 0..=0,
					_ if i == n => -k..=-k,
					_ => -k..=0,
				};
				IntVar::new(domain)
					.enforce_consistency(self.add_consistency)
					.with_label(format!("y{i}"))
			})
			.collect_vec();

		Ok(con
			.terms()
			.iter()
			.zip(totals.iter().tuple_windows())
			.map(|(x, (carried, left))| {
				TernaryIntLinear::new(
					x.clone(),
					Term::new(1, left.clone()),
					cmp,
					Term::new(1, carried.clone()),
				)
			})
			.collect())
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for SwcEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "swc_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		self.encoder().encode_decomposed(db, con, self)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for SwcEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for SwcEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

#[cfg(test)]
mod tests {
	use crate::helpers::tests::{linear_test_suite, prelude::*};

	card1_test_suite! {
		swc_encoder_card1, SwcEncoder::default()
	}
	linear_test_suite! {swc_encoder, SwcEncoder::default()}
}
