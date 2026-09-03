//! Encoding a linear constraint as a chain of running totals.
//!
//! One intermediate per term, each the sum so far, so the shape is a line
//! rather than a tree.

use itertools::Itertools;

use crate::{
	constraint::{
		linear::Comparator,
		bool_linear::NormalizedBoolLinear,
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		int_linear::{Decompose, NormalizedIntLinear},
		int_ternary::{IntTernary, IntTernaryConfig, IntTernaryEncoder},
	},
	decision::integer::{Consistency, IntVar},
	ClauseDatabase, Coeff, Encoder, Result, Unsatisfiable,
};

/// Encoder for a linear constraint, decomposing it into a chain of running
/// totals (a sequential weight counter, SWC).
///
/// One intermediate per term, each the sum so far, so the pieces are a line
/// rather than a tree: the last intermediate is as wide as the whole sum.
///
/// # Examples
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{linear::{Comparator, Linear}, int_linear::SwcEncoder,
/// #                  linear::{LinAggregator, LinVariant}},
/// #     decision::integer::IntVar, Cnf, Encoder,
/// # };
/// # let mut f = Cnf::default();
/// # let (x, y) = (IntVar::new(0..=5), IntVar::new(0..=5));
/// let con = Linear::new(x * 2 + y * 3, Comparator::LessEq, 10);
/// let LinVariant::Linear(con) = LinAggregator::default().aggregate(&mut f, &con)? else {
///     panic!("a sum of integer terms is a linear constraint");
/// };
/// SwcEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
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
	fn encoder(&self) -> IntTernaryEncoder {
		IntTernaryEncoder::with_config(IntTernaryConfig {
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
	) -> Result<Vec<IntTernary>, Unsatisfiable> {
		// Two terms or fewer are already as small as the chain would make them.
		if let Some(addition) = con.as_ternary() {
			return Ok(vec![addition]);
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
			.map(|(c, x)| (**c, x.clone()))
			.zip(totals.iter().tuple_windows())
			.map(|(x, (carried, left))| {
				IntTernary::new(x, (1, left.clone()), cmp, (1, carried.clone()))
			})
			.collect())
	}
}

impl<Db> Encoder<Db, NormalizedBoolLinear> for SwcEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	fn encode(&self, db: &mut Db, con: &NormalizedBoolLinear) -> Result {
		// Decomposing works in integers, so the literals become them first.
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
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
