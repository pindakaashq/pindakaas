//! Encoding a linear constraint as a chain of running totals.
//!
//! One intermediate per term, each the sum so far, so the shape is a line
//! rather than a tree.
//!
//! With unit coefficients this is Sinz's sequential counter [^2]; weighted, it
//! is the sequential weight counter, SWC [^1]; and where a term stands for a
//! group of mutually exclusive literals, GSWC [^3]. Domain consistent [^3].
//!
//! [^1]: S. Hölldobler, N. Manthey, P. Steinke, "A Compact Encoding of
//! Pseudo-Boolean Constraints into SAT", KI 2012, LNCS 7526, 107–118.
//!
//! [^2]: C. Sinz, "Towards an Optimal CNF Encoding of Boolean Cardinality
//! Constraints", CP 2005, LNCS 3709, 827–831.
//!
//! [^3]: M. Bofill, J. Coll, P. Nightingale, J. Suy, F. Ulrich-Oltean, M.
//! Villaret, "SAT encodings for pseudo-Boolean constraints together with
//! at-most-one constraints", Artificial Intelligence 302 (2022) 103604.

use itertools::Itertools;

use crate::{
	constraint::{
		bool_linear::NormalizedBoolLinear,
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		count::Count,
		int_linear::{decompose_setters, Decompose, DecomposeConfig, NormalizedIntLinear},
		int_ternary::IntTernary,
		linear::Comparator,
	},
	ClauseDatabase, Coeff, Encoder, Result, Unsatisfiable,
};

/// A chain of running totals (sequential counter, SWC, or GSWC).
///
/// # Examples
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{linear::{Comparator, Linear}, int_linear::SequentialCounterEncoder,
/// #                  linear::{LinAggregator, LinVariant}},
/// #     decision::integer::IntVar, Cnf, Encoder,
/// # };
/// # let mut f = Cnf::default();
/// # let (x, y) = (IntVar::new(0..=5), IntVar::new(0..=5));
/// let con = Linear::new(x * 2 + y * 3, Comparator::LessEq, 10);
/// let LinVariant::Linear(con) = LinAggregator::default().aggregate(&mut f, &con)? else {
///     panic!("a sum of integer terms is a linear constraint");
/// };
/// SequentialCounterEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SequentialCounterEncoder {
	config: DecomposeConfig,
}

impl SequentialCounterEncoder {
	decompose_setters!();
}

impl Decompose for SequentialCounterEncoder {
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
				self.config
					.intermediate(domain)
					.with_label(format_args!("y{i}"))
			})
			.collect_vec();

		Ok(con
			.signed_terms()
			.zip(totals.iter().tuple_windows())
			.map(|(x, (carried, left))| {
				IntTernary::new(x, (1, left.clone()), cmp, (1, carried.clone()))
			})
			.collect())
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for SequentialCounterEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for SequentialCounterEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Count> for SequentialCounterEncoder {
	fn encode(&self, db: &mut Db, con: &Count) -> Result {
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, NormalizedBoolLinear> for SequentialCounterEncoder {
	fn encode(&self, db: &mut Db, con: &NormalizedBoolLinear) -> Result {
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for SequentialCounterEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "sequential_counter_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		self.config.encoder().encode_decomposed(db, con, self)
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::helpers::tests::{linear_test_suite, prelude::*};

	#[test]
	fn supplied_direct_views_reject_a_nonzero_equality_sum() {
		use crate::decision::integer::IntVar;

		let mut cnf = Cnf::default();
		let mut expression = LinExp::default();
		let mut selected = Vec::new();
		// Preserve the term order that exposes the sequential-counter failure.
		for (values, index) in [
			((0..=4).collect_vec(), 0),
			((0..=10).collect_vec(), 8),
			((-3..=0).collect_vec(), 2),
			((-3..=0).collect_vec(), 2),
		] {
			let lits = values.iter().map(|_| cnf.new_lit()).collect_vec();
			PairwiseEncoder::default()
				.encode(
					&mut cnf,
					&CardinalityOne::new(lits.clone(), LimitComp::Equal),
				)
				.unwrap();
			let variable = IntVar::from_direct_walk(
				&mut cnf,
				values
					.into_iter()
					.zip(lits.iter().copied().map(BoolVal::Lit)),
			)
			.unwrap();
			expression += variable * 1;
			selected.push(lits[index]);
		}
		let constraint = Linear::new(expression, Comparator::Equal, 0);
		let constraint = LinAggregator::default()
			.aggregate(&mut cnf, &constraint)
			.unwrap();
		SequentialCounterEncoder::default()
			.encode(&mut cnf, &constraint)
			.unwrap();

		// Exactly-one views fixed to 0 + 8 - 1 - 1 = 6 cannot sum to zero.
		for &literal in &selected {
			cnf.add_clause([literal]).unwrap();
		}
		assert!(
			models_over(&cnf, &selected, |_| ()).is_empty(),
			"the sequential-counter encoding must reject 0 + 8 - 1 - 1 = 0"
		);
	}

	card1_test_suite! {
		sequential_counter_encoder_card1, SequentialCounterEncoder::default()
	}
	linear_test_suite! {sequential_counter_encoder, SequentialCounterEncoder::default()}
}
