//! Counting literals into an integer, `Σ lits ≷ y`.
//!
//! A cardinality constraint whose bound is a variable rather than a constant,
//! so that what was counted is available to whatever else mentions `y`. A
//! sorting network states it directly, where going through a general linear
//! constraint would count into intermediate integers first.

pub use crate::encoder::sorting_network::{SortingNetworkEncoder, SortingNetworkStrategy};
use crate::{
	constraint::{
		int_linear::{lit_terms, NormalizedIntLinear},
		linear::{LimitComp, PosCoeff},
	},
	decision::integer::IntVar,
	Checker, ClauseDatabase, ClauseDatabaseTools, Coeff, Lit, Result, Unsatisfiable, Valuation,
};

/// Which encoders take a [`Count`], which rustdoc lists on the trait but the
/// compiler only checks if something names them.
#[cfg(test)]
const _: () = {
	use crate::{
		constraint::linear::{
			AdderEncoder, DecisionDiagramEncoder, MixedRadixEncoder, SequentialCounterEncoder,
			TotalizerEncoder, WatchdogEncoder,
		},
		Cnf, Encoder,
	};

	const fn takes<Db: ClauseDatabase + ?Sized, C, E: Encoder<Db, C>>() {}
	takes::<Cnf, Count, AdderEncoder>();
	takes::<Cnf, Count, DecisionDiagramEncoder>();
	takes::<Cnf, Count, MixedRadixEncoder>();
	takes::<Cnf, Count, SortingNetworkEncoder>();
	takes::<Cnf, Count, WatchdogEncoder>();
	takes::<Cnf, Count, SequentialCounterEncoder>();
	takes::<Cnf, Count, TotalizerEncoder>();
};

/// The constraint that `lits` add up to the integer `y`.
#[derive(Debug, Clone)]
pub struct Count {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) y: IntVar,
}

impl Count {
	/// Read the constraint as the integer linear constraint it is.
	///
	/// A literal is an integer worth one when it holds, and the bound counts
	/// the other way, which is a view on it rather than a variable of its own.
	/// Only for an encoder that works in integer terms; a sorting network
	/// states the constraint as it stands.
	pub(crate) fn as_int_linear<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<NormalizedIntLinear, Unsatisfiable> {
		// No count reaches a negative value.
		if self.y.max() < 0 {
			db.contradiction()?;
			unreachable!();
		}
		let mut terms = lit_terms(self.lits.iter().map(|&l| (l, PosCoeff::new(1))));
		// Counting the bound down from its greatest value turns its coefficient
		// positive and starts it at zero, as a normalised term has to.
		let k = self.y.max();
		terms.push((PosCoeff::new(1), -self.y.clone() + k));
		Ok(NormalizedIntLinear::new(terms, self.cmp, PosCoeff::new(k)))
	}

	/// Construct a constraint that `lits` add up to `y`, or to at most `y`.
	///
	/// # Examples
	///
	/// ```rust
	/// use pindakaas::{
	///     constraint::{count::{Count, SortingNetworkEncoder}, linear::LimitComp},
	///     decision::integer::IntVar, ClauseDatabase, Cnf, Encoder,
	/// };
	///
	/// let mut cnf = Cnf::default();
	/// let lits = cnf.new_var_range(4).map(Into::into).collect();
	/// let count = IntVar::new(0..=4);
	/// let constraint = Count::new(lits, LimitComp::Equal, count);
	/// SortingNetworkEncoder::default().encode(&mut cnf, &constraint)?;
	/// # Ok::<(), pindakaas::Unsatisfiable>(())
	/// ```
	pub fn new(lits: Vec<Lit>, cmp: LimitComp, y: IntVar) -> Self {
		Self { lits, cmp, y }
	}
}

impl Checker for Count {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<()> {
		let lhs = self.lits.iter().filter(|&&l| sol.value(l)).count() as Coeff;
		let rhs = self.y.value(sol);

		if match self.cmp {
			LimitComp::LessEq => lhs <= rhs,
			LimitComp::Equal => lhs == rhs,
		} {
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}
}

#[cfg(test)]
mod tests {
	use rangelist::RangeList;
	use traced_test::test;

	use crate::{
		constraint::{
			count::SortingNetworkEncoder,
			linear::{
				AdderEncoder, DecisionDiagramEncoder, LimitComp, MixedRadixEncoder,
				SequentialCounterEncoder, TotalizerEncoder,
			},
		},
		helpers::tests::assert_count_admits,
		Encoder,
	};

	/// A bound that can go negative is still counted from zero when the count
	/// is read as a linear constraint.
	#[test]
	fn a_negative_bound_is_counted_from_zero() {
		for cmp in [LimitComp::LessEq, LimitComp::Equal] {
			assert_count_admits(2, RangeList::from(-2..=2), cmp, |cnf, con| {
				TotalizerEncoder::default().encode(cnf, con)
			});
		}
	}

	/// Every encoder of a count admits exactly the assignments the count does,
	/// whether it states the constraint outright or reads it as a linear one.
	#[test]
	fn every_encoder_admits_the_same_counts() {
		for cmp in [LimitComp::LessEq, LimitComp::Equal] {
			for domain in [
				RangeList::from(0..=2),
				RangeList::from(1..=3),
				RangeList::from_elements([-1, 1, 3]),
			] {
				for name in ["sorted", "adder", "bdd", "swc", "gt", "mgto"] {
					assert_count_admits(3, domain.clone(), cmp, |cnf, con| match name {
						"sorted" => SortingNetworkEncoder::default().encode(cnf, con),
						"adder" => AdderEncoder::default().encode(cnf, con),
						"bdd" => DecisionDiagramEncoder::default().encode(cnf, con),
						"swc" => SequentialCounterEncoder::default().encode(cnf, con),
						"gt" => TotalizerEncoder::default().encode(cnf, con),
						_ => MixedRadixEncoder::default().encode(cnf, con),
					});
				}
			}
		}
	}
}
