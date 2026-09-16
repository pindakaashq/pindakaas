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
	Checker, ClauseDatabase, Coeff, Lit, Result, Unsatisfiable, Valuation,
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
		let mut terms = lit_terms(db, self.lits.iter().map(|&l| (l, PosCoeff::new(1))))?;
		// Counting the bound from its far end turns its coefficient positive,
		// and moves what it was worth into the constant.
		let mut k = self.y.min() + self.y.max();
		let mut y = IntVar::mirrored(db, &self.y)?;
		if y.min() < 0 {
			// A normalised constraint counts every term from zero, and what the
			// shift is worth goes to the bound.
			k -= y.min();
			y = IntVar::shifted(db, &y, -y.min())?;
		}
		terms.push((PosCoeff::new(1), y));
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
	use itertools::Itertools;
	use traced_test::test;

	use super::{Count, SortingNetworkEncoder};
	use crate::{
		constraint::linear::{
			AdderEncoder, DecisionDiagramEncoder, LimitComp, MixedRadixEncoder,
			SequentialCounterEncoder, TotalizerEncoder,
		},
		decision::integer::IntVar,
		helpers::tests::{models, models_over},
		ClauseDatabaseTools, Cnf, Encoder,
	};

	/// A bound that can go negative is still counted from zero when the count
	/// is read as a linear constraint.
	#[test]
	fn a_negative_bound_is_counted_from_zero() {
		for cmp in [LimitComp::LessEq, LimitComp::Equal] {
			let mut cnf = Cnf::default();
			let lits = (0..2).map(|_| cnf.new_lit()).collect_vec();
			let y = IntVar::new(-2..=2).with_label("y");
			let con = Count::new(lits.clone(), cmp.clone(), y.clone());
			TotalizerEncoder::default().encode(&mut cnf, &con).unwrap();

			let mut seen = models(&cnf, |sol| {
				let n = lits.iter().filter(|&&l| sol.value(l)).count() as i64;
				(n, y.value(sol))
			});
			seen.sort_unstable();
			seen.dedup();
			let want = (0..=2)
				.cartesian_product(-2..=2)
				.filter(|&(n, v)| match cmp {
					LimitComp::LessEq => n <= v,
					LimitComp::Equal => n == v,
				})
				.collect_vec();
			assert_eq!(seen, want, "{cmp:?} over a bound reaching below zero");
		}
	}

	/// Every encoder of a count admits the same assignments, whether it states
	/// the constraint outright or reads it as a linear one.
	#[test]
	fn every_encoder_admits_the_same_counts() {
		for cmp in [LimitComp::LessEq, LimitComp::Equal] {
			let mut want: Option<Vec<(usize, i64)>> = None;
			for name in ["sorted", "adder", "bdd", "swc", "gt", "mgto"] {
				let mut cnf = Cnf::default();
				let lits = (0..3).map(|_| cnf.new_lit()).collect_vec();
				let y = IntVar::new(0..=2).with_label("y");
				let con = Count::new(lits.clone(), cmp.clone(), y.clone());
				match name {
					"sorted" => SortingNetworkEncoder::default().encode(&mut cnf, &con),
					"adder" => AdderEncoder::default().encode(&mut cnf, &con),
					"bdd" => DecisionDiagramEncoder::default().encode(&mut cnf, &con),
					"swc" => SequentialCounterEncoder::default().encode(&mut cnf, &con),
					"gt" => TotalizerEncoder::default().encode(&mut cnf, &con),
					_ => MixedRadixEncoder::default().encode(&mut cnf, &con),
				}
				.unwrap();

				let mut seen = models_over(&cnf, &lits, |sol| {
					let n = lits.iter().filter(|&&l| sol.value(l)).count();
					(n, y.value(sol))
				});
				seen.sort_unstable();
				seen.dedup();
				match &want {
					None => {
						assert!(!seen.is_empty(), "{name} {cmp:?} admits something");
						for &(n, v) in &seen {
							match cmp {
								LimitComp::Equal => assert_eq!(n as i64, v, "{name}: {n} vs {v}"),
								LimitComp::LessEq => assert!(n as i64 <= v, "{name}: {n} vs {v}"),
							}
						}
						want = Some(seen);
					}
					Some(want) => {
						assert_eq!(&seen, want, "{name} {cmp:?} differs from the network")
					}
				}
			}
		}
	}
}
