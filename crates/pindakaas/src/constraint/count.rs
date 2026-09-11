//! Counting literals into an integer, `Σ lits ≷ y`.
//!
//! A cardinality constraint whose bound is a variable rather than a constant,
//! so that what was counted is available to whatever else mentions `y`. A
//! sorting network states it directly, where going through a general linear
//! constraint would count into intermediate integers first.

use itertools::Itertools;

pub use crate::encoder::sorting_network::{SortingNetworkEncoder, SortingNetworkStrategy};
use crate::{
	constraint::{
		int_linear::NormalizedIntLinear,
		linear::{LimitComp, LinExp, PosCoeff},
	},
	decision::integer::IntVar,
	Checker, ClauseDatabase, Lit, Result, Unsatisfiable, Valuation,
};

/// The constraint that `lits` add up to the integer `y`.
#[derive(Debug, Clone)]
pub struct Count {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) y: IntVar,
}

impl Count {
	/// The constraint that `lits` add up to `y`, or to at most `y`.
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
		let mut terms = self
			.lits
			.iter()
			.enumerate()
			.map(|(i, &lit)| {
				IntVar::from_direct_encoding(db, 0..=1, &[!lit, lit])
					.map(|x| (PosCoeff::new(1), x.with_label(format!("x{i}"))))
			})
			.collect::<Result<Vec<_>, _>>()?;
		// Counting the bound from its far end turns its coefficient positive,
		// and moves what it was worth into the constant.
		let k = self.y.min() + self.y.max();
		terms.push((PosCoeff::new(1), IntVar::mirrored(db, &self.y)?));
		Ok(NormalizedIntLinear::new(
			terms,
			self.cmp.clone(),
			PosCoeff::new(k),
		))
	}
}

impl Checker for Count {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<()> {
		let lhs = LinExp::from_terms(self.lits.iter().map(|x| (*x, 1)).collect_vec().as_slice())
			.value(sol)?;
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

/// Which encoders take a [`Count`], which rustdoc lists on the trait but the
/// compiler only checks if something names them.
#[cfg(test)]
const _: () = {
	use crate::{
		constraint::linear::{
			AdderEncoder, DecisionDiagramEncoder, WatchdogEncoder, MixedRadixEncoder,
			SequentialCounterEncoder, TotalizerEncoder,
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

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use traced_test::test;

	use super::{Count, SortingNetworkEncoder};
	use crate::{
		constraint::linear::{
			AdderEncoder, DecisionDiagramEncoder, LimitComp, MixedRadixEncoder, SequentialCounterEncoder,
			TotalizerEncoder,
		},
		decision::integer::IntVar,
		solver::{cadical::Cadical, SolveResult, Solver},
		ClauseDatabaseTools, Cnf, Encoder, Valuation,
	};

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

				let mut seen = Vec::new();
				let mut slv = Cadical::from(&cnf);
				loop {
					let read = match slv.solve() {
						SolveResult::Satisfied(sol) => {
							let n = lits.iter().filter(|&&l| sol.value(l)).count();
							let vals = lits
								.iter()
								.map(|&l| if sol.value(l) { l } else { !l })
								.collect_vec();
							(n, y.value(&sol), vals)
						}
						_ => break,
					};
					seen.push((read.0, read.1));
					if slv.add_clause(read.2.into_iter().map(|l| !l)).is_err() {
						break;
					}
				}
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
					Some(want) => assert_eq!(&seen, want, "{name} {cmp:?} differs from the network"),
				}
			}
		}
	}
}
