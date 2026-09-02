//! The constraint that at most, or exactly, `k` of a set of literals hold.
//!
//! Every term counts for one, which is what separates it from a general
//! [`Linear`](super::bool_linear::Linear) and what lets the encoders below
//! count rather than add.

pub use crate::encoder::{
	adder::AdderEncoder, bdd::BddEncoder,
	sorting_network::SortingNetworkEncoder, swc::SwcEncoder, totalizer::TotalizerEncoder,
};
use rustc_hash::FxHashSet;

use crate::{
	constraint::{
		bool_linear::{Comparator, LimitComp, PosCoeff},
		cardinality_one::CardinalityOne,
		int_linear::NormalizedIntLinear,
	},
	decision::integer::IntVar,
	Checker, ClauseDatabase, Coeff, Lit, Result, Unsatisfiable, Valuation,
};

#[derive(Clone, Debug)]
/// Linear constraint that enforces that ∑ litᵢ ≷ k.
///
/// Compared to a general linear constraint, this one does not multiply literals
/// by coefficients.
///
/// All literals in the constraint are guaranteed to be from distinct Boolean
/// variables.
pub struct Cardinality {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

impl Cardinality {
	/// The constraint that `k` of `lits` hold, or at most `k` of them.
	///
	/// # Panics
	///
	/// If `k` is negative, or if two of `lits` are over the same variable —
	/// counting a variable twice is a linear constraint rather than a
	/// cardinality one.
	///
	/// # Examples
	///
	/// ```rust
	/// # use pindakaas::{
	/// #     constraint::{bool_linear::{AdderEncoder, LimitComp}, cardinality::Cardinality},
	/// #     ClauseDatabaseTools, Cnf, Encoder,
	/// # };
	/// let mut f = Cnf::default();
	/// let (a, b, c) = f.new_lits();
	///
	/// // At most two of the three.
	/// let con = Cardinality::new(vec![a, b, c], LimitComp::LessEq, 2);
	/// AdderEncoder::default().encode(&mut f, &con)?;
	/// # Ok::<(), pindakaas::Unsatisfiable>(())
	/// ```
	pub fn new(lits: Vec<Lit>, cmp: LimitComp, k: Coeff) -> Self {
		assert!(
			lits.iter().map(|l| l.var()).collect::<FxHashSet<_>>().len() == lits.len(),
			"a cardinality constraint counts distinct variables"
		);
		Self {
			lits,
			cmp,
			k: PosCoeff::new(k),
		}
	}

	/// Read the constraint as the linear constraint it is.
	///
	/// Its terms all count for one and none of them constrains another, so each
	/// is an integer worth one or nothing.
	pub(crate) fn as_linear<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<NormalizedIntLinear, Unsatisfiable> {
		let terms = self
			.lits
			.iter()
			.enumerate()
			.map(|(i, &l)| {
				// The literal is worth one when it holds and nothing when it
				// does not, which is a direct encoding of `0..=1`.
				IntVar::from_direct_encoding(db, 0..=1, &[!l, l])
					.map(|x| (PosCoeff::new(1), x.with_label(format!("x{i}"))))
			})
			.collect::<Result<Vec<_>, _>>()?;
		Ok(NormalizedIntLinear::new(terms, self.cmp.clone(), self.k))
	}

	/// Get the comparator of the cardinality constraint.
	pub fn comparator(&self) -> Comparator {
		self.cmp.clone().into()
	}

	/// Iterate over the literals of the cardinality constraint.
	pub fn iter_lits(&self) -> impl Iterator<Item = Lit> + '_ {
		self.lits.iter().copied()
	}

	/// Get the right-hand side constant against which the cardinality
	/// constraint compares its left-hand side literals.
	pub fn rhs(&self) -> Coeff {
		self.k.into()
	}

	#[cfg(any(feature = "tracing", test))]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(self.lits.iter().map(trace_print_lit), " + ");
		let op = if self.cmp == LimitComp::LessEq {
			"≤"
		} else {
			"="
		};
		format!("{x} {op} {:?}", *self.k)
	}
}

impl Checker for Cardinality {
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result {
		let count = self.lits.iter().filter(|&&l| value.value(l)).count() as Coeff;
		let holds = match self.cmp {
			LimitComp::LessEq => count <= *self.k,
			LimitComp::Equal => count == *self.k,
		};
		holds.then_some(()).ok_or(Unsatisfiable)
	}
}

impl From<CardinalityOne> for Cardinality {
	fn from(card1: CardinalityOne) -> Self {
		Self {
			lits: card1.lits,
			cmp: card1.cmp,
			k: PosCoeff::new(1),
		}
	}
}

/// Every encoder that takes a cardinality or an at-most-one constraint.
///
/// These used to follow from a pair of blanket implementations over marker
/// traits, which meant nothing said anywhere which encoder took which
/// constraint. Naming them costs a line each and makes the set something that
/// can be read, and lost by accident only if this stops compiling.
#[cfg(test)]
const _: () = {
	use crate::{
		constraint::{
			bool_linear::{AdderEncoder, BddEncoder, SwcEncoder, TotalizerEncoder},
		},
		Cnf, Encoder,
	};

	const fn takes<Db: ClauseDatabase + ?Sized, C, E: Encoder<Db, C>>() {}
	takes::<Cnf, Cardinality, AdderEncoder>();
	takes::<Cnf, Cardinality, BddEncoder>();
	takes::<Cnf, Cardinality, SwcEncoder>();
	takes::<Cnf, Cardinality, TotalizerEncoder>();
	takes::<Cnf, Cardinality, SortingNetworkEncoder>();
	takes::<Cnf, CardinalityOne, AdderEncoder>();
	takes::<Cnf, CardinalityOne, BddEncoder>();
	takes::<Cnf, CardinalityOne, SwcEncoder>();
	takes::<Cnf, CardinalityOne, TotalizerEncoder>();
	takes::<Cnf, CardinalityOne, SortingNetworkEncoder>();
};

#[cfg(test)]
pub(crate) mod tests {
	#[test]
	#[should_panic = "distinct variables"]
	fn a_repeated_variable_is_not_a_cardinality_constraint() {
		use crate::{
			constraint::{bool_linear::LimitComp, cardinality::Cardinality},
			ClauseDatabaseTools, Cnf,
		};
		let mut f = Cnf::default();
		let a = f.new_lit();
		let _ = Cardinality::new(vec![a, !a], LimitComp::LessEq, 1);
	}

	macro_rules! card_test_suite {
		($encoder:expr) => {
			mod cardinality {
				use traced_test::test;

				use crate::helpers::tests::prelude::*;

				#[test]
				fn card_le_2_3() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(3).iter_lits().collect_vec();
					$encoder
						.encode(
							&mut cnf,
							&Cardinality {
								lits: vars.clone(),
								cmp: LimitComp::LessEq,
								k: PosCoeff::new(2),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vars,
						&expect_file!["cardinality/test_card_le_2_3.sol"],
					)
				}

				#[test]
				fn card_eq_1_3() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(3).iter_lits().collect_vec();
					$encoder
						.encode(
							&mut cnf,
							&Cardinality {
								lits: vars.clone(),
								cmp: LimitComp::Equal,
								k: PosCoeff::new(1),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vars,
						&expect_file!["cardinality/test_card_eq_1_3.sol"],
					)
				}

				#[test]
				fn card_eq_2_3() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(3).iter_lits().collect_vec();
					$encoder
						.encode(
							&mut cnf,
							&Cardinality {
								lits: vars.clone(),
								cmp: LimitComp::Equal,
								k: PosCoeff::new(2),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vars,
						&expect_file!["cardinality/test_card_eq_2_3.sol"],
					)
				}

				#[test]
				fn card_eq_2_4() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(4).iter_lits().collect_vec();
					$encoder
						.encode(
							&mut cnf,
							&Cardinality {
								lits: vars.clone(),
								cmp: LimitComp::Equal,
								k: PosCoeff::new(2),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vars,
						&expect_file!["cardinality/test_card_eq_2_4.sol"],
					);
				}

				#[test]
				fn card_eq_3_5() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(5).iter_lits().collect_vec();
					$encoder
						.encode(
							&mut cnf,
							&Cardinality {
								lits: vars.clone(),
								cmp: LimitComp::Equal,
								k: PosCoeff::new(3),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vars,
						&expect_file!["cardinality/test_card_eq_3_5.sol"],
					);
				}
			}
		};
	}

	pub(crate) use card_test_suite;
}
