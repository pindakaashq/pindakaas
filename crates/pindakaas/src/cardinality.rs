//! This module contains representations and encoding algorithms for general
//! Boolean cardinality constraints.
//!
//! Cardinality constraints can be represented using the [`Cardinality`] type.
//! [`SortingNetworkEncoder`] can then be used to encode the constraint into
//! CNF, as well as [`Encoder`] implementations for [`NormalizedBoolLinear`].

use crate::{
	bool_linear::{Comparator, LimitComp, LinMarker, NormalizedBoolLinear, PosCoeff},
	cardinality_one::CardinalityOne,
	integer::IntVarEnc,
	sorted::{Sorted, SortedEncoder},
	AsDynClauseDatabase, Checker, ClauseDatabase, Coeff, Encoder, Lit, Result, Valuation,
};

// local marker trait, to ensure the previous definition only applies within
// this crate
pub(crate) trait CardMarker {}

#[derive(Clone, Debug)]
/// Linear constraint that enforces that ∑ litᵢ ≷ k.
///
/// Compared to [`NormalizedBoolLinear`], this constraint does not multiply
/// literals by coefficients.
///
/// All literals in the constraint are guaranteed to be from distinct Boolean
/// variables.
pub struct Cardinality {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

/// Encoder for the linear constraints that ∑ litᵢ ≷ k using a sorting network
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SortingNetworkEncoder {
	/// Encoder used to encode the [`Sorted`] constraints.
	sorted_encoder: SortedEncoder,
}

impl Cardinality {
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
		NormalizedBoolLinear::from(self.clone()).check(value)
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

// Automatically implement AtMostOne encoding when you can encode Cardinality
// constraints
impl<Db, Enc> Encoder<Db, CardinalityOne> for Enc
where
	Db: ClauseDatabase + ?Sized,
	Enc: Encoder<Db, Cardinality> + CardMarker,
{
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

impl<M: LinMarker> CardMarker for M {}

impl SortingNetworkEncoder {
	// TODO: Sorted is currently private.
	/// Set the [`Encoder`] used to encode the `Sorted` constraints within the
	/// sorting network.
	pub fn with_sorted_encoder(&mut self, sorted_encoder: SortedEncoder) -> &mut Self {
		self.sorted_encoder = sorted_encoder;
		self
	}
}

impl CardMarker for SortingNetworkEncoder {}

impl Default for SortingNetworkEncoder {
	fn default() -> Self {
		let mut sorted_encoder = SortedEncoder::default();
		let _ = sorted_encoder
			.with_overwrite_direct_cmp(None)
			.with_overwrite_recursive_cmp(None);
		Self { sorted_encoder }
	}
}

impl<Db> Encoder<Db, Cardinality> for SortingNetworkEncoder
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "sorting_network_encoder", skip_all, fields(constraint = card.trace_print()))
	)]
	fn encode(&self, db: &mut Db, card: &Cardinality) -> Result {
		self.sorted_encoder.encode(
			db,
			&Sorted::new(
				card.lits.as_slice(),
				card.cmp.clone(),
				&IntVarEnc::Const(card.k.into()),
			),
		)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	macro_rules! card_test_suite {
		($encoder:expr) => {
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
		};
	}

	macro_rules! sorted_card_test_suite {
		($encoder:expr,$cmp:expr) => {
			use itertools::Itertools;
			use traced_test::test;

			use crate::{
				bool_linear::{LimitComp, PosCoeff},
				cardinality::{Cardinality, SortingNetworkEncoder},
				helpers::tests::assert_solutions,
				sorted::{SortedEncoder, SortedStrategy},
				ClauseDatabase, Cnf, Encoder,
			};

			#[test]
			fn card_2_1() {
				test_card!($encoder, 2, $cmp, 1);
			}

			#[test]
			fn card_2_2() {
				test_card!($encoder, 2, $cmp, 2);
			}

			#[test]
			fn card_3_1() {
				test_card!($encoder, 3, $cmp, 1);
			}

			#[test]
			fn card_3_2() {
				test_card!($encoder, 3, $cmp, 2);
			}

			#[test]
			fn card_3_3() {
				test_card!($encoder, 3, $cmp, 3);
			}

			#[test]
			fn card_4_2() {
				test_card!($encoder, 4, $cmp, 2);
			}

			#[test]
			fn card_4_3() {
				test_card!($encoder, 4, $cmp, 3);
			}

			#[test]
			fn card_4_4() {
				test_card!($encoder, 4, $cmp, 4);
			}

			#[test]
			fn card_5_3() {
				test_card!($encoder, 5, $cmp, 3);
			}

			#[test]
			fn card_6_1() {
				test_card!($encoder, 6, $cmp, 1);
			}

			#[test]
			fn card_5_2() {
				test_card!($encoder, 5, $cmp, 1);
			}
		};
	}

	macro_rules! test_card {
		($encoder:expr,$n:expr,$cmp:expr,$k:expr) => {
			let mut cnf = Cnf::default();
			let vars = cnf.new_var_range($n).iter_lits().collect_vec();
			$encoder
				.encode(
					&mut cnf,
					&Cardinality {
						lits: vars.clone(),
						cmp: $cmp,
						k: PosCoeff::new($k),
					},
				)
				.unwrap();

			let expect = crate::helpers::tests::expect_file![format!(
				"cardinality/sorting_network/test_card_{}_{}_{}.sol",
				$n,
				$k,
				match $cmp {
					LimitComp::LessEq => "le",
					LimitComp::Equal => "eq",
				}
			)];
			assert_solutions(&cnf, vars, &expect);
		};
	}

	pub(crate) use card_test_suite;

	mod eq_direct {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let mut f = SortedEncoder::default();
				let _ = f
					.with_strategy(SortedStrategy::Direct)
					.with_overwrite_direct_cmp(None)
					.with_overwrite_recursive_cmp(None);
				let _ = e.with_sorted_encoder(f);
				e
			},
			LimitComp::Equal
		);
	}

	mod eq_recursive {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let mut f = SortedEncoder::default();
				let _ = f
					.with_strategy(SortedStrategy::Recursive)
					.with_overwrite_direct_cmp(None)
					.with_overwrite_recursive_cmp(None);
				let _ = e.with_sorted_encoder(f);
				e
			},
			LimitComp::Equal
		);
	}

	mod le_direct {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let mut f = SortedEncoder::default();
				let _ = f
					.with_strategy(SortedStrategy::Direct)
					.with_overwrite_direct_cmp(None)
					.with_overwrite_recursive_cmp(None);
				let _ = e.with_sorted_encoder(f);
				e
			},
			LimitComp::LessEq
		);
	}

	mod le_mixed {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let mut f = SortedEncoder::default();
				let _ = f
					.with_strategy(SortedStrategy::Mixed(2))
					.with_overwrite_direct_cmp(None)
					.with_overwrite_recursive_cmp(None);
				let _ = e.with_sorted_encoder(f);
				e
			},
			LimitComp::LessEq
		);
	}

	mod le_recursive {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let mut f = SortedEncoder::default();
				let _ = f
					.with_strategy(SortedStrategy::Recursive)
					.with_overwrite_direct_cmp(None)
					.with_overwrite_recursive_cmp(None);
				let _ = e.with_sorted_encoder(f);
				e
			},
			LimitComp::LessEq
		);
	}
}
