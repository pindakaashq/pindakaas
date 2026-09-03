//! Encoding a cardinality constraint as a sorting network.
//!
//! The literals are counted into an integer pinned to `k`, which is a
//! [`Count`] constraint, so the network
//! that encodes one encodes this too.

use crate::{
	constraint::{
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		count::{Count, SortedEncoder},
	},
	decision::integer::IntVar,
	ClauseDatabase, Coeff, Encoder, Result,
};

/// Encoder for the linear constraints that ∑ litᵢ ≷ k using a sorting network
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct SortingNetworkEncoder {
	/// Encoder used to encode the [`Count`](crate::constraint::count::Count) constraints.
	sorted_encoder: SortedEncoder,
}

impl SortingNetworkEncoder {
	/// Set the [`Encoder`] used for the [`Count`] constraint the network
	/// becomes.
	///
	/// Its comparator overrides are cleared, since a cardinality constraint
	/// asks for the sorted value itself rather than a bound on it.
	pub fn with_sorted_encoder(&mut self, mut sorted_encoder: SortedEncoder) -> &mut Self {
		let _ = sorted_encoder
			.with_overwrite_direct_cmp(None)
			.with_overwrite_recursive_cmp(None);
		self.sorted_encoder = sorted_encoder;
		self
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for SortingNetworkEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}


impl<Db> Encoder<Db, Cardinality> for SortingNetworkEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "sorting_network_encoder", skip_all, fields(constraint = card.trace_print()))
	)]
	fn encode(&self, db: &mut Db, card: &Cardinality) -> Result {
		let k: Coeff = card.k.into();
		let y = IntVar::new(k..=k).with_label("k");
		self.sorted_encoder
			.encode(db, &Count::new(card.lits.clone(), card.cmp.clone(), y))
	}
}

#[cfg(test)]
mod tests {
	use crate::helpers::tests::prelude::*;

	#[test]
	fn a_sorting_network_counts_exactly() {
		// The sorted encoder's comparator overrides let a merge state less than
		// it knows, which is a saving where a bound will do. A cardinality
		// constraint is not such a case: an equality encoded that way admits
		// counts it forbids. The network clears them, whether it made the
		// encoder itself or was handed one.
		let mut given = SortingNetworkEncoder::default();
		let _ = given.with_sorted_encoder(SortedEncoder::default());
		for enc in [SortingNetworkEncoder::default(), given] {
			let mut cnf = Cnf::default();
			let lits = cnf.new_var_range(4).iter_lits().collect_vec();
			let con = Cardinality {
				lits,
				cmp: LimitComp::Equal,
				k: PosCoeff::new(2),
			};
			enc.encode(&mut cnf, &con).unwrap();
			assert_checker(&cnf, &con);
		}
	}

	macro_rules! sorted_card_test_suite {
		($encoder:expr,$cmp:expr) => {
			use traced_test::test;

			use crate::helpers::tests::prelude::*;

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

			let expect = expect_file![format!(
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
