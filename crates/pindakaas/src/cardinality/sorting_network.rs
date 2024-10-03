use crate::{
	int::IntVarEnc,
	sorted::{Sorted, SortedEncoder},
	Cardinality, ClauseDatabase, Encoder, Result,
};

/// Encoder for the linear constraints that ∑ litsᵢ ≷ k using a sorting network
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SortingNetworkEncoder {
	pub sorted_encoder: SortedEncoder,
}

impl Default for SortingNetworkEncoder {
	fn default() -> Self {
		let mut sorted_encoder = SortedEncoder::default();
		let _ = sorted_encoder
			.with_overwrite_direct_cmp(None)
			.with_overwrite_recursive_cmp(None);
		Self { sorted_encoder }
	}
}

impl SortingNetworkEncoder {
	pub fn set_sorted_encoder(&mut self, sorted_encoder: SortedEncoder) -> &mut Self {
		self.sorted_encoder = sorted_encoder;
		self
	}
}

impl<DB: ClauseDatabase> Encoder<DB, Cardinality> for SortingNetworkEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "sorting_network_encoder", skip_all, fields(constraint = card.trace_print()))
	)]
	fn encode(&self, db: &mut DB, card: &Cardinality) -> Result {
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
mod tests {
	macro_rules! test_card {
		($encoder:expr,$n:expr,$cmp:expr,$k:expr) => {
			let mut cnf = Cnf::default();
			let vars = cnf.next_var_range($n).unwrap().iter_lits().collect_vec();
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

	macro_rules! sorted_card_test_suite {
		($encoder:expr,$cmp:expr) => {
			use itertools::Itertools;
			use traced_test::test;

			use crate::{
				cardinality::sorting_network::SortingNetworkEncoder,
				helpers::tests::assert_solutions,
				linear::PosCoeff,
				sorted::{SortedEncoder, SortedStrategy},
				Cardinality, Cnf, Encoder, LimitComp, NextVarRange,
			};

			#[test]
			fn test_card_2_1() {
				test_card!($encoder, 2, $cmp, 1);
			}

			#[test]
			fn test_card_2_2() {
				test_card!($encoder, 2, $cmp, 2);
			}

			#[test]
			fn test_card_3_1() {
				test_card!($encoder, 3, $cmp, 1);
			}

			#[test]
			fn test_card_3_2() {
				test_card!($encoder, 3, $cmp, 2);
			}

			#[test]
			fn test_card_3_3() {
				test_card!($encoder, 3, $cmp, 3);
			}

			#[test]
			fn test_card_4_2() {
				test_card!($encoder, 4, $cmp, 2);
			}

			#[test]
			fn test_card_4_3() {
				test_card!($encoder, 4, $cmp, 3);
			}

			#[test]
			fn test_card_4_4() {
				test_card!($encoder, 4, $cmp, 4);
			}

			#[test]
			fn test_card_5_3() {
				test_card!($encoder, 5, $cmp, 3);
			}

			#[test]
			fn test_card_6_1() {
				test_card!($encoder, 6, $cmp, 1);
			}

			#[test]
			fn test_card_5_2() {
				test_card!($encoder, 5, $cmp, 1);
			}
		};
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
				let _ = e.set_sorted_encoder(f);
				e
			},
			LimitComp::LessEq
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
				let _ = e.set_sorted_encoder(f);
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
				let _ = e.set_sorted_encoder(f);
				e
			},
			LimitComp::LessEq
		);
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
				let _ = e.set_sorted_encoder(f);
				e
			},
			LimitComp::Equal
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
				let _ = e.set_sorted_encoder(f);
				e
			},
			LimitComp::LessEq
		);
	}
}
