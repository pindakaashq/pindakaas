use crate::{
	int::IntVarEnc,
	sorted::{Sorted, SortedEncoder},
	Cardinality, ClauseDatabase, Coefficient, Encoder, Result,
};

/// Encoder for the linear constraints that ∑ litsᵢ ≷ k using a sorting network
pub struct SortingNetworkEncoder {
	pub sorted_encoder: SortedEncoder,
}

impl Default for SortingNetworkEncoder {
	fn default() -> Self {
		Self {
			sorted_encoder: SortedEncoder {
				overwrite_direct_cmp: None,
				overwrite_recursive_cmp: None,
				..SortedEncoder::default()
			},
		}
	}
}

impl SortingNetworkEncoder {
	pub fn set_sorted_encoder(&mut self, sorted_encoder: SortedEncoder) -> &mut Self {
		self.sorted_encoder = sorted_encoder;
		self
	}
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Cardinality<DB::Lit, C>>
	for SortingNetworkEncoder
{
	fn encode(&mut self, db: &mut DB, card: &Cardinality<DB::Lit, C>) -> Result {
		self.sorted_encoder.encode(
			db,
			&Sorted::new(
				card.lits.as_slice(),
				card.cmp.clone(),
				&IntVarEnc::Const(*card.k),
			),
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		helpers::tests::assert_sol,
		linear::LimitComp,
		sorted::{SortedEncoder, SortedStrategy},
		Cardinality, Encoder,
	};

	macro_rules! test_card {
		($encoder:expr,$n:expr,$cmp:expr,$k:expr) => {
			assert_sol!(
				$encoder,
				$n,
				&Cardinality {
					lits: (1..=$n).collect(),
					cmp: $cmp,
					k: $k.into()
				}
			);
		};
	}

	macro_rules! sorted_card_test_suite {
		($encoder:expr,$cmp:expr) => {
			use super::*;

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

			// #[test]
			// fn test_card_12_7() {
			// 	test_card!($encoder, 12, $cmp, 7);
			// }
		};
	}

	mod le_recursive {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				#[allow(unused_mut)]
				let mut f = SortedEncoder {
					strategy: SortedStrategy::Recursive,
					overwrite_direct_cmp: None,
					overwrite_recursive_cmp: None,
					..SortedEncoder::default()
				};
				e.set_sorted_encoder(f);
				e
			},
			LimitComp::LessEq
		);
	}

	mod eq_recursive {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				#[allow(unused_mut)]
				let mut f = SortedEncoder {
					strategy: SortedStrategy::Recursive,
					overwrite_direct_cmp: None,
					overwrite_recursive_cmp: None,
					..SortedEncoder::default()
				};
				f.set_strategy(SortedStrategy::Recursive);
				e.set_sorted_encoder(f);
				e
			},
			LimitComp::Equal
		);
	}

	mod le_direct {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				#[allow(unused_mut)]
				let mut f = SortedEncoder {
					strategy: SortedStrategy::Direct,
					overwrite_direct_cmp: None,
					overwrite_recursive_cmp: None,
					..SortedEncoder::default()
				};
				e.set_sorted_encoder(f);
				e
			},
			LimitComp::LessEq
		);
	}

	mod eq_direct {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				#[allow(unused_mut)]
				let mut f = SortedEncoder {
					strategy: SortedStrategy::Direct,
					overwrite_direct_cmp: None,
					overwrite_recursive_cmp: None,
					..SortedEncoder::default()
				};
				e.set_sorted_encoder(f);
				e
			},
			LimitComp::Equal
		);
	}

	mod le_mixed {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				#[allow(unused_mut)]
				let mut f = SortedEncoder {
					strategy: SortedStrategy::Mixed(2),
					overwrite_direct_cmp: None,
					overwrite_recursive_cmp: None,
					..SortedEncoder::default()
				};
				e.set_sorted_encoder(f);
				e
			},
			LimitComp::LessEq
		);
	}
}
