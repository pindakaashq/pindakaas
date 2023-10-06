use crate::{
	linear::{LimitComp, LinMarker, Linear, PosCoeff},
	CardinalityOne, CheckError, Checker, ClauseDatabase, Encoder, Lit, Valuation,
};

mod sorting_network;
pub use sorting_network::SortingNetworkEncoder;

#[derive(Clone, Debug)]
pub struct Cardinality {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
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

impl Cardinality {
	#[cfg(feature = "trace")]
	#[allow(dead_code)] // FIXME: Remove when used
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
	fn check<F: Valuation>(&self, value: F) -> Result<(), CheckError> {
		Linear::from(self.clone()).check(value)
	}
}

// Automatically implement AtMostOne encoding when you can encode Cardinality constraints
impl<DB: ClauseDatabase, Enc: Encoder<DB, Cardinality> + CardMarker> Encoder<DB, CardinalityOne>
	for Enc
{
	fn encode(&mut self, db: &mut DB, con: &CardinalityOne) -> crate::Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}
// local marker trait, to ensure the previous definition only applies within this crate
pub(crate) trait CardMarker {}
impl<T: LinMarker> CardMarker for T {}
impl CardMarker for SortingNetworkEncoder {}

#[cfg(test)]
pub(crate) mod tests {
	macro_rules! card_test_suite {
		($encoder:expr) => {

			#[test]
			fn test_card_le_2_3() {
				assert_sol!(
					$encoder,
					3,
					&Cardinality {
						lits: lits![-1, -2, 3],
						cmp: LimitComp::LessEq,
						k: PosCoeff::new(2)
					} =>
						vec![
							lits![-1, -2, -3],
							lits![-1, 2, -3],
							lits![-1, 2, 3],
							lits![1, -2, -3],
							lits![1, -2, 3],
							lits![1, 2, -3],
							lits![1, 2, 3],
						]
				);
			}

			#[test]
			fn test_card_eq_1_3() {
				assert_sol!(
					$encoder,
					3,
					&Cardinality {
						lits: lits![1, 2, 3],
						cmp: LimitComp::Equal,
						k: PosCoeff::new(1)
					}
					=>
					vec![
						lits![ 1,-2,-3],
						lits![-1, 2,-3],
						lits![-1,-2, 3],
					]
				);
			}


			#[test]
			fn test_card_eq_2_3() {
				assert_sol!(
					$encoder,
					3,
					&Cardinality {
						lits: lits![1, 2, 3],
						cmp: LimitComp::Equal,
						k: PosCoeff::new(2)
					}
					=>
					vec![
						lits![1, 2, -3],
						lits![1, -2, 3],
						lits![-1, 2, 3],
					]
				);
			}

			#[test]
			fn test_card_eq_2_4() {
				assert_sol!(
					$encoder,
					4,
					&Cardinality {
						lits: lits![1, 2, 3, 4],
						cmp: LimitComp::Equal,
						k: PosCoeff::new(2)
					} =>
					vec![
					  lits![1, 2, -3, -4],
					  lits![1, -2, 3, -4],
					  lits![-1, 2, 3, -4],
					  lits![1, -2, -3, 4],
					  lits![-1, 2, -3, 4],
					  lits![-1, -2, 3, 4],
					]
				);
			}



			#[test]
			fn test_card_eq_3_5() {
				assert_sol!(
					$encoder,
					5,
					&Cardinality {
						lits: lits![1, 2, 3, 4 ,5],
						cmp: LimitComp::Equal,
						k: PosCoeff::new(3)
					}
					=>
					vec![
						lits![1, 2, 3, -4, -5],
						lits![1, 2, -3, 4, -5],
						lits![1, -2, 3, 4, -5],
						lits![-1, 2, 3, 4, -5],
						lits![1, 2, -3, -4, 5],
						lits![1, -2, 3, -4, 5],
						lits![-1, 2, 3, -4, 5],
						lits![1, -2, -3, 4, 5],
						lits![-1, 2, -3, 4, 5],
						lits![-1, -2, 3, 4, 5],
					]
				);
			}
		};
	}

	pub(crate) use card_test_suite;
}
