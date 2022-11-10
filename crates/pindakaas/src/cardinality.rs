use crate::{
	linear::{LimitComp, LinMarker, Linear, PosCoeff},
	CardinalityOne, Checker, ClauseDatabase, Coefficient, Encoder, Literal,
};

mod sorting_network;
pub use sorting_network::SortingNetworkEncoder;

#[derive(Clone, Debug)]
pub struct Cardinality<Lit: Literal, C: Coefficient> {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff<C>,
}

impl<Lit: Literal, C: Coefficient> From<CardinalityOne<Lit>> for Cardinality<Lit, C> {
	fn from(card1: CardinalityOne<Lit>) -> Self {
		Self {
			lits: card1.lits,
			cmp: card1.cmp,
			k: C::one().into(),
		}
	}
}

impl<Lit: Literal, C: Coefficient> Cardinality<Lit, C> {
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

impl<Lit: Literal, C: Coefficient> Checker for Cardinality<Lit, C> {
	type Lit = Lit;

	fn check(&self, solution: &[Self::Lit]) -> Result<(), crate::CheckError<Self::Lit>> {
		Linear::from(self.clone()).check(solution)
	}
}

// Automatically implement AtMostOne encoding when you can encode Cardinality constraints
impl<DB: ClauseDatabase, Enc: Encoder<DB, Cardinality<DB::Lit, i8>> + CardMarker>
	Encoder<DB, CardinalityOne<DB::Lit>> for Enc
{
	fn encode(&mut self, db: &mut DB, con: &CardinalityOne<DB::Lit>) -> crate::Result {
		self.encode(db, &Cardinality::<DB::Lit, i8>::from(con.clone()))
	}
}
// local marker trait, to ensure the previous definition only applies within this crate
pub(crate) trait CardMarker {}
impl<T: LinMarker> CardMarker for T {}

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
						lits: vec![-1, -2, 3],
						cmp: LimitComp::LessEq,
						k: 2.into()
					} =>
						vec![
							vec![-1, -2, -3],
							vec![-1, 2, -3],
							vec![-1, 2, 3],
							vec![1, -2, -3],
							vec![1, -2, 3],
							vec![1, 2, -3],
							vec![1, 2, 3],
						]
				);
			}

			#[test]
			fn test_card_eq_1_3() {
				assert_sol!(
					$encoder,
					3,
					&Cardinality {
						lits: vec![1, 2, 3],
						cmp: LimitComp::Equal,
						k: 1.into()
					}
					=>
					vec![
					vec![ 1,-2,-3],
					vec![-1, 2,-3],
					vec![-1,-2, 3],
					]
				);
			}


			#[test]
			fn test_card_eq_2_3() {
				assert_sol!(
					$encoder,
					3,
					&Cardinality {
						lits: vec![1, 2, 3],
						cmp: LimitComp::Equal,
						k: 2.into()
					}
					=>
					vec![
					vec![1, 2, -3],
					vec![1, -2, 3],
					vec![-1, 2, 3],
					]
				);
			}

			#[test]
			fn test_card_eq_2_4() {
				assert_sol!(
					$encoder,
					4,
					&Cardinality {
						lits: vec![1, 2, 3, 4],
						cmp: LimitComp::Equal,
						k: 2.into()
					} =>
					vec![
					  vec![1, 2, -3, -4],
					  vec![1, -2, 3, -4],
					  vec![-1, 2, 3, -4],
					  vec![1, -2, -3, 4],
					  vec![-1, 2, -3, 4],
					  vec![-1, -2, 3, 4],
					]
				);
			}



			#[test]
			fn test_card_eq_3_5() {
				assert_sol!(
					$encoder,
					5,
					&Cardinality {
						lits: vec![ 1,  2, 3, 4 ,5 ],
						cmp: LimitComp::Equal,
						k: 3.into()
					}
					=>
					vec![
					vec![1, 2, 3, -4, -5],
					vec![1, 2, -3, 4, -5],
					vec![1, -2, 3, 4, -5],
					vec![-1, 2, 3, 4, -5],
					vec![1, 2, -3, -4, 5],
					vec![1, -2, 3, -4, 5],
					vec![-1, 2, 3, -4, 5],
					vec![1, -2, -3, 4, 5],
					vec![-1, 2, -3, 4, 5],
					vec![-1, -2, 3, 4, 5],
					]
				);
			}



		};
	}

	pub(crate) use card_test_suite;
}
