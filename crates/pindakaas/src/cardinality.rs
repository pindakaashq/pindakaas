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
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result<(), CheckError> {
		Linear::from(self.clone()).check(value)
	}
}

// Automatically implement AtMostOne encoding when you can encode Cardinality constraints
impl<DB: ClauseDatabase, Enc: Encoder<DB, Cardinality> + CardMarker> Encoder<DB, CardinalityOne>
	for Enc
{
	fn encode(&self, db: &mut DB, con: &CardinalityOne) -> crate::Result {
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
				let mut cnf = Cnf::default();
				let vars = cnf.next_var_range(3).unwrap().iter_lits().collect_vec();
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
			fn test_card_eq_1_3() {
				let mut cnf = Cnf::default();
				let vars = cnf.next_var_range(3).unwrap().iter_lits().collect_vec();
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
			fn test_card_eq_2_3() {
				let mut cnf = Cnf::default();
				let vars = cnf.next_var_range(3).unwrap().iter_lits().collect_vec();
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
			fn test_card_eq_2_4() {
				let mut cnf = Cnf::default();
				let vars = cnf.next_var_range(4).unwrap().iter_lits().collect_vec();
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
			fn test_card_eq_3_5() {
				let mut cnf = Cnf::default();
				let vars = cnf.next_var_range(5).unwrap().iter_lits().collect_vec();
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
	pub(crate) use card_test_suite;
}
