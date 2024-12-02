use crate::{
	bool_linear::{LimitComp, LinMarker, NormalizedBoolLinear, PosCoeff},
	cardinality_one::CardinalityOne,
	CheckError, Checker, ClauseDatabase, Encoder, Lit, Result, Valuation,
};

// local marker trait, to ensure the previous definition only applies within this crate
pub(crate) trait CardMarker {}

#[derive(Clone, Debug)]
pub struct Cardinality {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

impl Cardinality {
	#[allow(
		dead_code,
		reason = "TODO: no idea why it has this warning but not on develop?"
	)]
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

// Automatically implement AtMostOne encoding when you can encode Cardinality constraints
impl<DB: ClauseDatabase, Enc: Encoder<DB, Cardinality> + CardMarker> Encoder<DB, CardinalityOne>
	for Enc
{
	fn encode(&self, db: &mut DB, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

impl<M: LinMarker> CardMarker for M {}

#[cfg(test)]
pub(crate) mod tests {

	macro_rules! card_test_suite {
		($encoder:expr) => {
			#[test]
			fn test_card_le_2_3() {
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
			fn test_card_eq_1_3() {
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
			fn test_card_eq_2_3() {
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
			fn test_card_eq_2_4() {
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
			fn test_card_eq_3_5() {
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

	pub(crate) use card_test_suite;
}
