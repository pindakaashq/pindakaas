//! `pindakaas` is a collection of encoders to transform integer and
//! pseudo-Boolean (PB) constraints into conjunctive normal form (CNF). It
//! currently considers mostly linear constraints, which are in the form ∑
//! aᵢ·xᵢ ≷ k, where the aᵢ's and k are constant, xᵢ's are integer variables
//! or boolean literals, and ≷ can be the relationship ≤, =, or ≥. Two forms
//! of PB constraints are seen as special forms of PB constraints: ensuring a
//! set of booleans is *At Most One (AMO)* or *At Most K (AMK)*. Specialised
//! encodings are used when these cases are detected.

use std::clone::Clone;
use std::cmp::Eq;
use std::error::Error;
use std::fmt;
use std::hash::Hash;
use std::ops::Neg;

use itertools::Itertools;
use num::traits::{NumAssignOps, NumOps};
use num::{PrimInt, Signed, Unsigned};

mod adder;
mod aggregate;
mod helpers;
mod totalizer;

pub use aggregate::BoolLin;

/// Literal is the super-trait for types that can be used to represent boolean
/// literals in this library.
///
/// Literals need to implement the following trait to be used as literals:
///
///  - [`std::clone::Clone`] to allow creating a new copy of the literal to create clauses.
///
///  - [`std::ops::Neg`] to allow the negation literals.
///
///  - [`std::cmp::Eq`] and [`std::hash::Hash`] to allow PB constraints to be
///    simplified
pub trait Literal: fmt::Debug + Clone + Eq + Hash {
	/// Returns `true` when the literal a negated boolean variable.
	fn is_negated(&self) -> bool;
	fn negate(&self) -> Self;
}
impl<T: Signed + fmt::Debug + Clone + Eq + Hash + Neg<Output = Self>> Literal for T {
	fn is_negated(&self) -> bool {
		self.is_negative()
	}
	fn negate(&self) -> Self {
		-(self.clone())
	}
}

/// Unsatisfiable is a error type to returned when the problem being encoding is found to be
/// inconsistent.
#[derive(Debug, PartialEq, Eq, PartialOrd)]
pub struct Unsatisfiable;
impl Error for Unsatisfiable {}
impl fmt::Display for Unsatisfiable {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Problem inconsistency detected")
	}
}
pub type Result<T = (), E = Unsatisfiable> = std::result::Result<T, E>;

/// Coefficient in PB constraints are represented by types that implement the
/// `Coefficient` constraint.
pub trait Coefficient: Signed + PrimInt + NumAssignOps + NumOps + fmt::Debug {}
impl<T: Signed + PrimInt + NumAssignOps + NumOps + fmt::Debug> Coefficient for T {}
/// PositiveCoefficient is a trait used for types used for coefficients that
/// have been simplified.
pub trait PositiveCoefficient:
	Unsigned + PrimInt + NumAssignOps + NumOps + Hash + fmt::Debug
{
}
impl<T: Unsigned + PrimInt + NumAssignOps + NumOps + Hash + fmt::Debug> PositiveCoefficient for T {}

/// IntEncoding is a enumerated type use to represent Boolean encodings of integer variables within
/// this library
pub enum IntEncoding<'a, Lit: Literal, C: Coefficient> {
	/// The Direct variant represents a integer variable encoded using domain or direct encoding of
	/// an integer variable. Each given Boolean literal represents whether the integer takes the
	/// associated value (i.e., X = (first+i) ↔ vals\[i\]).
	Direct { first: C, vals: &'a [Lit] },
	/// The Order variant represents a integer variable using an order encoding. Each given Boolean
	/// literal represents whether the integer is bigger than the associated value
	/// (i.e., X > (first+i) ↔ vals\[i\]).
	Order { first: C, vals: &'a [Lit] },
	/// The Log variant represents a integer variable using a two's complement encoding.
	/// The sum of the Boolean literals multiplied by their associated power of two represents value
	/// of the integer (i.e., X = ∑ 2ⁱ·bits\[i\]).
	Log { signed: bool, bits: &'a [Lit] },
}

// TODO just temporary until I find out how to use IntEncodings for this
#[derive(Debug, Clone)]
pub enum Constraint<Lit> {
	Amo(Vec<Lit>),
	Ic(Vec<Lit>),
}

// TODO how can we support both Part(itions) of "terms" ( <Lit, C> for pb constraints) and just lits (<Lit>) for AMK/AMO's?
// TODO add EO, and probably something for Unconstrained
#[derive(Debug)]
pub enum Part<Lit, C> {
	Amo(Vec<(Lit, C)>),
	Ic(Vec<(Lit, C)>),
}

impl<Lit, C> Part<Lit, C> {
	fn iter(&self) -> std::slice::Iter<(Lit, C)> {
		match self {
			Part::Amo(terms) => terms.iter(),
			Part::Ic(terms) => terms.iter(),
		}
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Comparator {
	LessEq,
	Equal,
	GreaterEq,
}

/// The `ClauseDatabase` trait is the common trait implemented by types that are
/// used to manage the encoding of PB constraints and contain their output. This
/// trait can be used for all encoding methods in this library.
///
/// This trait is a supertrait of [`ClauseSink`], which means that implementers
/// should have a [`ClauseSink::add_clause`] method. Futhermore, implementers
/// are required to have a [`Self::new_var`] method.
pub trait ClauseDatabase: ClauseSink {
	/// Method to be used to receive a new Boolean variable that can be used in
	/// the encoding of a constraint.
	fn new_var(&mut self) -> Self::Lit;

	/// Encode an integer linear constraint
	fn encode_int_lin<C: Coefficient + TryInto<PC>, PC: PositiveCoefficient>(
		&mut self,
		coeff: &[C],
		vars: &[IntEncoding<Self::Lit, C>],
		cmp: Comparator,
		k: C,
	) -> Result {
		assert_eq!(coeff.len(), vars.len());

		// TODO: Actually deal with the fact that these constraints are integers
		let mut bool_coeff = Vec::new();
		let mut bool_vars = Vec::new();
		let mut k = k;

		for i in 0..coeff.len() {
			match &vars[i] {
				IntEncoding::Direct { first, vals } => {
					let mut counter = *first;
					for j in 0..vals.len() {
						bool_coeff.push(coeff[i] * counter);
						bool_vars.push(vals[j].clone());
						counter += C::one();
					}
				}
				IntEncoding::Order { first, vals } => {
					k -= *first * coeff[i];
					for i in 0..vals.len() {
						bool_coeff.push(coeff[i]);
						bool_vars.push(vals[i].clone());
					}
				}
				IntEncoding::Log { signed, bits } => {
					let two = C::one() + C::one();
					for i in 0..bits.len() {
						bool_coeff.push(coeff[i] * two.pow(i as u32));
						bool_vars.push(bits[i].clone());
					}
					if *signed {
						let last_coeff = bool_coeff.last_mut().unwrap();
						*last_coeff = -*last_coeff;
					}
				}
			}
		}

		self.encode_bool_lin(&bool_coeff, &bool_vars, cmp, k, &[])
	}

	/// Encode a Boolean linear constraint
	fn encode_bool_lin<C: Coefficient + TryInto<PC>, PC: PositiveCoefficient>(
		&mut self,
		coeff: &[C],
		lits: &[Self::Lit],
		cmp: Comparator,
		k: C,
		cons: &[Constraint<Self::Lit>], // slice
	) -> Result {
		let constraint = BoolLin::aggregate(self, coeff, lits, cmp, k, cons)?;

		self.encode_aggregated_bool_lin(&constraint)
	}

	fn encode_aggregated_bool_lin<PC: PositiveCoefficient>(
		&mut self,
		constraint: &BoolLin<PC, Self::Lit>,
	) -> Result {
		use BoolLin::*;
		// TODO: Make better educated choices
		match constraint {
			LinEqual { terms, k } => self.encode_bool_lin_eq_adder(terms, *k),
			LinLessEq { terms, k } => self.encode_bool_lin_le_adder(terms, *k),
			AtMostK { lits, k } => self.encode_bool_lin_le_adder(
				// &lits.iter().map(|l| (l.clone(), PC::one())).collect(),
				lits.iter()
					.map(|l| Part::Amo(vec![(l.clone(), PC::one())]))
					.collect::<Vec<_>>()
					.as_slice(),
				*k,
			),
			EqualK { lits, k } => self.encode_bool_lin_eq_adder(
				// &lits.iter().map(|l| (l.clone(), PC::one())).collect(),
				lits.iter()
					.map(|l| Part::Amo(vec![(l.clone(), PC::one())]))
					.collect::<Vec<_>>()
					.as_slice(),
				*k,
			),
			AtMostOne { lits } => self.encode_amo_pairwise(lits),
			Trivial => Ok(()),
		}
	}

	/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
	fn encode_bool_lin_eq_adder<PC: PositiveCoefficient>(
		&mut self,
		terms: &[Part<Self::Lit, PC>],
		k: PC,
	) -> Result {
		adder::encode_bool_lin_adder(self, terms, Comparator::Equal, k)
	}

	/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
	fn encode_bool_lin_le_adder<PC: PositiveCoefficient>(
		&mut self,
		terms: &[Part<Self::Lit, PC>],
		k: PC,
	) -> Result {
		adder::encode_bool_lin_adder(self, terms, Comparator::LessEq, k)
	}

	/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a totalizer
	fn encode_bool_lin_le_totalizer<PC: PositiveCoefficient>(
		&mut self,
		partition: &[Part<Self::Lit, PC>],
		k: PC,
	) -> Result {
		totalizer::encode_bool_lin_le_totalizer(self, partition, Comparator::LessEq, k)
	}

	fn encode_amo_ladder(&mut self, xs: &Vec<Self::Lit>) -> Result {
		debug_assert!(xs.iter().duplicates().count() == 0);
		debug_assert!(xs.len() >= 2);

		// TODO could be slightly optimised to not introduce fixed lits
		let mut a = self.new_var(); // y_v-1
		self.add_clause(&[a.clone()])?;
		for x in xs {
			let b = self.new_var(); // y_v
			self.add_clause(&[b.negate(), a.clone()])?; // y_v -> y_v-1

			// "Channelling" clauses for x_v <-> (y_v-1 /\ ¬y_v)
			self.add_clause(&[x.negate(), a.clone()])?; // x_v -> y_v-1
			self.add_clause(&[x.negate(), b.negate()])?; // x_v -> ¬y_v
			self.add_clause(&[a.negate(), b.clone(), x.clone()])?; // (y_v-1 /\ ¬y_v) -> x=v
			a = b;
		}
		self.add_clause(&[a.negate()])?;
		Ok(())
	}
}

/// Types that abide by the `ClauseSink` trait can be used as the output for the
/// constraint encodings. This trait also contains basic encodings that never
/// create nh literals.
///
/// To satisfy the trait, the type must implement a
/// [`Self::add_clause`] method.
pub trait ClauseSink {
	/// Type used to represent a Boolean literal in the constraint input and
	/// generated clauses.
	type Lit: Literal;

	/// Add a clause to the `ClauseSink`. The sink is allowed to return `false`
	/// only when the collection of clauses has been *proven* to be
	/// unsatisfiable. This is used as a signal to the encoder that any
	/// subsequent encoding effort can be abandoned.
	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result;

	/// Adds an encoding for an At Most One constraints to `sink` that for every
	/// pair of literals from `lits` states that one of the literals has to be
	/// `false`.
	///
	/// # Required Preprocessing
	///
	/// - `lits` is expected to contain at least 2 literals. In cases where an
	///   AMO constraint has fewer literals, the literals can either be removed
	///   for the problem or the problem is already unsatisfiable
	fn encode_amo_pairwise(&mut self, lits: &Vec<Self::Lit>) -> Result {
		// Precondition: there are multiple literals in the AMO constraint
		debug_assert!(lits.iter().duplicates().count() == 0);
		debug_assert!(lits.len() >= 2);
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for (a, b) in lits.iter().tuple_combinations() {
			self.add_clause(&[a.negate(), b.negate()])?
		}
		Ok(())
	}
}

impl<Lit: Literal> ClauseSink for Vec<Vec<Lit>> {
	type Lit = Lit;
	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
		self.push(cl.iter().map(|x| (*x).clone()).collect());
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use splr::{
		types::{CNFDescription, Instantiate},
		Config, SatSolverIF, Solver, SolverError,
	};
	use std::collections::HashSet;

	#[test]
	fn test_int_literals() {
		assert!(is_lit(1i8));
		assert!(is_lit(1i16));
		assert!(is_lit(1i32));
		assert!(is_lit(1i64));
		assert!(is_lit(1i128));
	}
	fn is_lit<T: Literal>(_: T) -> bool {
		true
	}

	#[test]
	fn test_encoders() {
		// +7*x1 +10*x2 +4*x3 +4*x4 <= 9
		let mut two = TestDB::new(4).expect_solutions(vec![
			vec![-1, -2, -3, -4],
			vec![1, -2, -3, -4],
			vec![-1, -2, 3, -4],
			vec![-1, -2, -3, 4],
		]);
		// two.add_clause(&[-5]).unwrap();
		// TODO encode this if encoder does not support constraint
		assert!(two.encode_amo_pairwise(&vec![1, 2]).is_ok());
		assert!(two.encode_amo_pairwise(&vec![3, 4]).is_ok());
		assert!(two
			.encode_bool_lin::<i64, u64>(
				&[7, 10, 4, 4],
				&[1, 2, 3, 4],
				crate::Comparator::LessEq,
				9,
				&[Constraint::Amo(vec![1, 2]), Constraint::Amo(vec![3, 4])],
			)
			.is_ok());
		two.check_complete();
	}

	#[test]
	fn test_amo_ladder() {
		let mut two = TestDB::new(2).expect_clauses(vec![
			vec![-1, 3],
			vec![1, -3, 4],
			vec![-1, -4],
			vec![-2, -5],
			vec![-2, 4],
			vec![3],
			vec![-4, 3],
			vec![-4, 5, 2],
			vec![-5, 4],
			vec![-5],
		]);
		two.encode_amo_ladder(&vec![1, 2]).unwrap();
		two.check_complete();
		assert_eq!(two.num_var(), 5);
	}

	#[test]
	fn test_coefficients() {
		assert!(is_coeff(1i8));
		assert!(is_coeff(1i16));
		assert!(is_coeff(1i32));
		assert!(is_coeff(1i64));
		assert!(is_coeff(1i128));
	}
	fn is_coeff<T: Coefficient>(_: T) -> bool {
		true
	}

	#[test]
	fn test_positive_coefficients() {
		assert!(is_poscoeff(1u8));
		assert!(is_poscoeff(1u16));
		assert!(is_poscoeff(1u32));
		assert!(is_poscoeff(1u64));
		assert!(is_poscoeff(1u128));
	}
	fn is_poscoeff<T: PositiveCoefficient>(_: T) -> bool {
		true
	}

	#[test]
	fn test_amo_pairwise() {
		// AMO on two literals
		let mut two = TestDB::new(2)
			.expect_clauses(vec![vec![-1, -2]])
			.with_check(|sol| check_pb(&vec![1, 2], &vec![1, 1], Comparator::LessEq, 1, sol));
		two.encode_amo_pairwise(&vec![1, 2]).unwrap();
		two.check_complete();
		// AMO on a negated literals
		let mut two = TestDB::new(2)
			.expect_clauses(vec![vec![1, -2]])
			.with_check(|sol| check_pb(&vec![-1, 2], &vec![1, 1], Comparator::LessEq, 1, sol));
		two.encode_amo_pairwise(&vec![-1, 2]).unwrap();
		two.check_complete();
		// AMO on three literals
		let mut three = TestDB::new(3)
			.expect_clauses(vec![vec![-1, -2], vec![-1, -3], vec![-2, -3]])
			.with_check(|sol| check_pb(&vec![1, 2, 3], &vec![1, 1, 1], Comparator::LessEq, 1, sol));
		three.encode_amo_pairwise(&vec![1, 2, 3]).unwrap();
		three.check_complete();
	}

	#[test]
	fn test_pb_encode() {
		let mut two = TestDB::new(4)
			.expect_clauses(vec![vec![-4], vec![-3, -1], vec![-2, -1], vec![-3, -2]])
			.expect_solutions(vec![
				vec![-1, -2, -3, -4],
				vec![-1, -2, 3, -4],
				vec![-1, 2, -3, -4],
				vec![1, -2, -3, -4],
			]);
		assert!(two
			.encode_bool_lin::<i64, u64>(
				&[1, 1, 1, 2],
				&[1, 2, 3, 4],
				crate::Comparator::LessEq,
				1,
				&[]
			)
			.is_ok());
		two.check_complete();
	}

	pub struct TestDB {
		slv: Solver,
		/// Clauses expected by the test case
		clauses: Option<Vec<(bool, Vec<i32>)>>,
		/// Solutions expected by the test case
		solutions: Option<Vec<Vec<i32>>>,
		check: Option<fn(&[i32]) -> bool>,
	}

	impl TestDB {
		pub fn new(num_var: i32) -> TestDB {
			TestDB {
				slv: Solver::instantiate(
					&Config::default(),
					&CNFDescription {
						num_of_variables: num_var as usize,
						..CNFDescription::default()
					},
				),
				clauses: None,
				solutions: None,
				check: None,
			}
		}

		pub fn expect_clauses(mut self, mut clauses: Vec<Vec<i32>>) -> TestDB {
			for cl in &mut clauses {
				cl.sort_by(|a, b| a.abs().cmp(&b.abs()));
			}
			clauses.sort();
			self.clauses = Some(clauses.into_iter().map(|cl| (false, cl)).collect());
			self
		}

		pub fn expect_solutions(mut self, mut solutions: Vec<Vec<i32>>) -> TestDB {
			for sol in &mut solutions {
				sol.sort_by(|a, b| a.abs().cmp(&b.abs()));
			}
			solutions.sort();
			self.solutions = Some(solutions);
			self
		}

		pub fn with_check(mut self, checker: fn(&[i32]) -> bool) -> TestDB {
			self.check = Some(checker);
			self
		}

		pub fn check_complete(&mut self) {
			if let Some(clauses) = &self.clauses {
				let missing: Vec<Vec<i32>> = clauses
					.iter()
					.filter(|exp| exp.0 == false)
					.map(|exp| exp.1.clone())
					.collect();
				// assert!(false, "{:?} {:?}", clauses, missing);
				assert!(
					missing.is_empty(),
					"clauses are missing from the encoding: {:?}",
					missing
				);
			}
			if self.solutions.is_none() && self.check.is_none() {
				return;
			}
			let mut from_slv: Vec<Vec<i32>> = self.slv.iter().collect();
			for sol in &mut from_slv {
				sol.sort_by(|a, b| a.abs().cmp(&b.abs()));
			}
			if let Some(check) = &self.check {
				for sol in &mut from_slv {
					assert!(check(sol), "solution {:?} failed check", sol)
				}
			}
			if let Some(solutions) = &self.solutions {
				// we are only interested in literals present in the expected solutions (and not in auxiliary variables)
				let vars = HashSet::<i32>::from_iter(
					solutions
						.iter()
						.flat_map(|sol| sol.iter().map(|lit| lit.abs())),
				);

				let mut from_slv: Vec<Vec<i32>> = HashSet::<Vec<i32>>::from_iter(
					from_slv
						.into_iter()
						.map(|xs| xs.into_iter().filter(|x| vars.contains(&x.abs())).collect()),
				)
				.into_iter()
				.collect();
				from_slv.sort();

				assert_eq!(
					&from_slv, solutions,
					"solutions founds by the solver do not match expected set of solutions"
				);
			}
		}

		pub fn num_var(&self) -> usize {
			self.slv.asg.num_vars
		}
	}

	impl ClauseSink for TestDB {
		type Lit = i32;

		fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
			let mut cl = Vec::from(cl);
			cl.sort_by(|a, b| a.abs().cmp(&b.abs()));
			if let Some(clauses) = &mut self.clauses {
				let mut found = false;
				for exp in clauses {
					if cl == exp.1 {
						exp.0 = true;
						found = true;
						break;
					}
				}
				assert!(found, "unexpected clause: {:?}", cl);
			}

			match match cl.len() {
				0 => return Err(Unsatisfiable),
				1 => self.slv.add_assignment(cl[0]),
				_ => self.slv.add_clause(cl),
			} {
				Ok(_) => Ok(()),
				Err(err) => match err {
					SolverError::EmptyClause => Ok(()),
					SolverError::RootLevelConflict(_) => Err(Unsatisfiable),
					err => {
						panic!("unexpected solver error: {:?}", err);
					}
				},
			}
		}
	}

	impl ClauseDatabase for TestDB {
		fn new_var(&mut self) -> Self::Lit {
			self.slv.add_var() as i32
		}
	}

	pub fn check_pb(
		lits: &Vec<i32>,
		coefs: &Vec<i32>,
		cmp: Comparator,
		k: i32,
		// cons: Vec<Constraint<i32>>,
		sol: &[i32],
	) -> bool {
		assert_eq!(lits.len(), coefs.len());
		// TODO check side constraints?
		let lhs = lits.iter().zip(coefs.iter()).fold(0, |acc, (lit, coef)| {
			let a = sol.iter().find(|x| x.abs() == lit.abs());
			acc + (lit == a.unwrap()) as i32 * coef
		});
		match cmp {
			Comparator::LessEq => lhs <= k,
			Comparator::Equal => lhs == k,
			Comparator::GreaterEq => lhs >= k,
		}
	}
}
