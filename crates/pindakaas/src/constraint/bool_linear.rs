//! This module contains representations and encoding algorithms for general
//! Boolean linear constraints.
//!
//! Boolean linear constraints can be modelled using [`LinExp`] and
//! subsequently [`Linear`]. These representations can then be normalized
//! and simplified using
//! [`BoolLinAggregator`](crate::encoder::aggregate::BoolLinAggregator), which
//! reads the integers a group of literals stands for and yields a
//! [`NormalizedIntLinear`](crate::int_linear::NormalizedIntLinear). That is
//! what the [`AdderEncoder`], [`BddEncoder`], [`SwcEncoder`] and
//! [`TotalizerEncoder`] encode.
//!
//! This module contains some additional helper types that can be used to
//! simplify this encoding process.
//! [`StaticLinEncoder`](crate::encoder::aggregate::StaticLinEncoder) can help
//! choose an encoder based on the
//! [`LinVariant`](crate::constraint::linear::LinVariant) produced by
//! [`BoolLinAggregator`](crate::encoder::aggregate::BoolLinAggregator).
//! [`LinearEncoder`](crate::encoder::aggregate::LinearEncoder) can be used to
//! pipeline [`BoolLinAggregator`](crate::encoder::aggregate::BoolLinAggregator)
//! and a [`LinVariant`](crate::constraint::linear::LinVariant)
//! [`Encoder`](crate::Encoder).

use std::{
	fmt::{self, Display},
	ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign, Neg, Sub, SubAssign},
};

use itertools::Itertools;

pub use crate::encoder::{
	adder::AdderEncoder, bdd::BddEncoder, swc::SwcEncoder, totalizer::TotalizerEncoder,
};
use crate::{decision::integer::IntVar, Checker, Coeff, Lit, Result, Unsatisfiable, Valuation};

#[derive(Clone, Debug)]
/// A linear combination of boolean variables, where Boolean literals are
/// multiplied by constant coefficients and added together.
pub struct LinExp {
	/// The terms of the expression, in the order they were written.
	pub(crate) terms: Vec<LinTerm>,
	/// Additive constant
	pub(crate) add: Coeff,
	/// Multiplicative contant
	pub(crate) mult: Coeff,
}

/// A term of a linear expression, and what it is worth.
///
/// A literal counts for its coefficient when it holds and nothing when it does
/// not; an integer variable counts for its coefficient times whichever of its
/// values it takes.
#[derive(Clone, Debug)]
pub enum LinTerm {
	/// A Boolean literal.
	Bool(Lit, Coeff),
	/// An integer variable.
	Int(IntVar, Coeff),
}

impl LinTerm {
	/// What the term is multiplied by.
	pub fn coefficient(&self) -> Coeff {
		match self {
			LinTerm::Bool(_, c) | LinTerm::Int(_, c) => *c,
		}
	}

	/// The term with its coefficient multiplied by `c`.
	fn scaled(self, c: Coeff) -> Self {
		match self {
			LinTerm::Bool(l, w) => LinTerm::Bool(l, w * c),
			LinTerm::Int(x, w) => LinTerm::Int(x, w * c),
		}
	}
}

#[derive(Debug, Clone)]
/// A Boolean linear constraint that can be used to constrain a linear
/// combination of boolean variables.
///
/// Note that this type of constraint is often referred to in literature under
/// the more general term of pseudo-Boolean constraints.
///
/// The constraint compares a [`LinExp`] to a constant using a
/// [`Comparator`], where the expression takes the left hand side of the
/// comparison and the constant takes the right hand side.
pub struct Linear {
	/// Expression being constrained
	pub(crate) exp: LinExp,
	/// Comparator when exp is on the left hand side and k is on the right hand
	/// side
	pub(crate) cmp: Comparator,
	/// Coefficient providing the upper bound or lower bound to exp, or both
	pub(crate) k: Coeff,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
/// A comparator type used in linear and cardinality constraints.
pub enum Comparator {
	/// Force the left hand side of the constraint to be less than or equal to
	/// the right hand side, i.e. `exp ≤ k`.
	LessEq,
	/// Force the left hand side of the constraint to be equal to the right hand
	/// side, i.e. `exp = k`.
	Equal,
	/// Force the left hand side of the constraint to be greater than or equal
	/// to the right hand side, i.e. `exp ≥ k`.
	GreaterEq,
}

impl Comparator {
	/// The comparator that holds when the sides are swapped.
	pub(crate) fn reverse(self) -> Self {
		match self {
			Comparator::LessEq => Comparator::GreaterEq,
			Comparator::Equal => Comparator::Equal,
			Comparator::GreaterEq => Comparator::LessEq,
		}
	}

	/// The inequalities that together mean the same as this comparator.
	pub(crate) fn split(self) -> Vec<Self> {
		match self {
			Comparator::Equal => vec![Comparator::LessEq, Comparator::GreaterEq],
			cmp => vec![cmp],
		}
	}
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
/// A comparator that has been limited to a either `Equal` or `LessEq`.
///
/// This type is used to ensure that the comparator of [`Cardinality`] and
/// [`CardinalityOne`] constraints, and of a normalized linear constraint, are
/// limited to a specific set of values.
pub(crate) enum LimitComp {
	Equal,
	LessEq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// PosCoeff is a type for coefficients that are guaranteed by the programmer to
/// be 0 or greater.
pub struct PosCoeff(pub(crate) Coeff);

impl LinExp {
	/// Add a constant to the linear expression
	///
	/// Note that this is a more explicit version of the `+` or `+=` operator.
	pub fn add_constant(mut self, k: Coeff) -> Self {
		self.add += k;
		self
	}

	/// Add a literal to the linear expression, taking the value `0` if `false`
	/// and `1` if `true`.
	///
	/// Note that this is a more explicit version of the `+` or `+=` operator.
	pub fn add_lit(mut self, lit: Lit) -> Self {
		self.terms.push(LinTerm::Bool(lit, 1));
		self
	}

	/// Create a linear expression from a slice of coefficients and literals,
	/// where each literal is multiplied by the coefficient in the
	/// corresponding position.
	///
	/// Note that the number of coefficients and literals must be equal.
	pub fn from_slices(coeffs: &[Coeff], lits: &[Lit]) -> Self {
		assert_eq!(
			coeffs.len(),
			lits.len(),
			"the number of weights and literals must be equal"
		);
		Self {
			terms: lits
				.iter()
				.zip(coeffs)
				.map(|(&l, &c)| LinTerm::Bool(l, c))
				.collect(),
			..Default::default()
		}
	}

	/// Create a linear expression from a slice of terms, where each term
	/// consist of a literal and coefficient and the former will be multiplied
	/// by the latter.
	pub fn from_terms(terms: &[(Lit, Coeff)]) -> Self {
		Self {
			terms: terms.iter().map(|&(l, c)| LinTerm::Bool(l, c)).collect(),
			..Default::default()
		}
	}

	/// Iterate over the terms of the linear expression, consisting of a literal
	/// and the coefficient by which it is multiplied.
	pub fn terms(&self) -> impl Iterator<Item = (Lit, Coeff)> + '_ {
		self.terms.iter().filter_map(|t| match t {
			LinTerm::Bool(l, c) => Some((*l, *c)),
			LinTerm::Int(..) => None,
		})
	}

	/// Iterate over the terms of the expression that are integer variables,
	/// each with the coefficient by which it is multiplied.
	pub fn int_terms(&self) -> impl Iterator<Item = (&IntVar, Coeff)> + '_ {
		self.terms.iter().filter_map(|t| match t {
			LinTerm::Int(x, c) => Some((x, *c)),
			LinTerm::Bool(..) => None,
		})
	}

	pub(crate) fn value<F: Valuation + ?Sized>(&self, sol: &F) -> Result<Coeff> {
		let mut total = self.add;
		for term in &self.terms {
			total += match term {
				LinTerm::Bool(l, c) if sol.value(*l) => *c,
				LinTerm::Bool(..) => 0,
				LinTerm::Int(x, c) => c * x.value(sol),
			};
		}
		Ok(total * self.mult)
	}
}

impl Add for LinExp {
	type Output = LinExp;

	fn add(mut self, rhs: Self) -> Self::Output {
		self += rhs;
		self
	}
}

impl Add<Coeff> for LinExp {
	type Output = LinExp;

	fn add(mut self, rhs: Coeff) -> Self::Output {
		self += rhs;
		self
	}
}

impl AddAssign for LinExp {
	fn add_assign(&mut self, rhs: Self) {
		// The pending multiplier reaches everything already here before
		// anything is added beside it.
		if self.mult != 1 {
			self.add *= self.mult;
			for term in self.terms.drain(..).collect_vec() {
				self.terms.push(term.scaled(self.mult));
			}
		}
		self.mult = 1;
		self.add += rhs.add * rhs.mult;
		self.terms
			.extend(rhs.terms.into_iter().map(|t| t.scaled(rhs.mult)));
	}
}

impl AddAssign<Coeff> for LinExp {
	fn add_assign(&mut self, rhs: Coeff) {
		self.add += rhs;
	}
}

impl Default for LinExp {
	fn default() -> Self {
		Self {
			terms: Default::default(),
			add: 0,
			mult: 1,
		}
	}
}

impl Display for LinExp {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{}",
			self.terms
				.iter()
				.map(|t| match t {
					LinTerm::Bool(l, c) => (format!("{l}"), c * self.mult),
					LinTerm::Int(x, c) => (format!("{x}"), c * self.mult),
				})
				.format_with(" + ", |(name, c), f| match c {
					1 => f(&format_args!("{name}")),
					-1 => f(&format_args!("-{name}")),
					_ => f(&format_args!("{c}*{name}")),
				})
		)?;
		if self.add != 0 {
			if !self.terms.is_empty() {
				write!(f, " + ")?;
			}
			write!(f, "{}", self.add)?;
		}
		Ok(())
	}
}

impl From<Coeff> for LinExp {
	fn from(value: Coeff) -> Self {
		Self {
			add: value,
			..Default::default()
		}
	}
}

impl From<IntVar> for LinExp {
	fn from(x: IntVar) -> Self {
		Self {
			terms: vec![LinTerm::Int(x, 1)],
			..Default::default()
		}
	}
}

impl Mul<Coeff> for IntVar {
	type Output = LinExp;

	fn mul(self, rhs: Coeff) -> Self::Output {
		LinExp {
			terms: vec![LinTerm::Int(self, rhs)],
			..Default::default()
		}
	}
}

impl Add<IntVar> for LinExp {
	type Output = LinExp;

	fn add(self, rhs: IntVar) -> Self::Output {
		self + LinExp::from(rhs)
	}
}

impl From<Lit> for LinExp {
	fn from(lit: Lit) -> Self {
		Self {
			terms: vec![LinTerm::Bool(lit, 1)],
			..Default::default()
		}
	}
}

impl From<bool> for LinExp {
	fn from(b: bool) -> Self {
		Self {
			add: b.into(),
			..Default::default()
		}
	}
}

impl Mul<Coeff> for LinExp {
	type Output = LinExp;

	fn mul(mut self, rhs: Coeff) -> Self::Output {
		self *= rhs;
		self
	}
}

impl MulAssign<Coeff> for LinExp {
	fn mul_assign(&mut self, rhs: Coeff) {
		self.mult *= rhs;
	}
}

impl Neg for LinExp {
	type Output = Self;

	fn neg(mut self) -> Self::Output {
		self.mult = -self.mult;
		self
	}
}

impl Sub for LinExp {
	type Output = Self;

	fn sub(self, rhs: Self) -> Self::Output {
		let mut res = self.clone();
		res -= rhs;
		res
	}
}

impl SubAssign for LinExp {
	fn sub_assign(&mut self, rhs: Self) {
		self.add_assign(-rhs);
	}
}

impl Linear {
	/// Create a new Boolean linear constraint from a left hand side Boolean
	/// linear expression, a comparator, and a right hand side coefficient.
	pub fn new(exp: LinExp, cmp: Comparator, k: Coeff) -> Self {
		Self { exp, cmp, k }
	}

	/// Change the comparator of the Boolean linear constraint.
	pub fn set_cmp(&mut self, cmp: Comparator) {
		self.cmp = cmp;
	}

	#[cfg(any(feature = "tracing", test))]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(
			self.exp.terms.iter().map(|t| match t {
				LinTerm::Bool(l, c) => format!("{c:?}·{}", trace_print_lit(l)),
				LinTerm::Int(x, c) => format!("{c:?}·{}", x.label()),
			}),
			" + ",
		);
		let op = match self.cmp {
			Comparator::LessEq => "≤",
			Comparator::Equal => "=",
			Comparator::GreaterEq => "≥",
		};
		format!("{x} {op} {:?}", self.k)
	}
}

impl Checker for Linear {
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result<()> {
		let lhs = self.exp.value(value)?;
		if match self.cmp {
			Comparator::LessEq => lhs <= self.k,
			Comparator::Equal => lhs == self.k,
			Comparator::GreaterEq => lhs >= self.k,
		} {
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}
}

impl Display for Linear {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{} {} {}",
			self.exp,
			match self.cmp {
				Comparator::Equal => "==",
				Comparator::LessEq => "<=",
				Comparator::GreaterEq => ">=",
			},
			self.k
		)
	}
}

impl From<PosCoeff> for Coeff {
	fn from(val: PosCoeff) -> Self {
		val.0
	}
}

impl From<LimitComp> for Comparator {
	fn from(value: LimitComp) -> Self {
		match value {
			LimitComp::Equal => Comparator::Equal,
			LimitComp::LessEq => Comparator::LessEq,
		}
	}
}

impl Display for LimitComp {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			LimitComp::Equal => write!(f, "=="),
			LimitComp::LessEq => write!(f, "<="),
		}
	}
}

impl PosCoeff {
	pub(crate) fn new(c: Coeff) -> Self {
		if c < 0 {
			panic!("cannot create a PosCoeff with a negative value")
		}
		Self(c)
	}
}

impl Deref for PosCoeff {
	type Target = Coeff;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl DerefMut for PosCoeff {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl Display for PosCoeff {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.0)
	}
}
#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::helpers::tests::{linear_test_suite, prelude::*};

	#[test]
	fn encoders() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		// TODO encode this if encoder does not support constraint
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![c, d],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();
		// +7*x1 +10*x2 +4*x3 +4*x4 <= 9
		LinearEncoder::<StaticLinEncoder<AdderEncoder>>::default()
			.encode(
				&mut cnf,
				&Linear::new(
					LinExp::from_slices(&[7, 10, 4, 4], &[a, b, c, d]),
					Comparator::LessEq,
					9,
				),
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vec![a, b, c, d],
			&expect_file!["linear/adder/test_encoders.sol"],
		);
	}

	#[test]
	fn what_the_decompositions_cost() {
		// Clause counts for each way of decomposing a pseudo-Boolean
		// constraint. The `.sol` goldens these encoders already have are blind
		// to size, so this is the only thing standing between a decomposition
		// getting quietly worse and nobody noticing.
		let cases: [(&str, &[Coeff], Coeff); 5] = [
			("card-10", &[1; 10], 5),
			("pb-small", &[1, 2, 3, 4, 5], 8),
			("pb-mid", &[2, 3, 5, 7, 11, 13], 20),
			("pb-wide", &[1, 2, 4, 8, 16, 32, 64], 70),
			("pb-coprime", &[3, 5, 7, 11, 13, 17], 40),
		];
		let mut table = format!(
			"{:>11} {:>4} {:>6} {:>7} {:>8} {:>9}\n",
			"case", "cmp", "enc", "vars", "clauses", "literals"
		);
		for (name, coeffs, k) in cases {
			for cmp in [Comparator::LessEq, Comparator::Equal] {
				for enc in ["adder", "bdd", "swc", "gt"] {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(coeffs.len()).iter_lits().collect_vec();
					let con = Linear::new(LinExp::from_slices(coeffs, &vars), cmp.clone(), k);
					let done = match enc {
						"adder" => LinearEncoder::<StaticLinEncoder<AdderEncoder>>::default()
							.encode(&mut cnf, &con),
						"bdd" => LinearEncoder::<StaticLinEncoder<BddEncoder>>::default()
							.encode(&mut cnf, &con),
						"swc" => LinearEncoder::<StaticLinEncoder<SwcEncoder>>::default()
							.encode(&mut cnf, &con),
						_ => LinearEncoder::<StaticLinEncoder<TotalizerEncoder>>::default()
							.encode(&mut cnf, &con),
					};
					let cmp = if cmp == Comparator::LessEq {
						"<="
					} else {
						"=="
					};
					table += &match done {
						Err(Unsatisfiable) => {
							format!("{name:>11} {cmp:>4} {enc:>6} {:>27}\n", "unsatisfiable")
						}
						Ok(()) => format!(
							"{name:>11} {cmp:>4} {enc:>6} {:>7} {:>8} {:>9}\n",
							cnf.num_vars(),
							cnf.num_clauses(),
							cnf.literals()
						),
					};
				}
			}
		}
		expect_file!("linear/decompositions.size").assert_eq(&table);
	}

	#[test]
	fn pb_encode() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(4).iter_lits().collect_vec();
		LinearEncoder::<StaticLinEncoder>::default()
			.encode(
				&mut cnf,
				&Linear::new(
					LinExp::from_slices(&[1, 1, 1, 2], &vars),
					Comparator::LessEq,
					1,
				),
			)
			.unwrap();

		assert_encoding(&cnf, &expect_file!["linear/adder/test_pb_encode.cnf"]);
		assert_solutions(&cnf, vars, &expect_file!["linear/adder/test_pb_encode.sol"]);
	}

	#[test]
	fn sort_same_coefficients_2() {
		let mut db = Cnf::default();
		let vars = db.new_var_range(5).iter_lits().collect_vec();
		let mut agg = BoolLinAggregator::default();
		let _ = agg.sort_same_coefficients(SortedEncoder::default(), 3);
		let mut encoder = LinearEncoder::<StaticLinEncoder<TotalizerEncoder>>::default();
		let _ = encoder.with_linear_aggregator(agg);
		let con = Linear::new(
			LinExp::from_slices(&[3, 3, 1, 1, 3], &vars),
			Comparator::GreaterEq,
			2,
		);
		encoder.encode(&mut db, &con).unwrap();
		assert_checker(&db, &con);
	}

	linear_test_suite! {int_lin_encoder, crate::int_linear::IntLinEncoder::default()}
}
