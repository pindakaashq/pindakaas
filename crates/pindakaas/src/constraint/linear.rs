//! Writing a linear constraint, and what one turns out to be once aggregated.
//!
//! A term is either a literal, worth its coefficient when it holds, or an
//! integer variable, worth its coefficient times whichever value it takes — so
//! a [`Linear`] covers the pseudo-Boolean and the integer case alike. Passing
//! one through [`LinAggregator`] normalises it and reports which
//! [`LinVariant`] it actually is, so that a narrower constraint reaches an
//! encoder that specialises in it.

use std::{
	fmt::{self, Display},
	ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign, Neg, Sub, SubAssign},
};

use itertools::Itertools;

pub use crate::encoder::{
	adder::AdderEncoder,
	aggregate::{LinAggregator, LinearEncoder, StaticLinEncoder},
	decision_diagram::DecisionDiagramEncoder,
	mixed_radix::MixedRadixEncoder,
	watchdog::WatchdogEncoder,
	sequential_counter::SequentialCounterEncoder,
	totalizer::TotalizerEncoder,
};
use crate::{
	constraint::{
		bool_linear::NormalizedBoolLinear, cardinality::Cardinality,
		cardinality_one::CardinalityOne, count::Count, int_linear::NormalizedIntLinear,
	},
	decision::integer::IntVar,
	Checker, Coeff, Lit, Result, Unsatisfiable, Valuation,
};

#[derive(Clone, Debug)]
/// A sum of terms, each a literal or an integer variable scaled by a
/// coefficient.
pub struct LinExp {
	/// Terms in insertion order; aggregation performs canonicalisation later.
	pub(crate) terms: Vec<LinTerm>,
	/// Constant applied before the outer multiplier.
	pub(crate) add: Coeff,
	/// Multiplier shared by every term and the additive constant.
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
/// A linear constraint: a [`LinExp`] compared against a constant.
///
/// Where every term is a literal this is what the literature calls a
/// pseudo-Boolean constraint; the terms may equally be integer variables.
pub struct Linear {
	/// Left-hand expression.
	pub(crate) exp: LinExp,
	/// Relation between `exp` and `k`.
	pub(crate) cmp: Comparator,
	/// Right-hand constant.
	pub(crate) k: Coeff,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
/// Relation between the left- and right-hand sides of a constraint.
pub enum Comparator {
	/// `exp ≤ k`.
	LessEq,
	/// `exp = k`.
	Equal,
	/// `exp ≥ k`.
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
/// A comparator limited to `=` or `≤`.
///
/// A `≥` is the same constraint read the other way round, so a normalised
/// constraint never carries one and an encoder never has to handle it.
pub enum LimitComp {
	/// The sum is exactly the constant.
	Equal,
	/// The sum is at most the constant.
	LessEq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// A coefficient guaranteed to be zero or greater.
///
/// The type is a bound as often as it is a coefficient, and a bound of zero
/// is a real constraint, so zero stays inside it.
pub struct PosCoeff(pub(crate) Coeff);

impl LinExp {
	/// The expression with `k` added before any outer scaling.
	pub fn add_constant(mut self, k: Coeff) -> Self {
		self.add += k;
		self
	}

	/// The expression with an unweighted literal appended.
	pub fn add_lit(mut self, lit: Lit) -> Self {
		self.terms.push(LinTerm::Bool(lit, 1));
		self
	}

	/// A pseudo-Boolean sum from parallel coefficient and literal slices.
	///
	/// # Panics
	///
	/// The slices have different lengths.
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

	/// A pseudo-Boolean sum from `(literal, coefficient)` pairs.
	pub fn from_terms(terms: &[(Lit, Coeff)]) -> Self {
		Self {
			terms: terms.iter().map(|&(l, c)| LinTerm::Bool(l, c)).collect(),
			..Default::default()
		}
	}

	/// Boolean terms only, excluding the additive constant and outer multiplier.
	pub fn terms(&self) -> impl Iterator<Item = (Lit, Coeff)> + '_ {
		self.terms.iter().filter_map(|t| match t {
			LinTerm::Bool(l, c) => Some((*l, *c)),
			LinTerm::Int(..) => None,
		})
	}

	/// Integer terms only, excluding the additive constant and outer multiplier.
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
			write!(f, "{}", self.add * self.mult)?;
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
	/// The constraint `exp ≷ k`, without normalisation or aggregation.
	///
	/// # Examples
	///
	/// ```rust
	/// use pindakaas::{
	///     constraint::linear::{Comparator, Linear}, ClauseDatabaseTools, Cnf,
	/// };
	///
	/// let mut cnf = Cnf::default();
	/// let (x, y) = cnf.new_lits();
	/// let constraint = Linear::new(2 * x + 3 * y, Comparator::LessEq, 3);
	/// # let _ = constraint;
	/// # Ok::<(), pindakaas::Unsatisfiable>(())
	/// ```
	pub fn new(exp: LinExp, cmp: Comparator, k: Coeff) -> Self {
		Self { exp, cmp, k }
	}

	/// Change the comparator of the constraint.
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
	/// Wrap a coefficient that is not negative.
	///
	/// # Panics
	///
	/// If `c` is negative.
	pub fn new(c: Coeff) -> Self {
		assert!(c >= 0, "a PosCoeff cannot be negative, and {c} is");
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

	use crate::helpers::tests::prelude::*;

	#[test]
	fn encoders() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
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
			"{:>11} {:>4} {:>7} {:>7} {:>8} {:>9}\n",
			"case", "cmp", "enc", "vars", "clauses", "literals"
		);
		for (name, coeffs, k) in cases {
			for cmp in [Comparator::LessEq, Comparator::Equal] {
				for enc in ["adder", "diagram", "seq", "tree", "radix", "wdog", "wdog-l"] {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(coeffs.len()).iter_lits().collect_vec();
					let con = Linear::new(LinExp::from_slices(coeffs, &vars), cmp.clone(), k);
					// Every slot the cases reach — integer linear, Boolean
					// linear and cardinality — so that a row measures the
					// encoder it names rather than whichever is the default.
					let done = match enc {
						"adder" => LinearEncoder::<
							StaticLinEncoder<AdderEncoder, AdderEncoder, AdderEncoder>,
						>::default()
						.encode(&mut cnf, &con),
						"diagram" => LinearEncoder::<
							StaticLinEncoder<DecisionDiagramEncoder, DecisionDiagramEncoder, DecisionDiagramEncoder>,
						>::default()
						.encode(&mut cnf, &con),
						"seq" => LinearEncoder::<
							StaticLinEncoder<SequentialCounterEncoder, SequentialCounterEncoder, SequentialCounterEncoder>,
						>::default()
						.encode(&mut cnf, &con),
						"tree" => LinearEncoder::<
							StaticLinEncoder<TotalizerEncoder, TotalizerEncoder, TotalizerEncoder>,
						>::default()
						.encode(&mut cnf, &con),
						"wdog" => LinearEncoder::<
							StaticLinEncoder<
								WatchdogEncoder,
								WatchdogEncoder,
								WatchdogEncoder,
							>,
						>::default()
						.encode(&mut cnf, &con),
						"wdog-l" => {
							// The local form is the same encoder, so it is
							// configured rather than named separately.
							let mut enc = StaticLinEncoder::<
								WatchdogEncoder,
								WatchdogEncoder,
								WatchdogEncoder,
							>::default();
							let _ = enc.lin_encoder().with_local(true);
							let _ = enc.bool_lin_encoder().with_local(true);
							let _ = enc.card_encoder().with_local(true);
							LinearEncoder::new(enc, LinAggregator::default())
								.encode(&mut cnf, &con)
						}
						_ => LinearEncoder::<
							StaticLinEncoder<
								MixedRadixEncoder,
								MixedRadixEncoder,
								MixedRadixEncoder,
							>,
						>::default()
						.encode(&mut cnf, &con),
					};
					let cmp = if cmp == Comparator::LessEq {
						"<="
					} else {
						"=="
					};
					table += &match done {
						Err(Unsatisfiable) => {
							format!("{name:>11} {cmp:>4} {enc:>7} {:>27}\n", "unsatisfiable")
						}
						Ok(()) => format!(
							"{name:>11} {cmp:>4} {enc:>7} {:>7} {:>8} {:>9}\n",
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
		let mut agg = LinAggregator::default();
		let _ = agg.sort_same_coefficients(SortingNetworkEncoder::default(), 3);
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
}

#[derive(Debug)]
/// What a linear constraint turned out to be once aggregated.
///
/// Aggregation works out which terms belong together and what relates them,
/// and hands the general case on as a constraint over the integers those
/// groups encode. What it recognises as counting rather than weighing keeps a
/// form of its own, there being encoders that do only that.
pub enum LinVariant {
	/// A sum of weighted literals against a constant, mentioning no integer
	/// variable, which the encoders that work in literals take directly.
	BoolLinear(NormalizedBoolLinear),
	/// Literals counted into an integer, which a sorting network states
	/// outright rather than counting into intermediates first.
	Count(Count),
	/// Most general form: a sum of integer terms that must be
	/// (smaller-or-)equal to a constant. The groups the aggregator recognised
	/// have each become an integer, encoded on the literals they were found on.
	Linear(NormalizedIntLinear),
	/// Cardinality constraint (also known as a counting constraint): a sum of
	/// Boolean literals that must be (smaller-or-)equal to a positive constant.
	Cardinality(Cardinality),
	/// Cardinality constraint with the constant 1 (i.e. at-least or exactly 1
	/// literal must be true).
	CardinalityOne(CardinalityOne),
	/// Constraint was trivially encoded into clauses.
	Trivial,
}
