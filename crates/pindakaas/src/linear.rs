use std::{
	collections::VecDeque,
	fmt::{self, Display},
	ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign},
};

use itertools::Itertools;

use crate::{
	Cardinality, CardinalityOne, CheckError, Checker, ClauseDatabase, Coeff, Encoder, IntEncoding,
	IntVar, Lit, PairwiseEncoder, Result, Unsatisfiable, Valuation,
};

mod adder;
mod aggregator;
mod bdd;
mod swc;
pub(crate) mod totalizer;

pub use adder::AdderEncoder;
pub(crate) use adder::{lex_geq_const, lex_leq_const, log_enc_add_fn};
pub use aggregator::LinearAggregator;
pub use bdd::BddEncoder;
use itertools::Itertools;
pub use swc::SwcEncoder;
pub use totalizer::TotalizerEncoder;

/// PosCoeff is a type for coefficients that are guaranteed by the programmer to
/// be 0 or greater.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct PosCoeff(Coeff);

impl PosCoeff {
	pub fn new(c: Coeff) -> Self {
		if c < 0 {
			panic!("cannot create a PosCoeff with a negative value")
		}
		Self(c)
	}
}

impl From<PosCoeff> for Coeff {
	fn from(val: PosCoeff) -> Self {
		val.0
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

#[derive(Debug)]
pub enum LinVariant {
	Linear(Linear),
	Cardinality(Cardinality),
	CardinalityOne(CardinalityOne),
	Trivial,
}

#[derive(Debug, Clone)]
pub struct Linear {
	pub(crate) terms: Vec<Part>,
	pub cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

impl Linear {
	#[cfg(feature = "trace")]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(
			self.terms
				.iter()
				.flat_map(|part| part.iter().map(|(lit, coef)| (lit, coef)))
				.map(|(l, c)| format!("{c:?}·{}", trace_print_lit(l))),
			" + ",
		);
		let op = if self.cmp == LimitComp::LessEq {
			"≤"
		} else {
			"="
		};
		format!("{x} {op} {:?}", *self.k)
	}

	pub fn set_k(&mut self, k: Coeff) {
		self.k = PosCoeff::new(k);
	}

	pub fn len(&self) -> usize {
		self.terms.len()
	}

	pub fn is_empty(&self) -> bool {
		self.terms.is_empty()
	}
}

impl From<Cardinality> for Linear {
	fn from(card: Cardinality) -> Self {
		Self {
			terms: card
				.lits
				.into_iter()
				.map(|l| Part::Amo(vec![(l, PosCoeff::new(1))]))
				.collect(),
			cmp: card.cmp,
			k: card.k,
		}
	}
}
impl From<CardinalityOne> for Linear {
	fn from(amo: CardinalityOne) -> Self {
		Self::from(Cardinality::from(amo))
	}
}

// Automatically implement Cardinality encoding when you can encode Linear constraints
impl<DB: ClauseDatabase, Enc: Encoder<DB, Linear> + LinMarker> Encoder<DB, Cardinality> for Enc {
	fn encode(&self, db: &mut DB, con: &Cardinality) -> crate::Result {
		self.encode(db, &Linear::from(con.clone()))
	}
}
// local marker trait, to ensure the previous definition only applies within this crate
pub(crate) trait LinMarker {}
impl LinMarker for AdderEncoder {}
impl LinMarker for TotalizerEncoder {}
impl LinMarker for SwcEncoder {}
impl LinMarker for BddEncoder {}

// TODO how can we support both Part(itions) of "terms" ( <Lit, C> for pb
// constraints) and just lits (<Lit>) for AMK/AMO's?
//
// TODO add EO, and probably something for Unconstrained
// TODO this can probably follow the same structure as LinExp
#[derive(Debug, Clone)]
pub(crate) enum Part {
	Amo(Vec<(Lit, PosCoeff)>),
	Ic(Vec<(Lit, PosCoeff)>),
	Dom(Vec<(Lit, PosCoeff)>, PosCoeff, PosCoeff),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum LimitComp {
	Equal,
	LessEq,
}

impl fmt::Display for LimitComp {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			LimitComp::Equal => write!(f, "="),
			LimitComp::LessEq => write!(f, "≤"),
		}
	}
}

#[derive(Clone, Debug)]
pub struct LinExp {
	/// All terms of the pseudo-Boolean linear expression
	terms: VecDeque<(Lit, Coeff)>,
	/// Number of unconstrained terms (located at the front of `terms`)
	num_free: usize,
	/// Constraints placed on different terms, and the number of terms involved in the constraint
	constraints: Vec<(Constraint, usize)>,
	/// Additive constant
	pub add: Coeff,
	/// Multiplicative contant
	pub mult: Coeff,
}

/*
impl LinExp {
	pub(crate) fn value<F: Valuation + ?Sized>(&self, sol: &F) -> Result<Coeff, CheckError> {
		let mut total = self.add;
		for (constraint, terms) in self.iter() {
			// Calculate sum for constraint
			let sum = terms
				.iter()
				.filter(|(lit, _)| sol.value(*lit).expect("missing assignment to literal"))
				.map(|(_, i)| i)
				.sum();
			match constraint {
				Some(Constraint::AtMostOne) => {
					if sum != 0
						&& terms
							.iter()
							.filter(|&(l, _)| sol.value(*l).unwrap_or(true))
							.count() > 1
					{
						return Err(Unsatisfiable.into());
					}
				}
				Some(Constraint::ImplicationChain) => {
					if terms
						.iter()
						.map(|(l, _)| *l)
						.tuple_windows()
						.any(|(a, b)| !sol.value(a).unwrap_or(false) & sol.value(b).unwrap_or(true))
					{
						return Err(Unsatisfiable.into());
					}
				}
				Some(Constraint::Domain { lb, ub }) => {
					// divide by first coeff to get int assignment
					if sum > ub - lb {
						return Err(Unsatisfiable.into());
					}
				}
				None => {}
			};
			total += sum;
		}
		Ok(total * self.mult)
	}
}
*/

impl Default for LinExp {
	fn default() -> Self {
		Self {
			terms: Default::default(),
			num_free: 0,
			constraints: Default::default(),
			add: 0,
			mult: 1,
		}
	}
}

#[derive(Debug, Clone)]
pub struct LinearConstraint {
	/// Expression being constrained
	pub exp: LinExp,
	/// Comparator when exp is on the left hand side and k is on the right hand side
	pub cmp: Comparator,
	/// Coefficient providing the upper bound or lower bound to exp, or both
	pub k: Coeff,
}

impl From<LimitComp> for Comparator {
	fn from(value: LimitComp) -> Self {
		match value {
			LimitComp::Equal => Comparator::Equal,
			LimitComp::LessEq => Comparator::LessEq,
		}
	}
}

impl TryFrom<Comparator> for LimitComp {
	fn try_from(value: Comparator) -> Result<Self, ()> {
		match value {
			Comparator::Equal => Ok(LimitComp::Equal),
			Comparator::LessEq => Ok(LimitComp::LessEq),
			_ => Err(()),
		}
	}

	type Error = ();
}

impl From<Linear> for LinearConstraint {
	fn from(lin: Linear) -> Self {
		LinearConstraint {
			exp: LinExp::from_terms(
				lin.terms
					.iter()
					.flat_map(|part| part.into_iter().map(|&(l, c)| (l, *c)))
					.collect_vec()
					.as_slice(),
			),
			cmp: lin.cmp.into(),
			k: *lin.k,
		}
	}
}

impl LinearConstraint {
	pub fn new(exp: LinExp, cmp: Comparator, k: Coeff) -> Self {
		Self { exp, cmp, k }
	}

	#[cfg(feature = "trace")]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(
			self.exp
				.terms
				.iter()
				.map(|(l, c)| format!("{c:?}·{}", trace_print_lit(l))),
			" + ",
		);
		let op = match self.cmp {
			Comparator::LessEq => "≤",
			Comparator::Equal => "=",
			Comparator::GreaterEq => "≥",
		};
		format!("{x} {op} {:?}", self.k)
	}

	pub fn set_cmp(&mut self, cmp: Comparator) {
		self.cmp = cmp;
	}
}

impl From<&IntVar> for LinExp {
	fn from(x: &IntVar) -> Self {
		x.as_lin_exp()
	}
}

impl Checker for LinearConstraint {
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result<(), CheckError> {
		let lhs = self
			.exp
			.value(value)
			.expect("TODO: handle unassigned value");
		if match self.cmp {
			Comparator::LessEq => lhs <= self.k,
			Comparator::Equal => lhs == self.k,
			Comparator::GreaterEq => lhs >= self.k,
		} {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Comparator {
	LessEq,
	Equal,
	GreaterEq,
}

impl Comparator {
	pub(crate) fn split(&self) -> Vec<Comparator> {
		match self {
			Comparator::Equal => vec![Comparator::LessEq, Comparator::GreaterEq],
			_ => vec![*self],
		}
	}

	pub(crate) fn reverse(&self) -> Comparator {
		match *self {
			Comparator::LessEq => Comparator::GreaterEq,
			Comparator::Equal => panic!("Cannot reverse {self}"),
			Comparator::GreaterEq => Comparator::LessEq,
		}
	}

	pub(crate) fn is_ineq(&self) -> bool {
		match *self {
			Comparator::Equal => false,
			Comparator::LessEq | Comparator::GreaterEq => true,
		}
	}
}

impl fmt::Display for Comparator {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Comparator::Equal => write!(f, "="),
			Comparator::LessEq => write!(f, "≤"),
			Comparator::GreaterEq => write!(f, "≥"),
		}
	}
}

#[derive(Debug, Clone)]
pub(crate) enum Constraint {
	AtMostOne,
	ImplicationChain,
	Domain { lb: Coeff, ub: Coeff },
}

impl Part {
	pub fn iter(&self) -> impl Iterator<Item = &(Lit, PosCoeff)> {
		self.into_iter()
	}
}
impl<'a> IntoIterator for &'a Part {
	type Item = &'a (Lit, PosCoeff);
	type IntoIter = std::slice::Iter<'a, (Lit, PosCoeff)>;

	fn into_iter(self) -> Self::IntoIter {
		match self {
			Part::Amo(terms) => terms.iter(),
			Part::Ic(terms) => terms.iter(),
			Part::Dom(terms, _lb, _ub) => terms.iter(),
		}
	}
}

impl LinExp {
	pub fn from_slices(weights: &[Coeff], lits: &[Lit]) -> Self {
		assert_eq!(
			weights.len(),
			lits.len(),
			"the number of weights and literals must be equal"
		);
		Self {
			terms: lits.iter().cloned().zip(weights.iter().cloned()).collect(),
			num_free: lits.len(),
			..Default::default()
		}
	}

	pub fn from_terms(terms: &[(Lit, Coeff)]) -> Self {
		Self {
			terms: terms.iter().cloned().collect(),
			num_free: terms.len(),
			..Default::default()
		}
	}

	/// Add multiple terms to the linear expression of which at most one
	/// can be chosen
	pub fn add_choice(mut self, choice: &[(Lit, Coeff)]) -> Self {
		if let [term] = choice {
			self += *term;
		} else {
			self.terms.extend(choice.iter().cloned());
			self.constraints.push((Constraint::AtMostOne, choice.len()))
		}
		self
	}

	/// Add multiple terms to the linear expression where the literal
	/// in each term is implied by the literal in the consecutive term
	pub fn add_chain(mut self, chain: &[(Lit, Coeff)]) -> Self {
		if let [term] = chain {
			self += *term;
		} else {
			self.terms.extend(chain.iter().cloned());
			self.constraints
				.push((Constraint::ImplicationChain, chain.len()))
		}
		self
	}

	pub fn add_constant(mut self, k: Coeff) -> Self {
		self.add += k;
		self
	}

	pub fn add_lit(mut self, lit: Lit) -> Self {
		self += (lit, 1);
		self
	}

	// TODO I'm not really happy with this interface yet...
	// Probably makes more sense to use something like int encodings
	pub fn add_bounded_log_encoding(
		mut self,
		terms: &[(Lit, Coeff)],
		lb: Coeff,
		ub: Coeff,
	) -> Self {
		self.constraints
			.push((Constraint::Domain { lb, ub }, terms.len()));
		self.terms.extend(terms.iter().cloned());
		self
	}

	pub(crate) fn iter(&self) -> impl Iterator<Item = (Option<Constraint>, Vec<&(Lit, Coeff)>)> {
		let mut it = self.terms.iter();
		std::iter::once((
			None,
			Vec::from_iter((0..self.num_free).map(|_| it.next().unwrap())),
		))
		.chain(self.constraints.iter().map(move |constraint| {
			let mut terms = Vec::with_capacity(constraint.1);
			for _ in 0..constraint.1 {
				if let Some(term) = it.next() {
					terms.push(term)
				}
			}
			(Some(constraint.0.clone()), terms)
		}))
	}

	pub fn terms(&self) -> impl Iterator<Item = (Lit, Coeff)> + '_ {
		self.terms.iter().copied()
	}

	pub(crate) fn value<F: Valuation + ?Sized>(&self, sol: &F) -> Option<Coeff> {
		// TODO [?] look up how to return none if any none
		self.terms()
			.map(|(l, c)| sol.value(l).map(|l| c * l as Coeff))
			.sum()
	}
}

impl From<Lit> for LinExp {
	fn from(lit: Lit) -> Self {
		Self {
			terms: VecDeque::from([(lit, 1)]),
			num_free: 1,
			..Default::default()
		}
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
impl<'a> From<IntEncoding<'a>> for LinExp {
	fn from(var: IntEncoding<'a>) -> Self {
		match var {
			IntEncoding::Direct { first, vals } => {
				let mut terms = VecDeque::with_capacity(vals.len());
				let mut k = first;
				for lit in vals {
					terms.push_back((*lit, k));
					k += 1;
				}
				Self {
					terms,
					constraints: vec![(Constraint::AtMostOne, vals.len())],
					..Default::default()
				}
			}
			IntEncoding::Order { first, vals } => Self {
				terms: vals.iter().map(|lit| (*lit, 1)).collect(),
				constraints: vec![(Constraint::ImplicationChain, vals.len())],
				add: first,
				..Default::default()
			},
			IntEncoding::Log { signed, bits } => {
				let mut terms = VecDeque::with_capacity(bits.len());
				let two = 1 + 1;
				let mut k = 1;
				for lit in bits {
					terms.push_back((*lit, k));
					k *= two;
				}
				if signed {
					terms.back_mut().unwrap().1 *= -1;
				}
				Self {
					terms,
					num_free: bits.len(),
					..Default::default()
				}
			}
		}
	}
}

impl AddAssign<(Lit, Coeff)> for LinExp {
	fn add_assign(&mut self, rhs: (Lit, Coeff)) {
		self.terms.push_front(rhs);
		self.num_free += 1
	}
}
impl Add<(Lit, Coeff)> for LinExp {
	type Output = LinExp;
	fn add(mut self, rhs: (Lit, Coeff)) -> Self::Output {
		self += rhs;
		self
	}
}
impl<'a> AddAssign<IntEncoding<'a>> for LinExp {
	fn add_assign(&mut self, rhs: IntEncoding<'a>) {
		match rhs {
			IntEncoding::Direct { first, vals } => {
				let mut k = first;
				for lit in vals {
					self.terms.push_back((*lit, k));
					k += 1;
				}
				self.constraints.push((Constraint::AtMostOne, vals.len()))
			}
			IntEncoding::Order { first, vals } => {
				for lit in vals {
					self.terms.push_back((*lit, 1))
				}
				self.add += first;
				self.constraints
					.push((Constraint::ImplicationChain, vals.len()))
			}
			IntEncoding::Log { signed, bits } => {
				let two = 1 + 1;
				let mut k = 1;
				for lit in bits {
					self.terms.push_front((*lit, k));
					k *= two;
				}
				// TODO!
				if signed {
					self.terms.front_mut().unwrap().1 *= -1;
				}
				self.num_free += bits.len();
			}
		}
	}
}

impl<'a> Add<IntEncoding<'a>> for LinExp {
	type Output = LinExp;
	fn add(mut self, rhs: IntEncoding<'a>) -> Self::Output {
		self += rhs;
		self
	}
}
impl AddAssign<LinExp> for LinExp {
	fn add_assign(&mut self, rhs: LinExp) {
		// Multiply the current expression
		if self.mult != 1 {
			self.add *= self.mult;
			for term in &mut self.terms {
				term.1 *= self.mult;
			}
		}
		self.mult = 1;
		// Add other LinExp
		self.add += rhs.add * rhs.mult;
		let mut rh_terms = rhs.terms;
		self.terms.extend(
			rh_terms
				.drain(rhs.num_free..)
				.map(|(l, c)| (l, c * rhs.mult)),
		);
		debug_assert!(rh_terms.len() == rhs.num_free);
		self.terms
			.extend(rh_terms.into_iter().map(|(l, c)| (l, c * rhs.mult)));
		self.terms.rotate_right(rhs.num_free);
		self.num_free += rhs.num_free;
		self.constraints.extend(rhs.constraints);
	}
}
impl Add<LinExp> for LinExp {
	type Output = LinExp;
	fn add(mut self, rhs: LinExp) -> Self::Output {
		self += rhs;
		self
	}
}

impl MulAssign<Coeff> for LinExp {
	fn mul_assign(&mut self, rhs: Coeff) {
		self.mult *= rhs;
	}
}
impl Mul<Coeff> for LinExp {
	type Output = LinExp;
	fn mul(mut self, rhs: Coeff) -> Self::Output {
		self *= rhs;
		self
	}
}

impl Checker for Linear {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<(), CheckError> {
		let mut sum = 0;
		for (lit, coef) in self.terms.iter().flat_map(|p| p.iter().copied()) {
			match sol.value(lit) {
				Some(true) => sum += *coef,
				None if self.cmp == LimitComp::LessEq => sum += *coef,
				Some(false) => {}
				None => return Err(Unsatisfiable.into()),
			}
		}
		if match self.cmp {
			LimitComp::LessEq => sum <= *self.k,
			LimitComp::Equal => sum == *self.k,
		} {
			Ok(())
		} else {
			Err(Unsatisfiable.into())
		}
	}
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LinearEncoder<Enc = StaticLinEncoder, Agg = LinearAggregator> {
	pub enc: Enc,
	pub agg: Agg,
}

impl<Enc, Agg> LinearEncoder<Enc, Agg> {
	pub fn new(enc: Enc, agg: Agg) -> Self {
		Self { enc, agg }
	}
	pub fn add_variant_encoder(&mut self, enc: Enc) -> &mut Self {
		self.enc = enc;
		self
	}
	pub fn add_linear_aggregater(&mut self, agg: Agg) -> &mut Self {
		self.agg = agg;
		self
	}
}

impl<DB: ClauseDatabase, Enc: Encoder<DB, LinVariant>> Encoder<DB, LinearConstraint>
	for LinearEncoder<Enc>
{
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "linear_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut DB, lin: &LinearConstraint) -> Result {
		let variant = self.agg.aggregate(db, lin)?;
		self.enc.encode(db, &variant)
	}
}

// This is just a linear encoder that currently makes an arbitrary choice.
// This is probably not how we would like to do it in the future.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct StaticLinEncoder<
	LinEnc = AdderEncoder,
	CardEnc = AdderEncoder, // TODO: Actual Cardinality encoding
	AmoEnc = PairwiseEncoder,
> {
	lin_enc: LinEnc,
	card_enc: CardEnc,
	amo_enc: AmoEnc,
}

impl<LinEnc, CardEnc, AmoEnc> StaticLinEncoder<LinEnc, CardEnc, AmoEnc> {
	pub fn new(lin_enc: LinEnc, card_enc: CardEnc, amo_enc: AmoEnc) -> Self {
		Self {
			lin_enc,
			card_enc,
			amo_enc,
		}
	}
	pub fn lin_encoder(&mut self) -> &mut LinEnc {
		&mut self.lin_enc
	}
	pub fn card_encoder(&mut self) -> &mut CardEnc {
		&mut self.card_enc
	}
	pub fn amo_encoder(&mut self) -> &mut AmoEnc {
		&mut self.amo_enc
	}
}

impl<
		DB: ClauseDatabase,
		LinEnc: Encoder<DB, Linear>,
		CardEnc: Encoder<DB, Cardinality>,
		AmoEnc: Encoder<DB, CardinalityOne>,
	> Encoder<DB, LinVariant> for StaticLinEncoder<LinEnc, CardEnc, AmoEnc>
{
	fn encode(&self, db: &mut DB, lin: &LinVariant) -> Result {
		match &lin {
			LinVariant::Linear(lin) => self.lin_enc.encode(db, lin),
			LinVariant::Cardinality(card) => self.card_enc.encode(db, card),
			LinVariant::CardinalityOne(amo) => self.amo_enc.encode(db, amo),
			LinVariant::Trivial => Ok(()),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{Part, PosCoeff};
	use crate::{Coeff, Lit};

	pub(crate) fn construct_terms<L: Into<Lit> + Clone>(terms: &[(L, Coeff)]) -> Vec<Part> {
		terms
			.iter()
			.map(|(lit, coef)| Part::Amo(vec![(lit.clone().into(), PosCoeff::new(*coef))]))
			.collect()
	}

	macro_rules! linear_test_suite {
		($encoder:expr) => {
			#[test]
			fn test_small_le_1() {
				assert_sol!(
					$encoder,
					3,
					&Linear {
						terms: construct_terms(&[(1, 2), (2, 3), (3, 5),]),
						cmp: LimitComp::LessEq,
						k: PosCoeff::new(6)
					}
					=> vec![
						lits![-1, -2, -3], // 0
						lits![ 1, -2, -3], // 2
						lits![-1,  2, -3], // 3
						lits![ 1,  2, -3], // 5
						lits![-1, -2,  3], // 5
					]
				);
			}

			#[test]
			fn test_small_le_2() {
				assert_sol!(
					$encoder,
					6,
					&Linear {
						terms: construct_terms(&[
							(-1, 3),
							(-2, 6),
							(-3, 1),
							(-4, 2),
							(-5, 3),
							(-6, 6)
						]),
						cmp: LimitComp::LessEq,
						k: PosCoeff::new(19)
					}
				);
			}

			#[test]
			fn test_small_le_3() {
				assert_sol!(
					$encoder,
					3,
					&Linear {
						terms: construct_terms(&[(1, 1), (2, 2), (3, 4),]),
						cmp: LimitComp::LessEq,
						k: PosCoeff::new(5)
					}
					=> vec![
						lits![-1, -2, -3],
						lits![ 1, -2, -3],
						lits![-1,  2, -3],
						lits![ 1,  2, -3],
						lits![-1, -2,  3],
						lits![ 1, -2,  3],
					]
				);
			}

			#[test]
			fn test_small_le_4() {
				assert_sol!(
					$encoder,
					3,
					&Linear {
						terms: construct_terms(&[(1, 4), (2, 6), (3, 7),]),
						cmp: LimitComp::LessEq,
						k: PosCoeff::new(10)
					}
					=> vec![
						lits![-1, -2, -3],
						lits![1, -2, -3],
						lits![-1, 2, -3],
						lits![1, 2, -3],
						lits![-1, -2, 3],
					]

				);
			}



			#[test]
			fn test_small_eq_1() {
				assert_sol!(
					$encoder,
					3,
					&Linear {
						terms: construct_terms(&[(1, 1), (2, 2), (3, 4)]),
						cmp: LimitComp::Equal,
						k: PosCoeff::new(5)
					}
					=> vec![
						lits![ 1, -2,  3],
					]
				);
			}

			#[test]
			fn test_small_eq_2() {
				assert_sol!(
					$encoder,
					3,
					&Linear {
						terms: construct_terms(&[(1, 1), (2, 2), (3, 3),]),
						cmp: LimitComp::Equal,
						k: PosCoeff::new(3)
					}
					=> vec![
						lits![-1, -2,  3],
						lits![ 1,  2, -3],
					]
				);
			}

			#[test]
			fn test_small_eq_3() {
				assert_sol!(
					$encoder,
					4,
					&Linear {
						terms: construct_terms(&[(1, 2), (2, 3), (3, 5), (4,7)]),
						cmp: LimitComp::Equal,
						k: PosCoeff::new(10)
					}
					=> vec![
						lits![-1, 2,-3, 4],
						lits![ 1, 2, 3,-4],
					]
				);
			}

			#[test]
			fn test_small_eq_4() {
				assert_sol!(
					$encoder,
					4,
					&Linear {
						terms: construct_terms(&[(1, 2), (2, 1), (3, 2), (4,2)]),
						cmp: LimitComp::Equal,
						k: PosCoeff::new(4)
					}
					=> vec![
						lits![ 1,-2,-3, 4],
						lits![-1,-2, 3, 4],
						lits![ 1,-2, 3,-4],
					]
				);
			}
		};

    }
	pub(crate) use linear_test_suite;
}
