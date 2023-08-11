use itertools::Itertools;
use std::{
	collections::VecDeque,
	fmt,
	ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign},
};

use crate::{
	int::IntVarEnc, Cardinality, CardinalityOne, CheckError, Checker, ClauseDatabase, Coefficient,
	Encoder, IntEncoding, Literal, PairwiseEncoder, Result, Unsatisfiable,
};

mod adder;
mod aggregator;
mod bdd;
mod swc;
pub(crate) mod totalizer;

pub use adder::AdderEncoder;
pub(crate) use adder::{lex_geq_const, lex_leq_const, log_enc_add, log_enc_add_};
pub use aggregator::LinearAggregator;
pub use bdd::BddEncoder;
pub use swc::SwcEncoder;
pub use totalizer::TotalizerEncoder;

/// PosCoeff is a container used when coefficients that are guaranteed
/// by the programmer to be 0 or greater.
///
/// # Warning
/// The [`From`] implementation of this type will panic if the  
#[derive(Clone, Debug, PartialEq, PartialOrd, Ord, Eq)]
pub struct PosCoeff<C: Coefficient>(C);
impl<C: Coefficient> From<C> for PosCoeff<C> {
	fn from(c: C) -> Self {
		assert!(
			!c.is_negative(),
			"could not create PosCoeff, value was found to be negative"
		);
		Self(c)
	}
}
impl<C: Coefficient> Deref for PosCoeff<C> {
	type Target = C;
	fn deref(&self) -> &Self::Target {
		&self.0
	}
}
impl<C: Coefficient> DerefMut for PosCoeff<C> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}
#[derive(Debug)]
pub enum LinVariant<Lit: Literal, C: Coefficient> {
	Linear(Linear<Lit, C>),
	Cardinality(Cardinality<Lit, C>),
	CardinalityOne(CardinalityOne<Lit>),
	Trivial,
}

#[derive(Debug, Clone)]
pub struct Linear<Lit: Literal, C: Coefficient> {
	pub(crate) terms: Vec<Part<Lit, PosCoeff<C>>>,
	pub cmp: LimitComp,
	pub(crate) k: PosCoeff<C>,
}

impl<Lit: Literal, C: Coefficient> Linear<Lit, C> {
	#[cfg(feature = "trace")]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(
			self.terms
				.iter()
				.flat_map(|part| part.iter().map(|(lit, coef)| (lit, **coef)))
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

	pub fn set_k(&mut self, k: C) {
		self.k = k.into();
	}
}

impl<Lit: Literal, C: Coefficient> From<Cardinality<Lit, C>> for Linear<Lit, C> {
	fn from(card: Cardinality<Lit, C>) -> Self {
		Self {
			terms: card
				.lits
				.into_iter()
				.map(|l| Part::Amo(vec![(l, C::one().into())]))
				.collect(),
			cmp: card.cmp,
			k: card.k,
		}
	}
}
impl<Lit: Literal, C: Coefficient> From<CardinalityOne<Lit>> for Linear<Lit, C> {
	fn from(amo: CardinalityOne<Lit>) -> Self {
		Self::from(Cardinality::from(amo))
	}
}

// Automatically implement Cardinality encoding when you can encode Linear constraints
impl<DB: ClauseDatabase, C: Coefficient, Enc: Encoder<DB, Linear<DB::Lit, C>> + LinMarker>
	Encoder<DB, Cardinality<DB::Lit, C>> for Enc
{
	fn encode(&mut self, db: &mut DB, con: &Cardinality<DB::Lit, C>) -> crate::Result {
		self.encode(db, &Linear::<DB::Lit, C>::from(con.clone()))
	}
}
// local marker trait, to ensure the previous definition only applies within this crate
pub(crate) trait LinMarker {}
impl LinMarker for AdderEncoder {}
impl<C: Coefficient> LinMarker for TotalizerEncoder<C> {}
impl<C: Coefficient> LinMarker for SwcEncoder<C> {}
impl<C: Coefficient> LinMarker for BddEncoder<C> {}

// TODO how can we support both Part(itions) of "terms" ( <Lit, C> for pb
// constraints) and just lits (<Lit>) for AMK/AMO's?
//
// TODO add EO, and probably something for Unconstrained
// TODO this can probably follow the same structure as LinExp
#[derive(Debug, Clone)]
pub(crate) enum Part<Lit, C> {
	Amo(Vec<(Lit, C)>),
	Ic(Vec<(Lit, C)>),
	Dom(Vec<(Lit, C)>, C, C),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LimitComp {
	Equal,
	LessEq,
}

impl fmt::Display for LimitComp {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			LimitComp::Equal => write!(f, "=="),
			LimitComp::LessEq => write!(f, "<="),
		}
	}
}

#[derive(Clone, Debug)]
pub struct LinExp<Lit: Literal, C: Coefficient> {
	/// All terms of the pseudo-Boolean linear expression
	terms: VecDeque<(Lit, C)>,
	/// Number of unconstrained terms (located at the front of `terms`)
	num_free: usize,
	/// Constraints placed on different terms, and the number of terms involved in the constraint
	constraints: Vec<(Constraint<C>, usize)>,
	/// Additive constant
	pub add: C,
	/// Multiplicative contant
	pub mult: C,
}

#[derive(Debug, Clone)]
pub struct LinearConstraint<Lit: Literal, C: Coefficient> {
	/// Expression being constrained
	pub exp: LinExp<Lit, C>,
	/// Comparator when exp is on the left hand side and k is on the right hand side
	pub cmp: Comparator,
	/// Coefficient providing the upper bound or lower bound to exp, or both
	pub k: C,
}

impl From<LimitComp> for Comparator {
	fn from(value: LimitComp) -> Self {
		match value {
			LimitComp::Equal => Comparator::Equal,
			LimitComp::LessEq => Comparator::LessEq,
		}
	}
}

impl<Lit: Literal, C: Coefficient> From<Linear<Lit, C>> for LinearConstraint<Lit, C> {
	fn from(lin: Linear<Lit, C>) -> Self {
		LinearConstraint {
			exp: LinExp::from_terms(
				lin.terms
					.iter()
					.flat_map(|part| part.iter().map(|(l, c)| (l.clone(), *c.clone())))
					.collect::<Vec<_>>()
					.as_slice(),
			),
			cmp: lin.cmp.into(),
			k: *lin.k,
		}
	}
}

impl<Lit: Literal, C: Coefficient> LinearConstraint<Lit, C> {
	pub fn new(exp: LinExp<Lit, C>, cmp: Comparator, k: C) -> Self {
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

impl<Lit: Literal, C: Coefficient> From<&IntVarEnc<Lit, C>> for LinExp<Lit, C> {
	fn from(x: &IntVarEnc<Lit, C>) -> Self {
		x.as_lin_exp()
	}
}

impl<Lit: Literal, C: Coefficient> Checker for LinearConstraint<Lit, C> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let lhs = self.exp.assign(solution)?;
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Comparator {
	LessEq,
	Equal,
	GreaterEq,
}

#[derive(Debug, Clone)]
pub(crate) enum Constraint<C: Coefficient> {
	AtMostOne,
	ImplicationChain,
	Domain { lb: C, ub: C },
}

impl<Lit, C> Part<Lit, C> {
	fn iter(&self) -> std::slice::Iter<(Lit, C)> {
		match self {
			Part::Amo(terms) => terms.iter(),
			Part::Ic(terms) => terms.iter(),
			Part::Dom(terms, _lb, _ub) => terms.iter(),
		}
	}
}

impl<Lit: Literal, C: Coefficient> LinExp<Lit, C> {
	pub fn new() -> Self {
		Self {
			..Default::default()
		}
	}

	pub fn from_slices(weights: &[C], lits: &[Lit]) -> Self {
		assert!(weights.len() == lits.len(), "");
		Self {
			terms: lits.iter().cloned().zip(weights.iter().cloned()).collect(),
			num_free: lits.len(),
			..Default::default()
		}
	}

	pub fn from_terms(terms: &[(Lit, C)]) -> Self {
		Self {
			terms: terms.iter().cloned().collect(),
			num_free: terms.len(),
			..Default::default()
		}
	}

	/// Add multiple terms to the linear expression of which at most one
	/// can be chosen
	pub fn add_choice(mut self, choice: &[(Lit, C)]) -> Self {
		if let [term] = choice {
			self += term.clone();
		} else {
			self.terms.extend(choice.iter().cloned());
			self.constraints.push((Constraint::AtMostOne, choice.len()))
		}
		self
	}

	/// Add multiple terms to the linear expression where the literal
	/// in each term is implied by the literal in the consecutive term
	pub fn add_chain(mut self, chain: &[(Lit, C)]) -> Self {
		if let [term] = chain {
			self += term.clone();
		} else {
			self.terms.extend(chain.iter().cloned());
			self.constraints
				.push((Constraint::ImplicationChain, chain.len()))
		}
		self
	}

	pub fn add_constant(mut self, k: C) -> Self {
		self.add += k;
		self
	}

	pub fn add_lit(mut self, lit: Lit) -> Self {
		self += (lit, C::one());
		self
	}

	// TODO I'm not really happy with this interface yet...
	// Probably makes more sense to use something like int encodings
	pub fn add_bounded_log_encoding(mut self, terms: &[(Lit, C)], lb: C, ub: C) -> Self {
		self.constraints
			.push((Constraint::Domain { lb, ub }, terms.len()));
		self.terms.extend(terms.iter().cloned());
		self
	}

	pub(crate) fn iter(&self) -> impl Iterator<Item = (Option<Constraint<C>>, Vec<&(Lit, C)>)> {
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

	pub(crate) fn assign(&self, solution: &[Lit]) -> Result<C, CheckError<Lit>> {
		let evaluate = |assignments: &Vec<(Lit, C, Lit)>| {
			assignments
				.iter()
				.fold(C::zero(), |acc, (lit, coef, assignment)| {
					acc + if lit == assignment { *coef } else { C::zero() }
				})
		};
		self.iter().fold(Ok(self.add), |acc, (constraint,terms) | {
            let assignments = terms.into_iter().map(|(lit,coef)| {
                let assignment = solution.iter().find(|x| x.var() == lit.var()).unwrap_or_else(|| panic!("Could not find lit {lit:?} in solution {solution:?}; perhaps this variable did not occur in any clause"));
                                                    (
                    lit.clone(),*coef,assignment.clone())
                    }).collect::<Vec<(Lit,C,Lit)>>();

            let is_consistent = match constraint {
                Some(Constraint::AtMostOne) => assignments.iter().filter(|(lit,_,a)| lit == a).count() <= 1,
                Some(Constraint::ImplicationChain) =>  assignments.iter().map(|(lit,_,a)| lit == a).tuple_windows().all(|(a, b)| a.cmp(&b).is_ge()),
                Some(Constraint::Domain { lb, ub }) => {
                    let a = evaluate(&assignments);
                    lb <= a && a <= ub
                }
                None => true
            };

            if is_consistent {
                Ok(acc?+evaluate(&assignments) * self.mult)
            } else {
                Err(CheckError::Unsatisfiable(Unsatisfiable))
            }
		})
	}

	pub fn terms(&self) -> std::collections::vec_deque::Iter<'_, (Lit, C)> {
		self.terms.iter()
	}
}

impl<Lit: Literal, C: Coefficient> Default for LinExp<Lit, C> {
	fn default() -> Self {
		Self {
			terms: VecDeque::new(),
			num_free: 0,
			constraints: Vec::new(),
			add: C::zero(),
			mult: C::one(),
		}
	}
}

impl<Lit: Literal, C: Coefficient> From<Lit> for LinExp<Lit, C> {
	fn from(lit: Lit) -> Self {
		Self {
			terms: VecDeque::from([(lit, C::one())]),
			num_free: 1,
			..Default::default()
		}
	}
}
impl<Lit: Literal, C: Coefficient> From<(Lit, C)> for LinExp<Lit, C> {
	fn from(term: (Lit, C)) -> Self {
		Self {
			terms: VecDeque::from([term]),
			num_free: 1,
			..Default::default()
		}
	}
}
impl<'a, Lit: Literal, C: Coefficient> From<IntEncoding<'a, Lit, C>> for LinExp<Lit, C> {
	fn from(var: IntEncoding<'a, Lit, C>) -> Self {
		match var {
			IntEncoding::Direct { first, vals } => {
				let mut terms = VecDeque::with_capacity(vals.len());
				let mut k = first;
				for lit in vals {
					terms.push_back((lit.clone(), k));
					k += C::one();
				}
				Self {
					terms,
					constraints: vec![(Constraint::AtMostOne, vals.len())],
					..Default::default()
				}
			}
			IntEncoding::Order { first, vals } => Self {
				terms: vals.iter().map(|lit| (lit.clone(), C::one())).collect(),
				constraints: vec![(Constraint::ImplicationChain, vals.len())],
				add: first,
				..Default::default()
			},
			IntEncoding::Log { signed, bits } => {
				let mut terms = VecDeque::with_capacity(bits.len());
				let two = C::one() + C::one();
				let mut k = C::one();
				for lit in bits {
					terms.push_back((lit.clone(), k));
					k *= two;
				}
				if signed {
					terms.back_mut().unwrap().1 *= -C::one();
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

impl<Lit: Literal, C: Coefficient> AddAssign<(Lit, C)> for LinExp<Lit, C> {
	fn add_assign(&mut self, rhs: (Lit, C)) {
		self.terms.push_front(rhs);
		self.num_free += 1
	}
}
impl<Lit: Literal, C: Coefficient> Add<(Lit, C)> for LinExp<Lit, C> {
	type Output = LinExp<Lit, C>;
	fn add(mut self, rhs: (Lit, C)) -> Self::Output {
		self += rhs;
		self
	}
}
impl<'a, Lit: Literal, C: Coefficient> AddAssign<IntEncoding<'a, Lit, C>> for LinExp<Lit, C> {
	fn add_assign(&mut self, rhs: IntEncoding<'a, Lit, C>) {
		match rhs {
			IntEncoding::Direct { first, vals } => {
				let mut k = first;
				for lit in vals {
					self.terms.push_back((lit.clone(), k));
					k += C::one();
				}
				self.constraints.push((Constraint::AtMostOne, vals.len()))
			}
			IntEncoding::Order { first, vals } => {
				for lit in vals {
					self.terms.push_back((lit.clone(), C::one()))
				}
				self.add += first;
				self.constraints
					.push((Constraint::ImplicationChain, vals.len()))
			}
			IntEncoding::Log { signed, bits } => {
				let two = C::one() + C::one();
				let mut k = C::one();
				for lit in bits {
					self.terms.push_front((lit.clone(), k));
					k *= two;
				}
				// TODO!
				if signed {
					self.terms.front_mut().unwrap().1 *= -C::one();
				}
				self.num_free += bits.len();
			}
		}
	}
}

impl<'a, Lit: Literal, C: Coefficient> Add<IntEncoding<'a, Lit, C>> for LinExp<Lit, C> {
	type Output = LinExp<Lit, C>;
	fn add(mut self, rhs: IntEncoding<'a, Lit, C>) -> Self::Output {
		self += rhs;
		self
	}
}
impl<Lit: Literal, C: Coefficient> AddAssign<LinExp<Lit, C>> for LinExp<Lit, C> {
	fn add_assign(&mut self, rhs: LinExp<Lit, C>) {
		// Multiply the current expression
		if self.mult != C::one() {
			self.add *= self.mult;
			for term in &mut self.terms {
				term.1 *= self.mult;
			}
		}
		self.mult = C::one();
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
		self.constraints.extend(rhs.constraints.into_iter());
	}
}
impl<Lit: Literal, C: Coefficient> Add<LinExp<Lit, C>> for LinExp<Lit, C> {
	type Output = LinExp<Lit, C>;
	fn add(mut self, rhs: LinExp<Lit, C>) -> Self::Output {
		self += rhs;
		self
	}
}

impl<Lit: Literal, C: Coefficient> MulAssign<C> for LinExp<Lit, C> {
	fn mul_assign(&mut self, rhs: C) {
		self.mult *= rhs;
	}
}
impl<Lit: Literal, C: Coefficient> Mul<C> for LinExp<Lit, C> {
	type Output = LinExp<Lit, C>;
	fn mul(mut self, rhs: C) -> Self::Output {
		self *= rhs;
		self
	}
}

impl<Lit: Literal, C: Coefficient> Checker for Linear<Lit, C> {
	type Lit = Lit;

	fn check(&self, solution: &[Self::Lit]) -> Result<(), crate::CheckError<Self::Lit>> {
		let lhs = &self
			.terms
			.iter()
			.flat_map(|part| part.iter().map(|(lit, coef)| (lit.clone(), **coef)))
			.fold(C::zero(), |acc, (lit, coef)| {
				let a = solution.iter().find(|x| x.var() == lit.var());
				acc + if lit == *a.unwrap() {
					C::one()
				} else {
					C::zero()
				} * coef
			});
		if match self.cmp {
			LimitComp::LessEq => *lhs <= *self.k,
			LimitComp::Equal => *lhs == *self.k,
		} {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

#[derive(Default)]
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

impl<DB: ClauseDatabase, C: Coefficient, Enc: Encoder<DB, LinVariant<DB::Lit, C>>>
	Encoder<DB, LinearConstraint<DB::Lit, C>> for LinearEncoder<Enc>
{
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "linear_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &LinearConstraint<DB::Lit, C>) -> Result {
		let variant = self.agg.aggregate(db, lin)?;
		self.enc.encode(db, &variant)
	}
}

// This is just a linear encoder that currently makes an arbitrary choice.
// This is probably not how we would like to do it in the future.
#[derive(Default)]
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
		C: Coefficient,
		LinEnc: Encoder<DB, Linear<DB::Lit, C>>,
		CardEnc: Encoder<DB, Cardinality<DB::Lit, C>>,
		AmoEnc: Encoder<DB, CardinalityOne<DB::Lit>>,
	> Encoder<DB, LinVariant<DB::Lit, C>> for StaticLinEncoder<LinEnc, CardEnc, AmoEnc>
{
	fn encode(&mut self, db: &mut DB, lin: &LinVariant<DB::Lit, C>) -> Result {
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
	use super::Part;
	use crate::PosCoeff;

	pub(crate) fn construct_terms(terms: &[(i32, i32)]) -> Vec<Part<i32, PosCoeff<i32>>> {
		terms
			.iter()
			.map(|(lit, coef)| Part::Amo(vec![(lit.clone(), PosCoeff::from(coef.clone()))]))
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
						k: 6.into()
					}
					=> vec![
						vec![-1, -2, -3], // 0
						vec![ 1, -2, -3], // 2
						vec![-1,  2, -3], // 3
						vec![ 1,  2, -3], // 5
						vec![-1, -2,  3], // 5
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
						k: 19.into()
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
						k: 5.into()
					}
					=> vec![
						vec![-1, -2, -3],
						vec![ 1, -2, -3],
						vec![-1,  2, -3],
						vec![ 1,  2, -3],
						vec![-1, -2,  3],
						vec![ 1, -2,  3],
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
						k: 10.into()
					}
                    => vec![
                        vec![-1, -2, -3],
                        vec![1, -2, -3],
                        vec![-1, 2, -3],
                        vec![1, 2, -3],
                        vec![-1, -2, 3],
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
						k: 5.into()
					}
					=> vec![
						vec![ 1, -2,  3],
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
						k: 3.into()
					}
					=> vec![
						vec![-1, -2,  3],
						vec![ 1,  2, -3],
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
						k: 10.into()
					}
					=> vec![
						vec![-1, 2,-3, 4],
						vec![ 1, 2, 3,-4],
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
						k: 4.into()
					}
					=> vec![
						vec![ 1,-2,-3, 4],
						vec![-1,-2, 3, 4],
						vec![ 1,-2, 3,-4],
					]
				);
			}

            /*
             * TODO add clausees for Ics (otherwise test won't work for all encoders)
            #[test]
            fn test_eq_with_ics() {
                assert_sol!(
                    $encoder,
                    6,
                    &Linear {
                        terms: vec![
                            Part::Ic(vec![(1, PosCoeff(4)), (2, PosCoeff(4))]),
                            Part::Ic(vec![(3, PosCoeff(4)), (4, PosCoeff(4))]),
                            Part::Ic(vec![(5, PosCoeff(5)), (6, PosCoeff(5))]),
                        ],
                        cmp: LimitComp::Equal,
                        k: PosCoeff(18),
                    }
                    =>
                    vec![
                    vec![1, 2, -3, -4, 5, 6],
                    vec![1, -2, 3, -4, 5, 6],
                    vec![-1, -2, 3, 4, 5, 6],
                    ]
                        );
            }
            */
		};


	}
	pub(crate) use linear_test_suite;
}
