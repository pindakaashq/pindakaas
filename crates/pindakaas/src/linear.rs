use std::{
	collections::{HashMap, VecDeque},
	marker::PhantomData,
	ops::{Add, AddAssign, Mul, MulAssign},
};

use crate::{
	AtMostOne, Cardinality, CheckError, Checker, ClauseDatabase, Coefficient, Encoder, IntEncoding,
	Literal, PairwiseEncoder, PositiveCoefficient, Result, Unsatisfiable,
};

mod adder;
mod bdd;
mod swc;
mod totalizer;

pub use adder::AdderEncoder;
pub use bdd::BddEncoder;
pub use swc::SwcEncoder;
pub use totalizer::TotalizerEncoder;

#[derive(Debug)]
pub enum LinVariant<Lit: Literal, PC: PositiveCoefficient> {
	Linear(Linear<Lit, PC>),
	Cardinality(Cardinality<Lit, PC>),
	AtMostOne(AtMostOne<Lit>),
	Trivial,
}

#[derive(Debug)]
pub struct Linear<Lit: Literal, PC: PositiveCoefficient> {
	pub(crate) terms: Vec<Part<Lit, PC>>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PC,
}

// TODO how can we support both Part(itions) of "terms" ( <Lit, C> for pb
// constraints) and just lits (<Lit>) for AMK/AMO's?
//
// TODO add EO, and probably something for Unconstrained
// TODO this can probably follow the same structure as LinExp
#[derive(Debug)]
pub(crate) enum Part<Lit, C> {
	Amo(Vec<(Lit, C)>),
	Ic(Vec<(Lit, C)>),
	Dom(Vec<(Lit, C)>, C, C),
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum LimitComp {
	Equal,
	LessEq,
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
	add: C,
	/// Multiplicative contant
	mult: C,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Comparator {
	LessEq,
	Equal,
	GreaterEq,
}

#[derive(Debug, Clone)]
enum Constraint<C: Coefficient> {
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
					terms: VecDeque::from(terms),
					constraints: Vec::from([(Constraint::AtMostOne, vals.len())]),
					..Default::default()
				}
			}
			IntEncoding::Order { first, vals } => Self {
				terms: vals.iter().map(|lit| (lit.clone(), C::one())).collect(),
				constraints: Vec::from([(Constraint::ImplicationChain, vals.len())]),
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
					terms: VecDeque::from(terms),
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

impl<'a, Lit: Literal, C: Coefficient> MulAssign<C> for LinExp<Lit, C> {
	fn mul_assign(&mut self, rhs: C) {
		self.mult += rhs;
	}
}
impl<'a, Lit: Literal, C: Coefficient> Mul<C> for LinExp<Lit, C> {
	type Output = LinExp<Lit, C>;
	fn mul(mut self, rhs: C) -> Self::Output {
		self *= rhs;
		self
	}
}

impl<Lit: Literal, PC: PositiveCoefficient> Checker for Linear<Lit, PC> {
	type Lit = Lit;

	fn check(&self, solution: &[Self::Lit]) -> Result<(), crate::CheckError<Self::Lit>> {
		let abs = |l: Lit| if l.is_negated() { l.negate() } else { l };
		let lhs = &self
			.terms
			.iter()
			.flat_map(|part| part.iter().map(|(lit, coef)| (lit.clone(), *coef)))
			.fold(PC::zero(), |acc, (lit, coef)| {
				let a = solution
					.iter()
					.find(|x| abs((*x).clone()) == abs(lit.clone()));
				acc + if lit == *a.unwrap() {
					PC::one()
				} else {
					PC::zero()
				} * coef
			});
		if match self.cmp {
			LimitComp::LessEq => *lhs <= self.k,
			LimitComp::Equal => *lhs == self.k,
		} {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

pub trait LinVariantEncoder<Lit: Literal, PC: PositiveCoefficient>:
	Encoder<Lit = Lit, Ret = ()>
{
	fn new(variant: LinVariant<Lit, PC>) -> Self;
}

pub struct LinearEncoder<
	'a,
	Lit: Literal,
	C: Coefficient,
	PC: PositiveCoefficient + TryFrom<C>,
	Enc: LinVariantEncoder<Lit, PC> = ArbLinEncoder<Lit, PC>,
> {
	exp: &'a LinExp<Lit, C>,
	cmp: Comparator,
	k: C,
	_pc: PhantomData<PC>,
	_enc: PhantomData<Enc>,
}

impl<
		'a,
		Lit: Literal,
		C: Coefficient,
		PC: PositiveCoefficient + TryFrom<C>,
		Enc: LinVariantEncoder<Lit, PC>,
	> LinearEncoder<'a, Lit, C, PC, Enc>
{
	pub fn new(exp: &'a LinExp<Lit, C>, cmp: Comparator, k: C) -> Self {
		Self {
			exp,
			cmp,
			k,
			_pc: PhantomData,
			_enc: PhantomData,
		}
	}
}

impl<
		'a,
		Lit: Literal,
		C: Coefficient,
		PC: PositiveCoefficient + TryFrom<C>,
		Enc: LinVariantEncoder<Lit, PC>,
	> Encoder for LinearEncoder<'a, Lit, C, PC, Enc>
{
	type Lit = Lit;
	type Ret = ();

	fn encode<DB: ClauseDatabase<Lit = Self::Lit>>(&mut self, db: &mut DB) -> Result<Self::Ret> {
		let variant = LinearAggregator::new(self.exp, self.cmp, self.k).encode(db)?;
		Enc::new(variant).encode(db)
	}
}

// This is just a linear encoder that currently makes an arbitrary choice.
// This is probably not how we would like to do it in the future.
pub struct ArbLinEncoder<Lit: Literal, PC: PositiveCoefficient> {
	lin: LinVariant<Lit, PC>,
}
impl<Lit: Literal, PC: PositiveCoefficient> LinVariantEncoder<Lit, PC> for ArbLinEncoder<Lit, PC> {
	fn new(lin: LinVariant<Lit, PC>) -> Self {
		Self { lin }
	}
}
impl<Lit: Literal, PC: PositiveCoefficient> Encoder for ArbLinEncoder<Lit, PC> {
	type Lit = Lit;
	type Ret = ();

	fn encode<DB: ClauseDatabase<Lit = Self::Lit>>(&mut self, db: &mut DB) -> Result<Self::Ret> {
		match &self.lin {
			LinVariant::Linear(lin) => AdderEncoder::new(lin).encode(db),
			LinVariant::Cardinality(_) => unimplemented!(),
			LinVariant::AtMostOne(amo) => PairwiseEncoder::new(amo).encode(db),
			LinVariant::Trivial => Ok(()),
		}
	}
}
pub struct LinearAggregator<'a, Lit: Literal, C: Coefficient, PC: PositiveCoefficient + TryFrom<C>>
{
	exp: &'a LinExp<Lit, C>,
	cmp: Comparator,
	k: C,
	_pc: PhantomData<PC>,
}

impl<'a, Lit: Literal, C: Coefficient, PC: PositiveCoefficient + TryFrom<C>>
	LinearAggregator<'a, Lit, C, PC>
{
	pub fn new(exp: &'a LinExp<Lit, C>, cmp: Comparator, k: C) -> Self {
		Self {
			exp,
			cmp,
			k,
			_pc: PhantomData,
		}
	}
}

impl<'a, Lit: Literal, C: Coefficient, PC: PositiveCoefficient + TryFrom<C>> Encoder
	for LinearAggregator<'a, Lit, C, PC>
{
	type Lit = Lit;
	type Ret = LinVariant<Lit, PC>;

	fn encode<DB: ClauseDatabase<Lit = Self::Lit>>(&mut self, db: &mut DB) -> Result<Self::Ret> {
		// Convert ≤ to ≥ and aggregate multiple occurrences of the same
		// variable.
		let mut agg = HashMap::with_capacity(self.exp.terms.len());
		for term in &self.exp.terms {
			let var = term.0.var();
			let entry = agg.entry(var).or_insert_with(C::zero);
			let mut coef = term.1 * self.exp.mult;
			if term.0.is_negated() ^ (self.cmp == Comparator::GreaterEq) {
				coef *= -C::one()
			}
			*entry += coef;
		}

		let mut partition = Vec::with_capacity(self.exp.constraints.len());
		// Adjust side constraints when literals are combined (and currently transform to partition structure)
		let mut iter = self.exp.terms.iter().skip(self.exp.num_free);
		for con in &self.exp.constraints {
			let mut terms = Vec::with_capacity(con.1);
			for _ in 0..con.1 {
				let term = iter.next().unwrap();
				let entry = agg.remove_entry(&term.0.var());
				if let Some(term) = entry {
					terms.push(term)
				}
			}
			if !terms.is_empty() {
				match con.0 {
					Constraint::AtMostOne => partition.push(Part::Amo(terms)),
					Constraint::ImplicationChain => partition.push(Part::Ic(terms)),
					Constraint::Domain { lb, ub } => {
						let coef = terms[0].1;
						let still_log = |terms: &Vec<(Lit, C)>| {
							terms
								.iter()
								.enumerate()
								.all(|(i, (_, c))| c == &(num::pow(C::from(2).unwrap(), i) * coef))
						};
						// Domain constraint can only be enforced when PB is coef*(x1 + 2x2 + 4x3 + ...), where l <= x1 + 2*x2 + 4*x3 + ... <= u
						if terms.len() == con.1 && still_log(&terms) {
							// Adjust the bounds to account for coef
							let (lb, ub) = if self.cmp == Comparator::GreaterEq {
								// 0..range can be encoded by the bits multiplied by coef
								let range =
									-terms.iter().fold(C::zero(), |acc, (_, coef)| acc + *coef);
								// this range is inverted if we have flipped the comparator
								(range - ub, range - lb)
							} else {
								// in both cases, l and u now represent the true constraint
								(terms[0].1 * lb, terms[0].1 * ub)
							};
							partition.push(Part::Dom(terms, lb, ub))
						} else {
							for term in terms {
								partition.push(Part::Amo(vec![term]));
							}
						}
					}
				}
			}
		}
		// Add remaining (unconstrained) terms
		debug_assert!(agg.len() <= self.exp.num_free);
		for term in agg.drain() {
			partition.push(Part::Amo(vec![term]));
		}

		let mut k = if self.cmp == Comparator::GreaterEq {
			-self.k
		} else {
			self.k
		} - self.exp.add;
		let cmp = match self.cmp {
			Comparator::LessEq | Comparator::GreaterEq => LimitComp::LessEq,
			Comparator::Equal => LimitComp::Equal,
		};

		let into_positive_coefficient = |coef: C| -> PC {
			match coef.try_into() {
				Ok(coef) => coef,
				Err(_) => {
					panic!("Unable to convert coefficient to positive coefficient.")
				}
			}
		};

		// TODO cannot construct this as a closures due to inner closures problem
		let convert_term_if_negative = |term: (Lit, C), k: &mut C| -> (Lit, PC) {
			let (mut lit, mut coef) = term;
			if coef.is_negative() {
				coef = -coef;
				lit = lit.negate();
				*k += coef;
			};
			(lit, into_positive_coefficient(coef))
		};

		let partition: Vec<Part<Lit, PC>> = partition
			.into_iter()
			.filter(|part| part.iter().next().is_some()) // filter out empty groups
			.flat_map(|part| {
				// convert terms with negative coefficients
				match part {
					Part::Amo(mut terms) => {
						if terms.len() == 1 {
							return vec![Part::Amo(
								terms
									.into_iter()
									.filter(|(_, coef)| coef != &C::zero())
									.map(|(lit, coef)| {
										convert_term_if_negative((lit, coef), &mut k)
									})
									.collect(),
							)];
						}

						// Find most negative coefficient
						let (min_index, (_, min_coef)) = terms
							.iter()
							.enumerate()
							.min_by(|(_, (_, a)), (_, (_, b))| a.cmp(b))
							.expect("Partition should not contain constraint on zero terms");

						// If negative, normalize without breaking AMO constraint
						if min_coef.is_negative() {
							let q = -*min_coef;

							// this term will cancel out later when we add q*min_lit to the LHS
							terms.remove(min_index);

							// add aux var y and constrain y <-> ( ~x1 /\ ~x2 /\ ... )
							let y = db.new_var();
							db.add_clause(
								&terms
									.iter()
									.map(|(lit, _)| lit.negate())
									.chain(std::iter::once(y.clone()))
									.collect::<Vec<Lit>>(),
							)
							.unwrap();
							for lit in terms.iter().map(|tup| tup.0.clone()) {
								db.add_clause(&[y.negate(), lit]).unwrap();
							}

							// since y + x1 + x2 + ... = 1 (exactly-one), we have q*y + q*x1 + q*x2 + ... = q
							// after adding term 0*y, we can add q*y + q*x1 + q*x2 + ... on the LHS, and q on the RHS
							terms.push((y, C::zero())); // note: it's fine to add y into the same AMO group
							terms = terms
								.iter()
								.map(|(lit, coef)| (lit.clone(), *coef + q))
								.collect();
							k += q;
						}

						// all coefficients should be positive (since we subtracted the most negative coefficient)
						vec![Part::Amo(
							terms
								.into_iter()
								.map(|(lit, coef)| (lit, into_positive_coefficient(coef)))
								.collect(),
						)]
					}
					Part::Ic(terms) => {
						// normalize by splitting up the chain into two chains by coef polarity, inverting the coefs of the neg
						let (pos_chain, neg_chain): (_, Vec<(Lit, C)>) =
							terms.into_iter().partition(|(_, coef)| coef.is_positive());
						vec![
							Part::Ic(
								pos_chain
									.into_iter()
									.map(|(lit, coef)| (lit, into_positive_coefficient(coef)))
									.collect(),
							),
							Part::Ic(
								neg_chain
									.into_iter()
									.map(|(lit, coef)| {
										convert_term_if_negative((lit, coef), &mut k)
									})
									.rev() // x1 <- x2 <- x3 <- ... becomes ~x1 -> ~x2 -> ~x3 -> ...
									.collect(),
							),
						]
					}
					Part::Dom(terms, l, u) => {
						assert!(
							terms.iter().all(|(_,coef)| coef.is_positive())
								|| terms.iter().all(|(_,coef)| coef.is_negative()),
                                "Normalizing mixed positive/negative coefficients not yet supported for Dom constraint on {:?}", terms
						);
						vec![Part::Dom(
							terms
								.into_iter()
								.map(|(lit, coef)| convert_term_if_negative((lit, coef), &mut k))
								.collect(),
							into_positive_coefficient(l),
							into_positive_coefficient(u),
						)]
					}
				}
			})
			.map(|part| {
				// This step has to come *after* Amo normalization
				let filter_zero_coefficients = |terms: Vec<(Lit, PC)>| -> Vec<(Lit, PC)> {
					terms
						.into_iter()
						.filter(|(_, coef)| coef != &PC::zero())
						.collect()
				};

				match part {
					Part::Amo(terms) => Part::Amo(filter_zero_coefficients(terms)),
					Part::Ic(terms) => Part::Ic(filter_zero_coefficients(terms)),
					Part::Dom(terms, l, u) => Part::Dom(filter_zero_coefficients(terms), l, u),
				}
			})
			.filter(|part| part.iter().next().is_some()) // filter out empty groups
			.collect();

		// trivial case: constraint is unsatisfiable
		if k < C::zero() {
			return Err(Unsatisfiable);
		}
		// trivial case: no literals can be activated
		if k == C::zero() {
			for part in partition {
				for (lit, _) in part.iter() {
					db.add_clause(&[lit.negate()])?
				}
			}
			return Ok(LinVariant::Trivial);
		}

		let mut k = into_positive_coefficient(k);

		// Remove terms with coefs higher than k
		let partition = partition
			.into_iter()
			.map(|part| match part {
				Part::Amo(terms) => Part::Amo(
					terms
						.into_iter()
						.filter(|(lit, coef)| {
							if coef > &k {
								db.add_clause(&[lit.negate()]).unwrap();
								false
							} else {
								true
							}
						})
						.collect(),
				),
				Part::Ic(terms) => {
					// for IC, we can compare the running sum to k
					let mut acc = PC::zero();
					Part::Ic(
						terms
							.into_iter()
							.filter(|(lit, coef)| {
								acc += *coef;
								if acc > k {
									db.add_clause(&[lit.negate()]).unwrap();
									false
								} else {
									true
								}
							})
							.collect(),
					)
				}
				Part::Dom(terms, l, u) => {
					// remove terms exceeding k
					let terms = terms
						.into_iter()
						.filter(|(lit, coef)| {
							if coef > &k {
								db.add_clause(&[lit.negate()]).unwrap();
								false
							} else {
								true
							}
						})
						.collect::<Vec<_>>();
					// the one or more of the most significant bits have been removed, the upper bound could have dropped to a power of 2 (but not beyond)
					let u = std::cmp::min(
						u,
						terms
							.iter()
							.map(|(_, coef)| coef)
							.fold(PC::zero(), |a, b| a + *b),
					);
					Part::Dom(terms, l, u)
				}
			})
			.collect::<Vec<Part<Lit, PC>>>();

		// Check whether some literals can violate / satisfy the constraint
		let lhs_ub: PC = partition.iter().fold(PC::zero(), |acc, part| match part {
			Part::Amo(terms) => acc + terms.iter().map(|tup| tup.1).max().unwrap_or_else(PC::zero),
			Part::Ic(terms) | Part::Dom(terms, _, _) => {
				acc + terms.iter().fold(PC::zero(), |acc, (_, coef)| acc + *coef)
				// TODO max(k, acc + ..)
			}
		});

		match cmp {
			LimitComp::LessEq => {
				if lhs_ub <= k {
					return Ok(LinVariant::Trivial);
				}

				// If we have only 2 (unassigned) lits, which together (but not individually) exceed k, then -x1\/-x2
				if partition.iter().flat_map(|part| part.iter()).count() == 2 {
					db.add_clause(
						&partition
							.iter()
							.flat_map(|part| part.iter())
							.map(|(lit, _)| lit.negate())
							.collect::<Vec<Lit>>(),
					)?;
					return Ok(LinVariant::Trivial);
				}
			}
			LimitComp::Equal => {
				if lhs_ub < k {
					return Err(Unsatisfiable);
				}
				if lhs_ub == k {
					for part in partition {
						match part {
							Part::Amo(terms) => {
								db.add_clause(&[terms
									.iter()
									.max_by(|(_, a), (_, b)| a.cmp(b))
									.unwrap()
									.0
									.clone()])?;
							}
							Part::Ic(terms) | Part::Dom(terms, _, _) => {
								for (lit, _) in terms {
									db.add_clause(&[lit.clone()])?;
								}
							}
						};
					}
					return Ok(LinVariant::Trivial);
				}
			}
		}

		// debug_assert!(!partition.flat().is_empty());

		// TODO any smart way to implement len() method?
		// TODO assert all groups are non-empty / discard empty groups?
		debug_assert!(partition
			.iter()
			.flat_map(|part| part.iter())
			.next()
			.is_some());

		// special case: all coefficients are equal (and can be made one)
		let val = partition
			.iter()
			.flat_map(|part| part.iter().map(|(_, coef)| coef))
			.next()
			.unwrap();

		if partition
			.iter()
			.flat_map(|part| part.iter())
			.all(|(_, coef)| *coef == *val)
		{
			// trivial case: k cannot be made from the coefficients
			if cmp == LimitComp::Equal && k % *val != PC::zero() {
				return Err(Unsatisfiable);
			}

			k /= *val;
			let partition = partition
				.iter()
				.flat_map(|part| part.iter())
				.map(|(lit, _)| lit.clone())
				.collect::<Vec<Lit>>();
			if k == PC::one() {
				// Encode At Least One constraint
				if cmp == LimitComp::Equal {
					db.add_clause(&partition.to_vec())?
				}
				// Encode At Most One constraint
				return Ok(LinVariant::AtMostOne(AtMostOne { lits: partition }));
			}
			// Encode count constraint
			return Ok(LinVariant::Cardinality(Cardinality {
				lits: partition,
				cmp,
				k,
			}));
		}

		// Default case: encode pseudo-Boolean linear constraint
		Ok(LinVariant::Linear(Linear {
			terms: partition,
			cmp,
			k,
		}))
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;

	use super::*;
	use crate::helpers::tests::{assert_enc_sol, TestDB};
	use crate::{AtMostOne, Linear, Unsatisfiable};

	pub(crate) fn construct_terms(terms: &[(i32, u32)]) -> Vec<Part<i32, u32>> {
		terms
			.iter()
			.map(|(lit, coef)| Part::Amo(vec![(lit.clone(), coef.clone())]))
			.collect()
	}

	#[test]
	fn test_combine() {
		let mut db = TestDB::new(3).expect_clauses(vec![]);
		// Simple aggregation of multiple occurrences of the same literal
		assert_eq!(
			LinearAggregator::<i32, i32, u32>::new(
				&(LinExp::from((1, 1)) + (1, 2) + (2, 1) + (3, 2)),
				Comparator::LessEq,
				3
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 3), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 3
			}))
		);

		// Aggregation of positive and negative occurrences of the same literal
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (-1, 2) + (2, 1) + (3, 2)),
				Comparator::LessEq,
				2
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(-1, 1), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 3
			}))
		);

		// Aggregation of positive and negative coefficients of the same literal
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (1, -2) + (2, 1) + (3, 2)),
				Comparator::LessEq,
				2,
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(-1, 1), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 3
			}))
		);
		db.check_complete()
	}

	#[test]
	fn test_detection() {
		let mut db = TestDB::new(3);

		// Correctly detect at most one
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (2, 1) + (3, 1)),
				Comparator::LessEq,
				1
			)
			.encode(&mut db),
			Ok(LinVariant::AtMostOne(AtMostOne {
				lits: vec![1, 2, 3],
			}))
		);
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 2)) + (2, 2) + (3, 2)),
				Comparator::LessEq,
				2
			)
			.encode(&mut db),
			Ok(LinVariant::AtMostOne(AtMostOne {
				lits: vec![1, 2, 3],
			}))
		);

		// Correctly detect at most k
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (2, 1) + (3, 1)),
				Comparator::LessEq,
				2
			)
			.encode(&mut db),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3],
				cmp: LimitComp::LessEq,
				k: 2,
			}))
		);
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 3)) + (2, 3) + (3, 3)),
				Comparator::LessEq,
				7
			)
			.encode(&mut db),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3],
				cmp: LimitComp::LessEq,
				k: 2,
			}))
		);

		// Correctly detect equal k
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (2, 1) + (3, 1)),
				Comparator::Equal,
				2
			)
			.encode(&mut db),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3],
				cmp: LimitComp::Equal,
				k: 2,
			}))
		);
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 3)) + (2, 3) + (3, 3)),
				Comparator::Equal,
				6
			)
			.encode(&mut db),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3],
				cmp: LimitComp::Equal,
				k: 2,
			}))
		);

		// Is still normal Boolean linear in-equality
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (2, 2) + (3, 2)),
				Comparator::LessEq,
				2
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 1), (2, 2), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 2,
			}))
		);

		// Is still normal Boolean linear equality
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (2, 2) + (3, 2)),
				Comparator::Equal,
				2
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 1), (2, 2), (3, 2)]),
				cmp: LimitComp::Equal,
				k: 2,
			}))
		);

		// Correctly identify that the AMO is limiting the LHS ub
		assert_eq!(
			LinearAggregator::new(
				&LinExp::from((3, -1)).add_choice(&[(1, -1), (2, -1)]),
				Comparator::LessEq,
				-2,
			)
			.encode(&mut db),
			Ok(LinVariant::Trivial)
		);
	}

	#[test]
	fn test_equal_one() {
		let mut db = TestDB::new(3).expect_clauses(vec![vec![1, 2, 3]]);
		// An exactly one constraint adds an at most one constraint + a clause for all literals
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (2, 1) + (3, 1)),
				Comparator::Equal,
				1
			)
			.encode(&mut db),
			Ok(LinVariant::AtMostOne(AtMostOne {
				lits: vec![1, 2, 3],
			}))
		);
		db.check_complete()
	}

	#[test]
	fn test_neg_coeff() {
		let mut db = TestDB::new(3);

		// Correctly convert a negative coefficient
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 2)) + (2, 3) + (3, -2)),
				Comparator::LessEq,
				2
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 2), (2, 3), (-3, 2)]),
				cmp: LimitComp::LessEq,
				k: 4
			}))
		);

		// Correctly convert multiple negative coefficients
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, -1)) + (2, -1) + (3, -1)),
				Comparator::LessEq,
				-2,
			)
			.encode(&mut db),
			Ok(LinVariant::AtMostOne(AtMostOne {
				lits: vec![-1, -2, -3],
			}))
		);
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, -1)) + (2, -2) + (3, -3)),
				Comparator::LessEq,
				-2,
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(-1, 1), (-2, 2), (-3, 3)]),
				cmp: LimitComp::LessEq,
				k: 4
			}))
		);

		// Correctly convert multiple negative coefficients with AMO constraints
		let mut db = TestDB::new(6);
		assert_eq!(
			LinearAggregator::new(
				&LinExp::default()
					.add_choice(&[(1, -1), (2, -3), (3, -4)])
					.add_choice(&[(4, -2), (5, -3), (6, -5)]),
				Comparator::LessEq,
				-4,
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Amo(vec![(1, 3), (2, 1), (7, 4)]),
					Part::Amo(vec![(4, 3), (5, 2), (8, 5)]),
				],
				cmp: LimitComp::LessEq,
				k: 5
			}))
		);

		// Correctly convert multiple negative coefficients with side constraints
		let mut db = TestDB::new(6);
		assert_eq!(
			LinearAggregator::new(
				&LinExp::default().add_chain(&[(1, 1), (2, -3), (3, -2), (4, 2), (5, 5), (6, -3)]),
				Comparator::LessEq,
				3
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Ic(vec![(1, 1), (4, 2), (5, 5)]),
					Part::Ic(vec![(-6, 3), (-3, 2), (-2, 3)]),
				],
				cmp: LimitComp::LessEq,
				k: 11
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut db = TestDB::new(6);
		assert_eq!(
			LinearAggregator::new(
				&LinExp::default()
					.add_choice(&[(1, 1), (2, 2), (3, 3), (4, 4)])
					.add_choice(&[(5, 1), (6, 3)]),
				Comparator::GreaterEq,
				3,
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Amo(vec![(1, 3), (2, 2), (3, 1), (7, 4)]),
					Part::Amo(vec![(5, 2), (8, 3)]),
				],
				cmp: LimitComp::LessEq,
				k: 4 // -3 + 4 + 3
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut db = TestDB::new(6);
		assert_eq!(
			LinearAggregator::new(
				&LinExp::default()
					.add_chain(&[(1, 1), (2, 1), (3, 1), (4, 1)])
					.add_chain(&[(5, 1), (6, 2)]),
				Comparator::GreaterEq,
				3,
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Ic(vec![(-4, 1), (-3, 1), (-2, 1), (-1, 1)]),
					Part::Ic(vec![(-6, 2), (-5, 1)]),
				],
				cmp: LimitComp::LessEq,
				k: 4
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut db = TestDB::new(5);
		assert_eq!(
			LinearAggregator::new(
				&LinExp::default()
					.add_bounded_log_encoding(&[(1, 1), (2, 2), (3, 4)], 0, 5)
					.add_bounded_log_encoding(&[(4, 3), (5, 6)], 0, 2),
				Comparator::GreaterEq,
				3,
			)
			.encode(&mut db),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Dom(vec![(-1, 1), (-2, 2), (-3, 4)], 2, 7),
					Part::Dom(vec![(-4, 3), (-5, 6)], 7, 9),
				],
				cmp: LimitComp::LessEq,
				k: 13
			}))
		);
	}

	#[test]
	fn test_unsat() {
		let mut db = TestDB::new(3);

		// Constant cannot be reached
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (2, 2) + (3, 2)),
				Comparator::Equal,
				6
			)
			.encode(&mut db),
			Err(Unsatisfiable),
		);
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (2, 2) + (3, 2)),
				Comparator::GreaterEq,
				6,
			)
			.encode(&mut db),
			Err(Unsatisfiable),
		);
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 1)) + (2, 2) + (3, 2)),
				Comparator::LessEq,
				-1
			)
			.encode(&mut db),
			Err(Unsatisfiable),
		);

		// Scaled counting constraint with off-scaled Constant
		assert_eq!(
			LinearAggregator::new(
				&(LinExp::from((1, 4)) + (2, 4) + (3, 4)),
				Comparator::Equal,
				6
			)
			.encode(&mut db),
			Err(Unsatisfiable),
		);
	}

	#[test]
	fn test_pb_encode() {
		assert_enc_sol!(
			LinearEncoder::<i32,i32,u32>,
			4,
			&(LinExp::from((1,1)) + (2,1) + (3,1) + (4,2)),
			crate::Comparator::LessEq,
			1
			=>
			vec![
			vec![-4], vec![-3, -1], vec![-2, -1], vec![-3, -2]
			],
			vec![
				vec![-1, -2, -3, -4],
				vec![-1, -2, 3, -4],
				vec![-1, 2, -3, -4],
				vec![1, -2, -3, -4],
			]
		);
	}

	#[test]
	fn test_encoders() {
		// +7*x1 +10*x2 +4*x3 +4*x4 <= 9
		let mut db = TestDB::new(4).expect_solutions(vec![
			vec![-1, -2, -3, -4],
			vec![1, -2, -3, -4],
			vec![-1, -2, 3, -4],
			vec![-1, -2, -3, 4],
		]);
		// two.add_clause(&[-5]).unwrap();
		// TODO encode this if encoder does not support constraint
		assert!(PairwiseEncoder::new(&AtMostOne { lits: vec![1, 2] })
			.encode(&mut db)
			.is_ok());
		assert!(PairwiseEncoder::new(&AtMostOne { lits: vec![3, 4] })
			.encode(&mut db)
			.is_ok());
		assert!(LinearEncoder::<i32, i32, u32>::new(
			&LinExp::default()
				.add_choice(&[(1, 7), (2, 10)])
				.add_choice(&[(3, 4), (4, 4)]),
			crate::Comparator::LessEq,
			9,
		)
		.encode(&mut db)
		.is_ok());
		db.check_complete();
	}

	impl PartialEq for Part<i32, u32> {
		fn eq(&self, other: &Self) -> bool {
			let term_eq = |a: &Vec<(i32, u32)>, b: &Vec<(i32, u32)>| {
				itertools::equal(a.iter().sorted(), b.iter().sorted())
			};
			match self {
				Part::Amo(terms) => {
					if let Part::Amo(oterms) = other {
						term_eq(terms, oterms)
					} else {
						false
					}
				}
				Part::Ic(terms) => {
					if let Part::Ic(oterms) = other {
						term_eq(terms, oterms)
					} else {
						false
					}
				}
				Part::Dom(terms, l, u) => {
					if let Part::Dom(oterms, ol, ou) = other {
						term_eq(terms, oterms) && l == ol && u == ou
					} else {
						false
					}
				}
			}
		}
	}

	impl PartialOrd for Part<i32, u32> {
		fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
			let termcmp = |a: &Vec<(i32, u32)>, b: &Vec<(i32, u32)>| {
				let cmp = a.len().cmp(&b.len());
				if cmp != std::cmp::Ordering::Equal {
					cmp
				} else {
					for (a, b) in a.iter().sorted().zip_eq(other.iter().sorted()) {
						let cmp = a.0.cmp(&b.0);
						if cmp != std::cmp::Ordering::Equal {
							return cmp;
						}
						let cmp = a.1.cmp(&b.1);
						if cmp != std::cmp::Ordering::Equal {
							return cmp;
						}
					}
					std::cmp::Ordering::Equal
				}
			};
			Some(match self {
				Part::Amo(terms) => {
					if let Part::Amo(oterms) = other {
						termcmp(terms, oterms)
					} else {
						std::cmp::Ordering::Less
					}
				}
				Part::Ic(terms) => {
					if let Part::Ic(oterms) = other {
						termcmp(terms, oterms)
					} else {
						std::cmp::Ordering::Greater
					}
				}
				Part::Dom(terms, _, _) => {
					if let Part::Dom(oterms, _, _) = other {
						termcmp(terms, oterms)
					} else {
						std::cmp::Ordering::Less
					}
				}
			})
		}
	}

	impl PartialEq for LinVariant<i32, u32> {
		fn eq(&self, other: &Self) -> bool {
			let liteq =
				|a: &Vec<i32>, b: &Vec<i32>| itertools::equal(a.iter().sorted(), b.iter().sorted());
			let parteq = |a: &Vec<Part<i32, u32>>, b: &Vec<Part<i32, u32>>| {
				itertools::equal(
					a.iter()
						.map(|p| p.iter().sorted().collect::<Vec<&(i32, u32)>>())
						.sorted(),
					b.iter()
						.map(|p| p.iter().sorted().collect::<Vec<&(i32, u32)>>())
						.sorted(),
				)
			};
			match self {
				LinVariant::Linear(Linear { terms, cmp, k }) => {
					if let LinVariant::Linear(Linear {
						terms: oterms,
						cmp: oc,
						k: l,
					}) = other
					{
						cmp == oc && k == l && parteq(terms, oterms)
					} else {
						false
					}
				}
				LinVariant::Cardinality(Cardinality { lits, cmp, k }) => {
					if let LinVariant::Cardinality(Cardinality {
						lits: olits,
						cmp: oc,
						k: l,
					}) = other
					{
						cmp == oc && k == l && liteq(lits, olits)
					} else {
						false
					}
				}
				LinVariant::AtMostOne(amo) => {
					if let LinVariant::AtMostOne(oamo) = other {
						liteq(&amo.lits, &oamo.lits)
					} else {
						false
					}
				}
				LinVariant::Trivial => {
					if let LinVariant::Trivial = other {
						true
					} else {
						false
					}
				}
			}
		}
	}
}
