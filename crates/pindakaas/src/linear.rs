use std::collections::HashMap;

use crate::{
	AtMostOne, Cardinality, CheckError, Checker, ClauseDatabase, Coefficient, Encoder, Literal,
	PairwiseEncoder, PositiveCoefficient, Result, Unsatisfiable,
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

pub type LinearEncoder<'a, Lit, C, PC> = ArbLinEncoder<'a, Lit, C, PC>;

// TODO how can we support both Part(itions) of "terms" ( <Lit, C> for pb
// constraints) and just lits (<Lit>) for AMK/AMO's?
//
// TODO add EO, and probably something for Unconstrained
#[derive(Debug)]
pub(crate) enum Part<Lit, C> {
	Amo(Vec<(Lit, C)>),
	Ic(Vec<(Lit, C)>),
	Dom(Vec<(Lit, C)>, C, C),
}

impl<Lit, C> Part<Lit, C> {
	fn iter(&self) -> std::slice::Iter<(Lit, C)> {
		match self {
			Part::Amo(terms) => terms.iter(),
			Part::Ic(terms) => terms.iter(),
			Part::Dom(terms, _, _) => terms.iter(),
		}
	}
}

// TODO just temporary until I find out how to use IntEncodings for this
#[derive(Debug, Clone)]
pub enum Constraint<Lit, C> {
	Amo(Vec<Lit>),
	Ic(Vec<Lit>),
	Dom(Vec<Lit>, C, C),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Comparator {
	LessEq,
	Equal,
	GreaterEq,
}
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum LimitComp {
	Equal,
	LessEq,
}

impl<PC: PositiveCoefficient, Lit: Literal> LinVariant<Lit, PC> {
	pub fn aggregate<C: Coefficient + TryInto<PC>, DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		coeff: &[C],
		lits: &[Lit],
		cmp: Comparator,
		k: C,
		cons: &[Constraint<Lit, C>],
	) -> Result<LinVariant<Lit, PC>> {
		debug_assert_eq!(coeff.len(), lits.len());
		use Comparator::*;

		// Convert ≤ to ≥ and aggregate multiple occurrences of the same
		// variable.
		// TODO not accounting for IC/AMO groups yet
		let mut agg = HashMap::with_capacity(coeff.len());
		for i in 0..coeff.len() {
			let var = if lits[i].is_negated() {
				lits[i].negate()
			} else {
				lits[i].clone()
			};
			let entry = agg.entry(var).or_insert_with(C::zero);
			let mut coef = coeff[i];
			if lits[i].is_negated() ^ (cmp == GreaterEq) {
				coef *= -C::one()
			}
			*entry += coef;
		}

		// partition terms according to side constraints
		let mut partition = cons
			.iter()
			.map(|con| match con {
				Constraint::Amo(lits) => Part::Amo(
					lits.iter()
						.map(|lit| {
							(
								lit.clone(),
								agg.remove(lit).unwrap_or_else(|| {
									panic!("Lit {:?} was in side constraint but not in PB", lit)
								}),
							)
						})
						.collect(),
				),
				Constraint::Ic(lits) => Part::Ic(
					lits.iter()
						.map(|lit| {
							(
								lit.clone(),
								agg.remove(lit).unwrap_or_else(|| {
									panic!("Lit {:?} was in side constraint but not in PB", lit)
								}),
							)
						})
						.collect(),
				),
				Constraint::Dom(lits, l, u) => {
					let terms: Vec<(Lit, C)> = lits
						.iter()
						.map(|lit| {
							(
								lit.clone(),
								agg.remove(lit).unwrap_or_else(|| {
									panic!("Lit {:?} was in side constraint but not in PB", lit)
								}),
							)
						})
						.collect();

					// this constraints assumes PB is coef*(1x1 + 2x2 + 4x3 + ...), where l <= 1x1 + 2x2 + 4x3 + ... <= u
					// in other words, l and u do not take into account the coefficient yet.
					let (l, u) = if cmp == GreaterEq {
						// 0..range can be encoded by the bits multiplied by coef
						let range = -terms.iter().fold(C::zero(), |acc, (_, coef)| acc + *coef);
						// this range is inverted if we have flipped the comparator
						(range - *u, range - *l)
					} else {
						// in both cases, l and u now represent the true constraint
						(terms[0].1 * *l, terms[0].1 * *u)
					};
					// debug_assert!(
					// 	cmp != LessEq
					// 		|| k <= terms.iter().fold(C::zero(), |acc, (_, coef)| acc + *coef),
					// 	"The Dom constraint is trivial for {k:?} and {terms:?}"
					// );
					Part::Dom(terms, l, u)
				}
			})
			.collect::<Vec<Part<Lit, C>>>();

		let mut k = if cmp == GreaterEq { -k } else { k };
		let cmp = if cmp == GreaterEq { LessEq } else { cmp };

		// add remaining (unconstrained) terms
		partition.append(
			&mut agg
				.into_iter()
				.map(|(lit, coef)| Part::Amo(vec![(lit, coef)]))
				.collect(),
		);

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
				Part::Dom(terms, l, u) => Part::Dom(terms, l, u),
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

		if cmp == Comparator::LessEq {
			if lhs_ub <= k {
				return Ok(LinVariant::Trivial);
			}

			// If we have only 2 (unassigned) lits, which together exceed k, then -x1\/-x2
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
		} else if cmp == Comparator::Equal {
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
			if cmp == Equal && k % *val != PC::zero() {
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
				if cmp == Equal {
					db.add_clause(&partition.to_vec())?
				}
				// Encode At Most One constraint
				return Ok(LinVariant::AtMostOne(AtMostOne { lits: partition }));
			}
			// Encode count constraint
			return Ok(LinVariant::Cardinality(Cardinality {
				lits: partition,
				cmp: if cmp == Equal {
					LimitComp::Equal
				} else {
					LimitComp::LessEq
				},
				k,
			}));
		}

		// Default case: encode pseudo-Boolean linear constraint
		Ok(LinVariant::Linear(Linear {
			terms: partition,
			cmp: if cmp == Equal {
				LimitComp::Equal
			} else {
				LimitComp::LessEq
			},
			k,
		}))
	}
}

macro_rules! linear_encoder {
	($name:ident, $encode_variant:item) => {
		#[derive(Debug)]
		pub struct $name<
			'a,
			Lit: $crate::Literal,
			C: $crate::Coefficient + ::std::convert::TryInto<PC>,
			PC: $crate::PositiveCoefficient,
		> {
			coeff: &'a [C],
			lits: &'a [Lit],
			cmp: Comparator,
			k: C,
			cons: &'a [Constraint<Lit, C>],
			into: ::std::marker::PhantomData<PC>,
		}

		impl<
				'a,
				Lit: $crate::Literal,
				C: $crate::Coefficient + ::std::convert::TryInto<PC>,
				PC: $crate::PositiveCoefficient,
			> $name<'a, Lit, C, PC>
		{
			pub fn new(
				coeff: &'a [C],
				lits: &'a [Lit],
				cmp: Comparator,
				k: C,
				cons: &'a [Constraint<Lit, C>],
			) -> Self {
				Self {
					coeff,
					lits,
					cmp,
					k,
					cons,
					into: ::std::marker::PhantomData,
				}
			}

			$encode_variant
		}

		impl<
				'a,
				Lit: $crate::Literal,
				C: $crate::Coefficient + ::std::convert::TryInto<PC>,
				PC: $crate::PositiveCoefficient,
			> $crate::Encoder for $name<'a, Lit, C, PC>
		{
			type Lit = Lit;
			type Ret = ();

			fn encode<DB: $crate::ClauseDatabase<Lit = Lit>>(
				&mut self,
				db: &mut DB,
			) -> $crate::Result {
				let lin_var = LinVariant::aggregate(
					db,
					self.coeff,
					self.lits,
					self.cmp.clone(),
					self.k,
					self.cons,
				)?;
				self.encode_variant(db, lin_var)
			}
		}
	};
}
pub(crate) use linear_encoder;

// This is just a linear encoder that currently makes an arbitrary choice.
// This is probably not how we would like to do it in the future.
linear_encoder!(
	ArbLinEncoder,
	fn encode_variant<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		lin_var: LinVariant<Lit, PC>,
	) -> Result {
		match lin_var {
			LinVariant::Linear(lin) => AdderEncoder::new(&lin).encode(db),
			LinVariant::Cardinality(_) => unimplemented!(),
			LinVariant::AtMostOne(amo) => PairwiseEncoder::new(&amo).encode(db),
			LinVariant::Trivial => Ok(()),
		}
	}
);

#[cfg(debug_assertions)]
#[macro_export]
macro_rules! new_var {
	($db:expr) => {
		$db.new_var()
	};
	($db:expr, $lbl:expr) => {
		$db.new_var_with_label($lbl)
	};
}

#[cfg(not(debug_assertions))]
#[macro_export]
macro_rules! new_var {
	($db:expr) => {
		$db.new_var()
	};
	($db:expr, $lbl:expr) => {
		$db.new_var_with_label($lbl)
	};
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
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 2, 1, 2],
				&[1, 1, 2, 3],
				Comparator::LessEq,
				3,
				&[]
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 3), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 3
			}))
		);

		// Aggregation of positive and negative occurrences of the same literal
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 2, 1, 2],
				&[1, -1, 2, 3],
				Comparator::LessEq,
				2,
				&[]
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(-1, 1), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 3
			}))
		);

		// Aggregation of positive and negative coefficients of the same literal
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, -2, 1, 2],
				&[1, 1, 2, 3],
				Comparator::LessEq,
				2,
				&[]
			),
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
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 1, 1],
				&[1, 2, 3],
				Comparator::LessEq,
				1,
				&[]
			),
			Ok(LinVariant::AtMostOne(AtMostOne {
				lits: vec![1, 2, 3],
			}))
		);
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[2, 2, 2],
				&[1, 2, 3],
				Comparator::LessEq,
				2,
				&[]
			),
			Ok(LinVariant::AtMostOne(AtMostOne {
				lits: vec![1, 2, 3],
			}))
		);

		// Correctly detect at most k
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 1, 1],
				&[1, 2, 3],
				Comparator::LessEq,
				2,
				&[]
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3],
				cmp: LimitComp::LessEq,
				k: 2,
			}))
		);
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[3, 3, 3],
				&[1, 2, 3],
				Comparator::LessEq,
				7,
				&[]
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3],
				cmp: LimitComp::LessEq,
				k: 2,
			}))
		);

		// Correctly detect equal k
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 1, 1],
				&[1, 2, 3],
				Comparator::Equal,
				2,
				&[]
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3],
				cmp: LimitComp::Equal,
				k: 2,
			}))
		);
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[3, 3, 3],
				&[1, 2, 3],
				Comparator::Equal,
				6,
				&[]
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3],
				cmp: LimitComp::Equal,
				k: 2,
			}))
		);

		// Is still normal Boolean linear in-equality
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 2, 2],
				&[1, 2, 3],
				Comparator::LessEq,
				2,
				&[]
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 1), (2, 2), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 2,
			}))
		);

		// Is still normal Boolean linear equality
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 2, 2],
				&[1, 2, 3],
				Comparator::Equal,
				2,
				&[]
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 1), (2, 2), (3, 2)]),
				cmp: LimitComp::Equal,
				k: 2,
			}))
		);

		// Correctly identify that the AMO is limiting the LHS ub
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[-1, -1, -1],
				&[1, 2, 3],
				Comparator::LessEq,
				-2,
				&[Constraint::Amo(vec![1, 2])]
			),
			Ok(LinVariant::Trivial)
		);
	}

	#[test]
	fn test_equal_one() {
		let mut db = TestDB::new(3).expect_clauses(vec![vec![1, 2, 3]]);
		// An exactly one constraint adds an at most one constraint + a clause for all literals
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 1, 1],
				&[1, 2, 3],
				Comparator::Equal,
				1,
				&[]
			),
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
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[2, 3, -2],
				&[1, 2, 3],
				Comparator::LessEq,
				2,
				&[]
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 2), (2, 3), (-3, 2)]),
				cmp: LimitComp::LessEq,
				k: 4
			}))
		);

		// Correctly convert multiple negative coefficients
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[-1, -1, -1],
				&[1, 2, 3],
				Comparator::LessEq,
				-2,
				&[]
			),
			Ok(LinVariant::AtMostOne(AtMostOne {
				lits: vec![-1, -2, -3],
			}))
		);
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[-1, -2, -3],
				&[1, 2, 3],
				Comparator::LessEq,
				-2,
				&[]
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(-1, 1), (-2, 2), (-3, 3)]),
				cmp: LimitComp::LessEq,
				k: 4
			}))
		);

		// Correctly convert multiple negative coefficients with AMO constraints
		let mut db = TestDB::new(6);
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[-1, -3, -4, -2, -3, -5],
				&[1, 2, 3, 4, 5, 6],
				Comparator::LessEq,
				-4,
				&[
					Constraint::Amo(vec![1, 2, 3]),
					Constraint::Amo(vec![4, 5, 6])
				]
			),
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
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, -3, -2, 2, 5, -3],
				&[1, 2, 3, 4, 5, 6],
				Comparator::LessEq,
				3,
				&[Constraint::Ic(vec![1, 2, 3, 4, 5, 6])]
			),
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
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 2, 3, 4, 1, 3],
				&[1, 2, 3, 4, 5, 6],
				Comparator::GreaterEq,
				3,
				&[
					Constraint::Amo(vec![1, 2, 3, 4]),
					Constraint::Amo(vec![5, 6])
				]
			),
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
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 1, 1, 1, 1, 2],
				&[1, 2, 3, 4, 5, 6],
				Comparator::GreaterEq,
				3,
				&[Constraint::Ic(vec![1, 2, 3, 4]), Constraint::Ic(vec![5, 6])]
			),
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
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 2, 4, 3, 6],
				&[1, 2, 3, 4, 5],
				Comparator::GreaterEq,
				3,
				&[
					Constraint::Dom(vec![1, 2, 3], 0, 5),
					Constraint::Dom(vec![4, 5], 0, 2)
				]
			),
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
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 2, 2],
				&[1, 2, 3],
				Comparator::Equal,
				6,
				&[]
			),
			Err(Unsatisfiable),
		);
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 2, 2],
				&[1, 2, 3],
				Comparator::GreaterEq,
				6,
				&[]
			),
			Err(Unsatisfiable),
		);
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[1, 2, 2],
				&[1, 2, 3],
				Comparator::LessEq,
				-1,
				&[]
			),
			Err(Unsatisfiable),
		);

		// Scaled counting constraint with off-scaled Constant
		assert_eq!(
			LinVariant::<i32, u32>::aggregate(
				&mut db,
				&[4, 4, 4],
				&[1, 2, 3],
				Comparator::Equal,
				6,
				&[]
			),
			Err(Unsatisfiable),
		);
	}

	#[test]
	fn test_pb_encode() {
		assert_enc_sol!(
			ArbLinEncoder::<i32,i32,u32>,
			4,
			&[1, 1, 1, 2],
			&[1, 2, 3, 4],
			crate::Comparator::LessEq,
			1,
			&[]
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
		assert!(ArbLinEncoder::<i32, i32, u32>::new(
			&[7, 10, 4, 4],
			&[1, 2, 3, 4],
			crate::Comparator::LessEq,
			9,
			&[Constraint::Amo(vec![1, 2]), Constraint::Amo(vec![3, 4])],
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
