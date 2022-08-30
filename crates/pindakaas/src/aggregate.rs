use std::collections::{HashMap, HashSet};

use crate::{
	ClauseDatabase, Coefficient, Comparator, Constraint, Literal, Part, PositiveCoefficient,
	Result, Unsatisfiable,
};

#[derive(Debug, PartialEq)]
pub enum BoolLin<PC: PositiveCoefficient, Lit: Literal> {
	LinEqual { terms: Vec<Part<Lit, PC>>, k: PC },
	LinLessEq { terms: Vec<Part<Lit, PC>>, k: PC },
	AtMostK { lits: HashSet<Lit>, k: PC },
	EqualK { lits: HashSet<Lit>, k: PC },
	AtMostOne { lits: HashSet<Lit> },
	Trivial,
}

impl<PC: PositiveCoefficient, Lit: Literal> BoolLin<PC, Lit> {
	pub fn aggregate<C: Coefficient + TryInto<PC>, DB: ClauseDatabase<Lit = Lit> + ?Sized>(
		db: &mut DB,
		coeff: &[C],
		lits: &[Lit],
		cmp: Comparator,
		k: C,
		cons: &[Constraint<Lit>],
	) -> Result<BoolLin<PC, Lit>> {
		debug_assert_eq!(coeff.len(), lits.len());
		use BoolLin::*;
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
		let mut k = if cmp == GreaterEq { -k } else { k };
		let cmp = if cmp == GreaterEq { LessEq } else { cmp };

		// partition terms according to side constraints
		let mut partition = cons
			.iter()
			.map(|con| match con {
				Constraint::Amo(lits) => Part::Amo(HashMap::from_iter(
					lits.iter()
						.map(|lit| (lit.clone(), agg.remove(lit).unwrap())),
				)),
				Constraint::Ic(lits) => Part::Ic(
					lits.iter()
						.map(|lit| (lit.clone(), agg.remove(lit).unwrap()))
						.collect(),
				),
			})
			.collect::<Vec<Part<Lit, C>>>();

		// add remaining (unconstrained) terms
		partition.append(
			&mut agg
				.into_iter()
				.map(|(lit, coef)| Part::Amo(HashMap::from_iter([(lit, coef)])))
				.collect(),
		);

		let partition :Vec<Part<Lit, PC>> = partition
			.into_iter()
			.map(|part| match part { // filter terms with coefficients of 0
				// TODO avoid this duplication?
				Part::Amo(terms) => Part::Amo(
					terms
						.into_iter()
						.filter(|(_, coef)| coef != &C::zero())
						.collect(),
				),
				Part::Ic(terms) => Part::Ic(
					terms
						.into_iter()
						.filter(|(_, coef)| coef != &C::zero())
						.collect(),
				),
			})
			.flat_map(|part| { // convert terms with negative coefficients
				match part {
                    Part::Amo(mut terms) => {
                        // TODO some ugly duplication to handle this, but since data structure will change this is ok for now
                        if terms.len() == 1 {
                            // TODO construct iterators rather than these fixed length vecs?
                            return vec![Part::Amo(
							terms
								.into_iter()
								.filter(|(_, coef)| coef != &C::zero())
								.map(|(mut lit, mut coef)| {
									if coef.is_negative() {
										coef = -coef;
										lit = lit.negate();
										k += coef;
									};
									match coef.try_into() {
										Ok(coef) => (lit, coef),
										Err(_) => {
											panic!("Unable to convert coefficient to positive coeffient.")
										}
									}
								}).collect()
                                )]
                        }

						// Find most negative coefficient
						let (min_lit, min_coef) = terms
							.iter()
							.min_by(|(_, a), (_, b)| a.cmp(b))
							.expect("Partition should not contain constraint on zero terms");

                        let (min_lit, min_coef) = (min_lit.clone(), *min_coef);

						// If negative, normalize without breaking AMO constraint
						if min_coef.is_negative() {
							let q = -min_coef;

							// this term will cancel out later when we add q*min_lit to the LHS
							terms.remove(&min_lit);

							// add aux var y and constrain y <-> ( ~x1 /\ ~x2 /\ ... )
							let y = db.new_var();
							db.add_clause(
								&terms
									.iter()
									.map(|(lit, _)| lit.negate())
									.collect::<Vec<Lit>>(),
							)
							.unwrap();
							for lit in terms.keys() {
								db.add_clause(&[y.negate(), lit.clone()]).unwrap();
							}

							// since y + x1 + x2 + ... = 1 (exactly-one), we have q*y + q*x1 + q*x2 + ... = q
							// after adding term 0*y, we can add q*y + q*x1 + q*x2 + ... on the LHS, and q on the RHS
							terms.insert(y, C::zero());  // note: it's fine to add y into the same AMO group
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
								.map(|(lit, coef)| {
									(
										lit,
										match coef.try_into()  {
                                            				Ok(coef) => coef,
                                            				Err(_) => panic!("Unable to convert coefficient to positive coefficient."),
                                        }
									)
								})
								.collect(),
						)]
					},
					Part::Ic(terms) => { // normalize by splitting up the chain into two chains by coef polarity, inverting the coefs of the neg 
                        let (pos_chain, neg_chain) : (_, Vec<(Lit,C)>) = terms.into_iter().partition(|(_,coef)| coef.is_positive());
                        vec![
                            Part::Ic( pos_chain.into_iter().map(|(lit,coef)| match coef.try_into() {
                                Ok(coef) => (lit, coef),
                                Err(_) => {
                                    panic!("Unable to convert coefficient to positive coefficient.")
                                }
                            }).collect()),
						Part::Ic(
							neg_chain
                            .into_iter()
								.map(|(mut lit, mut coef)| {
									if coef.is_negative() {
										coef = -coef;
										lit = lit.negate();
										k += coef;
									};
									match coef.try_into() {
										Ok(coef) => (lit, coef),
										Err(_) => {
											panic!("Unable to convert coefficient to positive coefficient.")
										}
									}
								})
                                .rev() // x1 <- x2 <- x3 <- ... becomes ~x1 -> ~x2 -> ~x3 -> ...
								.collect(),
						)]
					}
				}
			})
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
			return Ok(Trivial);
		}

		let mut k = match k.try_into() {
			Ok(k) => k,
			Err(_) => panic!("Unable to convert coefficient to positive coeffient."),
		};

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
			})
			.collect::<Vec<Part<Lit, PC>>>();

		// Check whether some literals can violate / satisfy the constraint
		let lhs_ub: PC = partition.iter().fold(PC::zero(), |acc, part| match part {
			Part::Amo(terms) => acc + *terms.values().max().unwrap_or(&PC::zero()),
			Part::Ic(terms) => acc + terms.iter().fold(PC::zero(), |acc, (_, coef)| acc + *coef),
		});

		if cmp == Comparator::LessEq {
			if lhs_ub <= k {
				return Ok(Trivial);
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
				return Ok(Trivial);
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
						Part::Ic(terms) => {
							for (lit, _) in terms {
								db.add_clause(&[lit.clone()])?;
							}
						}
					};
				}
				return Ok(Trivial);
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
				.collect::<HashSet<Lit>>();
			if k == PC::one() {
				// Encode At Least One constraint
				if cmp == Equal {
					db.add_clause(&partition.iter().cloned().collect::<Vec<Lit>>())?
				}
				// Encode At Most One constraint
				return Ok(AtMostOne { lits: partition });
			}
			// Encode count constraint
			if cmp == Equal {
				return Ok(EqualK { lits: partition, k });
			} else {
				return Ok(AtMostK { lits: partition, k });
			}
		}

		// Default case: encode pseudo-Boolean linear constraint
		if cmp == Equal {
			Ok(LinEqual {
				terms: partition,
				k,
			})
		} else {
			Ok(LinLessEq {
				terms: partition,
				k,
			})
		}
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;
	use std::collections::HashSet;

	use crate::BoolLin;
	use crate::ClauseDatabase;
	use crate::ClauseSink;
	use crate::Comparator::*;
	use crate::Constraint;
	use crate::Part;
	use crate::Result;
	use crate::Unsatisfiable;

	struct TestDB {
		nr: i32,
		db: Vec<Vec<i32>>,
	}

	impl ClauseSink for TestDB {
		type Lit = i32;

		fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
			self.db.add_clause(cl)
		}
	}

	impl ClauseDatabase for TestDB {
		fn new_var(&mut self) -> Self::Lit {
			self.nr += 1;
			self.nr
		}
	}

	fn construct_terms(terms: &[(i32, u32)]) -> Vec<Part<i32, u32>> {
		terms
			.iter()
			.map(|(lit, coef)| Part::Amo(HashMap::from_iter([(lit.clone(), coef.clone())])))
			.collect()
	}

	#[allow(dead_code)]
	// TODO fix sorting issue first #[test]
	fn test_combine() {
		let mut db = TestDB { nr: 0, db: vec![] };

		// Simple aggregation of multiple occurrences of the same literal
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 2, 1, 2], &[1, 1, 2, 3], LessEq, 3, &[]),
			Ok(BoolLin::LinLessEq {
				terms: construct_terms(&[(1, 3), (2, 1), (3, 2)]),
				k: 3
			})
		);

		// Aggregation of positive and negative occurrences of the same literal
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 2, 1, 2], &[1, -1, 2, 3], LessEq, 2, &[]),
			Ok(BoolLin::LinLessEq {
				terms: construct_terms(&[(-1, 1), (2, 1), (3, 2)]),
				k: 3
			})
		);

		// Aggregation of positive and negative coefficients of the same literal
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, -2, 1, 2], &[1, 1, 2, 3], LessEq, 2, &[]),
			Ok(BoolLin::LinLessEq {
				terms: construct_terms(&[(-1, 1), (2, 1), (3, 2)]),
				k: 3
			})
		);
	}

	#[allow(dead_code)]
	// TODO fix sorting issue first #[test]
	fn test_detection() {
		let mut db = TestDB { nr: 0, db: vec![] };

		// Correctly detect at most one
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 1, 1], &[1, 2, 3], LessEq, 1, &[]),
			Ok(BoolLin::AtMostOne {
				lits: HashSet::from_iter([1, 2, 3]),
			})
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[2, 2, 2], &[1, 2, 3], LessEq, 2, &[]),
			Ok(BoolLin::AtMostOne {
				lits: HashSet::from_iter([1, 2, 3]),
			})
		);

		// Correctly detect at most k
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 1, 1], &[1, 2, 3], LessEq, 2, &[]),
			Ok(BoolLin::AtMostK {
				lits: HashSet::from_iter([1, 2, 3]),
				k: 2,
			})
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[3, 3, 3], &[1, 2, 3], LessEq, 7, &[]),
			Ok(BoolLin::AtMostK {
				lits: HashSet::from_iter([1, 2, 3]),
				k: 2,
			})
		);

		// Correctly detect equal k
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 1, 1], &[1, 2, 3], Equal, 2, &[]),
			Ok(BoolLin::EqualK {
				lits: HashSet::from_iter([1, 2, 3]),
				k: 2,
			})
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[3, 3, 3], &[1, 2, 3], Equal, 6, &[]),
			Ok(BoolLin::EqualK {
				lits: HashSet::from_iter([1, 2, 3]),
				k: 2,
			})
		);

		// Is still normal Boolean linear in-equality
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 2, 2], &[1, 2, 3], LessEq, 2, &[]),
			Ok(BoolLin::LinLessEq {
				terms: construct_terms(&[(1, 1), (2, 2), (3, 2)]),
				k: 2,
			})
		);

		// Is still normal Boolean linear equality
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 2, 2], &[1, 2, 3], Equal, 2, &[]),
			Ok(BoolLin::LinEqual {
				terms: construct_terms(&[(1, 1), (2, 2), (3, 2)]),
				k: 2,
			})
		);

		// Correctly identify that the Amo is limiting the LHS ub
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(
				&mut db,
				&[-1, -1, -1],
				&[1, 2, 3],
				LessEq,
				-2,
				&[Constraint::Amo(HashSet::from([1, 2]))]
			),
			Ok(BoolLin::Trivial)
		);
	}

	#[test]
	fn test_equal_one() {
		let mut db = TestDB { nr: 0, db: vec![] };
		// An exactly one constraint adds an at most one constraint + a clause for all literals
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 1, 1], &[1, 2, 3], Equal, 1, &[]),
			Ok(BoolLin::AtMostOne {
				lits: HashSet::from_iter([1, 2, 3]),
			})
		);
		// TODO: Fix checking with the order of clauses
		// assert_eq!(db, vec![vec![1, 2, 3]])
	}

	#[allow(dead_code)]
	// TODO fix sorting issue first #[test]
	fn test_neg_coeff() {
		let mut db = TestDB { nr: 0, db: vec![] };

		// Correctly convert a negative coefficient
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[2, 3, -2], &[1, 2, 3], LessEq, 2, &[]),
			Ok(BoolLin::LinLessEq {
				terms: construct_terms(&[(1, 2), (2, 3), (-3, 2)]),
				k: 4
			})
		);

		// Correctly convert multiple negative coefficients
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[-1, -1, -1], &[1, 2, 3], LessEq, -2, &[]),
			Ok(BoolLin::AtMostOne {
				lits: HashSet::from_iter([-1, -2, -3]),
			})
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[-1, -2, -3], &[1, 2, 3], LessEq, -2, &[]),
			Ok(BoolLin::LinLessEq {
				terms: construct_terms(&[(-1, 1), (-2, 2), (-3, 3)]),
				k: 4
			})
		);

		// Correctly convert multiple negative coefficients with AMO constraints
		let mut db = TestDB { nr: 6, db: vec![] };
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(
				&mut db,
				&[-1, -3, -4, -2, -3, -5],
				&[1, 2, 3, 4, 5, 6],
				LessEq,
				-4,
				&[
					Constraint::Amo(HashSet::from([1, 2, 3])),
					Constraint::Amo(HashSet::from([4, 5, 6]))
				]
			),
			Ok(BoolLin::LinLessEq {
				terms: vec![
					Part::Amo(HashMap::from_iter([(1, 3), (2, 1), (7, 4)])),
					Part::Amo(HashMap::from_iter([(4, 3), (5, 2), (8, 5)])),
				],
				k: 5
			})
		);

		// Correctly convert multiple negative coefficients with IC constraints
		let mut db = TestDB { nr: 6, db: vec![] };
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(
				&mut db,
				&[1, -3, -2, 2, 5, -3],
				&[1, 2, 3, 4, 5, 6],
				LessEq,
				3,
				&[Constraint::Ic(vec![1, 2, 3, 4, 5, 6])]
			),
			Ok(BoolLin::LinLessEq {
				terms: vec![
					Part::Ic(vec![(1, 1), (4, 2), (5, 5)]),
					Part::Ic(vec![(-6, 3), (-3, 2), (-2, 3)]),
				],
				k: 11
			})
		);
	}

	#[test]
	fn test_unsat() {
		let mut db = TestDB { nr: 0, db: vec![] };

		// Constant cannot be reached
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 2, 2], &[1, 2, 3], Equal, 6, &[]),
			Err(Unsatisfiable),
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 2, 2], &[1, 2, 3], GreaterEq, 6, &[]),
			Err(Unsatisfiable),
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 2, 2], &[1, 2, 3], LessEq, -1, &[]),
			Err(Unsatisfiable),
		);

		// Scaled counting constraint with off-scaled Constant
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[4, 4, 4], &[1, 2, 3], Equal, 6, &[]),
			Err(Unsatisfiable),
		);
	}
}
