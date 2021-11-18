// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap, HashSet};

use crate::{
	ClauseSink, Coefficient, Comparator, Literal, PositiveCoefficient, Result, Unsatisfiable,
};

#[derive(Debug, PartialEq)]
pub enum BoolLin<PC: PositiveCoefficient, Lit: Literal> {
	LinEqual { terms: HashMap<Lit, PC>, k: PC },
	LinLessEq { terms: HashMap<Lit, PC>, k: PC },
	AtMostK { lits: HashSet<Lit>, k: PC },
	EqualK { lits: HashSet<Lit>, k: PC },
	AtMostOne { lits: HashSet<Lit> },
	Trivial,
}

impl<PC: PositiveCoefficient, Lit: Literal> BoolLin<PC, Lit> {
	pub fn aggregate<C: Coefficient + TryInto<PC>, DB: ClauseSink<Lit = Lit> + ?Sized>(
		db: &mut DB,
		coeff: &[C],
		vars: &[Lit],
		cmp: Comparator,
		k: C,
	) -> Result<BoolLin<PC, Lit>> {
		debug_assert_eq!(coeff.len(), vars.len());
		use BoolLin::*;
		use Comparator::*;

		// Convert ≤ to ≥ and aggregate multiple occurences of the same
		// variable.
		let mut agg = HashMap::with_capacity(coeff.len());
		for i in 0..coeff.len() {
			let var = if vars[i].is_negated() {
				vars[i].negate()
			} else {
				vars[i].clone()
			};
			let entry = agg.entry(var).or_insert_with(C::zero);
			let mut coef = coeff[i].clone();
			if vars[i].is_negated() ^ (cmp == GreaterEq) {
				coef *= -C::one()
			}
			*entry += coef;
		}
		let mut k = if cmp == GreaterEq { -k } else { k };
		let cmp = if cmp == GreaterEq { LessEq } else { cmp };
		debug_assert_ne!(cmp, GreaterEq);

		// Convert all negative coefficients
		let mut normalized = HashMap::with_capacity(agg.len());
		for (mut lit, mut coef) in agg {
			if coef == C::zero() {
				continue;
			}
			if coef.is_negative() {
				coef = -coef;
				lit = lit.negate();
				k += coef.clone();
			};
			let coef = match coef.try_into() {
				Ok(coef) => coef,
				Err(_) => panic!("Unable to convert coefficient to positive coeffient."),
			};
			normalized.insert(lit, coef);
		}

		// trivial case: constraint is unsatisfiable
		if k < C::zero() {
			return Err(Unsatisfiable);
		}
		// trivial case: no literals can be activated
		if k == C::zero() {
			for (lit, _) in normalized {
				db.add_clause(&[lit.negate()])?
			}
			return Ok(Trivial);
		}

		let mut k = match k.try_into() {
			Ok(k) => k,
			Err(_) => panic!("Unable to convert coefficient to positive coeffient."),
		};
		// Remove pairs with coef higher than k
		let (impossible, mut considered): (HashMap<Lit, PC>, _) =
			normalized.drain().partition(|(_, c)| c > &k);
		// Force literals that cannot be activated
		for (lit, _) in impossible {
			db.add_clause(&[lit.negate()])?
		}
		// Check whether considered literals can violate / satisfy the constraint
		let mut total = PC::zero();
		for (_, c) in &considered {
			total += c;
		}
		if cmp == Comparator::LessEq {
			if total <= k {
				return Ok(Trivial);
			} else if considered.len() == 2 {
				// Simple decision between 2 literals
				db.add_clause(&considered.drain().map(|(lit, _)| lit).collect::<Vec<Lit>>())?;
				return Ok(Trivial);
			}
		} else if cmp == Comparator::Equal {
			if total < k {
				return Err(Unsatisfiable);
			}
			if total == k {
				for (lit, _) in considered {
					db.add_clause(&[lit])?
				}
				return Ok(Trivial);
			}
		}
		debug_assert!(!considered.is_empty());

		// special case: all coefficients are equal (and can be made one)
		let val = considered.values().nth(0).unwrap();
		if considered.iter().all(|(_, c)| c == val) {
			// trivial case: k cannot be made from the coefficients
			if cmp == Equal && k % val != PC::zero() {
				return Err(Unsatisfiable);
			}

			k /= val;
			let considered = considered
				.drain()
				.map(|(lit, _)| lit)
				.collect::<HashSet<Lit>>();
			if k == PC::one() {
				// Encode At Least One constraint
				if cmp == Equal {
					db.add_clause(&considered.iter().map(|v| v.clone()).collect::<Vec<Lit>>())?
				}
				// Encode At Most One constraint
				return Ok(AtMostOne { lits: considered });
			}
			// Encode count constraint
			if cmp == Equal {
				return Ok(EqualK {
					lits: considered,
					k,
				});
			} else {
				return Ok(AtMostK {
					lits: considered,
					k,
				});
			}
		}

		// Default case: encode pseudo-Boolean linear constraint
		if cmp == Equal {
			return Ok(LinEqual {
				terms: considered,
				k,
			});
		} else {
			return Ok(LinLessEq {
				terms: considered,
				k,
			});
		}
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;
	use std::collections::HashSet;

	use crate::BoolLin;
	use crate::Comparator::*;
	use crate::Unsatisfiable;

	#[test]
	fn test_combine() {
		let mut ignore: Vec<Vec<i32>> = vec![];

		// Simple aggragation of multiple occurences of the same literal
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 2, 1, 2], &[1, 1, 2, 3], LessEq, 3),
			Ok(BoolLin::LinLessEq {
				terms: HashMap::from_iter([(1, 3), (2, 1), (3, 2)]),
				k: 3
			})
		);

		// Aggragation of positive and negative occurences of the same literal
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 2, 1, 2], &[1, -1, 2, 3], LessEq, 2),
			Ok(BoolLin::LinLessEq {
				terms: HashMap::from_iter([(-1, 1), (2, 1), (3, 2)]),
				k: 3
			})
		);

		// Aggragation of positive and negative coefficients of the same literal
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, -2, 1, 2], &[1, 1, 2, 3], LessEq, 2),
			Ok(BoolLin::LinLessEq {
				terms: HashMap::from_iter([(-1, 1), (2, 1), (3, 2)]),
				k: 3
			})
		);
	}

	#[test]
	fn test_detection() {
		let mut ignore: Vec<Vec<i32>> = vec![];

		// Correctly detect at most one
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 1, 1], &[1, 2, 3], LessEq, 1),
			Ok(BoolLin::AtMostOne {
				lits: HashSet::from_iter([1, 2, 3]),
			})
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[2, 2, 2], &[1, 2, 3], LessEq, 2),
			Ok(BoolLin::AtMostOne {
				lits: HashSet::from_iter([1, 2, 3]),
			})
		);

		// Correctly detect at most k
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 1, 1], &[1, 2, 3], LessEq, 2),
			Ok(BoolLin::AtMostK {
				lits: HashSet::from_iter([1, 2, 3]),
				k: 2,
			})
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[3, 3, 3], &[1, 2, 3], LessEq, 7),
			Ok(BoolLin::AtMostK {
				lits: HashSet::from_iter([1, 2, 3]),
				k: 2,
			})
		);

		// Correctly detect equal k
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 1, 1], &[1, 2, 3], Equal, 2),
			Ok(BoolLin::EqualK {
				lits: HashSet::from_iter([1, 2, 3]),
				k: 2,
			})
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[3, 3, 3], &[1, 2, 3], Equal, 6),
			Ok(BoolLin::EqualK {
				lits: HashSet::from_iter([1, 2, 3]),
				k: 2,
			})
		);

		// Is still normal Boolean linear in-equality
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 2, 2], &[1, 2, 3], LessEq, 2),
			Ok(BoolLin::LinLessEq {
				terms: HashMap::from_iter([(1, 1), (2, 2), (3, 2)]),
				k: 2,
			})
		);

		// Is still normal Boolean linear equality
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 2, 2], &[1, 2, 3], Equal, 2),
			Ok(BoolLin::LinEqual {
				terms: HashMap::from_iter([(1, 1), (2, 2), (3, 2)]),
				k: 2,
			})
		);
	}

	#[test]
	fn test_equal_one() {
		let mut db: Vec<Vec<i32>> = vec![];
		// An exactly one constraint adds an at most one constraint + a clause for all literals
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut db, &[1, 1, 1], &[1, 2, 3], Equal, 1),
			Ok(BoolLin::AtMostOne {
				lits: HashSet::from_iter([1, 2, 3]),
			})
		);
		// TODO: Fix checking with the order of clauses
		// assert_eq!(db, vec![vec![1, 2, 3]])
	}

	#[test]
	fn test_neg_coeff() {
		let mut ignore: Vec<Vec<i32>> = vec![];

		// Correctly convert a negative coefficient
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[2, 3, -2], &[1, 2, 3], LessEq, 2),
			Ok(BoolLin::LinLessEq {
				terms: HashMap::from_iter([(1, 2), (2, 3), (-3, 2)]),
				k: 4
			})
		);

		// Correctly convert multiple negative coefficients
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[-1, -1, -1], &[1, 2, 3], LessEq, -2),
			Ok(BoolLin::AtMostOne {
				lits: HashSet::from_iter([-1, -2, -3]),
			})
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[-1, -2, -3], &[1, 2, 3], LessEq, -2),
			Ok(BoolLin::LinLessEq {
				terms: HashMap::from_iter([(-1, 1), (-2, 2), (-3, 3)]),
				k: 4
			})
		);
	}

	#[test]
	fn test_unsat() {
		let mut ignore: Vec<Vec<i32>> = vec![];

		// Constant cannot be reached
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 2, 2], &[1, 2, 3], Equal, 6),
			Err(Unsatisfiable),
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 2, 2], &[1, 2, 3], GreaterEq, 6),
			Err(Unsatisfiable),
		);
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[1, 2, 2], &[1, 2, 3], LessEq, -1),
			Err(Unsatisfiable),
		);

		// Scaled counting constraint with off-scaled Constant
		assert_eq!(
			BoolLin::<u32, i32>::aggregate(&mut ignore, &[4, 4, 4], &[1, 2, 3], Equal, 6),
			Err(Unsatisfiable),
		);
	}
}
