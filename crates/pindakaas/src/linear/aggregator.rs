use rustc_hash::FxHashMap;
use std::hash::BuildHasherDefault;

use crate::{
	helpers::is_powers_of_two,
	linear::{Constraint, LimitComp, Part, PosCoeff},
	sorted::{Sorted, SortedEncoder},
	trace::{emit_clause, new_var},
	Cardinality, CardinalityOne, ClauseDatabase, Coefficient, Comparator, Encoder, LinVariant,
	Linear, LinearConstraint, Literal, Result, Unsatisfiable,
};
use itertools::Itertools;

#[derive(Default)]
pub struct LinearAggregator {
	sort_same_coefficients: usize,
	add_sorted_consistency: bool, // TODO should we pass a whole Encoder<Sorted..>?
}

impl LinearAggregator {
	/// For non-zero `n`, detect groups of minimum size `n` with free literals and same coefficients, sort them and add them as implication chain group
	pub fn sort_same_coefficients(&mut self, n: usize) -> &mut Self {
		self.sort_same_coefficients = n;
		self
	}

	/// When sorting same coefficients, also impose consistency on resulting auxiliary variables
	pub fn add_sorted_consistency(&mut self, b: bool) -> &mut Self {
		self.add_sorted_consistency = b;
		self
	}

	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "aggregator", skip_all, fields(constraint = lin.trace_print()))
	)]
	pub fn aggregate<DB: ClauseDatabase, C: Coefficient>(
		&mut self,
		db: &mut DB,
		lin: &LinearConstraint<DB::Lit, C>,
	) -> Result<LinVariant<DB::Lit, C>> {
		// Convert ≤ to ≥ and aggregate multiple occurrences of the same
		// variable.
		let mut agg =
			FxHashMap::with_capacity_and_hasher(lin.exp.terms.len(), BuildHasherDefault::default());
		for term in &lin.exp.terms {
			let var = term.0.var();
			let entry = agg.entry(var).or_insert_with(C::zero);
			let mut coef = term.1 * lin.exp.mult;
			if term.0.is_negated() ^ (lin.cmp == Comparator::GreaterEq) {
				coef *= -C::one()
			}
			*entry += coef;
		}

		let mut partition = Vec::with_capacity(lin.exp.constraints.len());
		// Adjust side constraints when literals are combined (and currently transform to partition structure)
		let mut iter = lin.exp.terms.iter().skip(lin.exp.num_free);
		for con in &lin.exp.constraints {
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
						// Domain constraint can only be enforced when PB is coef*(x1 + 2x2 + 4x3 + ...), where l <= x1 + 2*x2 + 4*x3 + ... <= u
						if terms.len() == con.1
							&& is_powers_of_two(
								terms.iter().map(|(_, c)| *c).collect::<Vec<_>>().as_slice(),
							) {
							// Adjust the bounds to account for coef
							let (lb, ub) = if lin.cmp == Comparator::GreaterEq {
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
		debug_assert!(agg.len() <= lin.exp.num_free);
		for term in agg.drain() {
			partition.push(Part::Amo(vec![term]));
		}

		let mut k = if lin.cmp == Comparator::GreaterEq {
			-lin.k
		} else {
			lin.k
		} - lin.exp.add;
		let cmp = match lin.cmp {
			Comparator::LessEq | Comparator::GreaterEq => LimitComp::LessEq,
			Comparator::Equal => LimitComp::Equal,
		};

		let convert_term_if_negative = |term: (DB::Lit, C), k: &mut C| -> (DB::Lit, PosCoeff<C>) {
			let (mut lit, mut coef) = term;
			if coef.is_negative() {
				coef = -coef;
				lit = lit.negate();
				*k += coef;
			};
			(lit, coef.into())
		};

		let partition: Vec<Part<DB::Lit, PosCoeff<C>>> = partition
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

							// add aux var y and constrain y <-> ( ~x1 /\ ~x2 /\ .. )
							let y = db.new_var();

                            // ~x1 /\ ~x2 /\ .. -> y == x1 \/ x2 \/ .. \/ y
							emit_clause!(
								db,
								&terms
									.iter()
									.map(|(lit, _)| lit.clone())
									.chain(std::iter::once(y.clone()))
									.collect::<Vec<DB::Lit>>()
							)
							.unwrap();

                            // y -> ( ~x1 /\ ~x2 /\ .. ) == ~y \/ ~x1, ~y \/ ~x2, ..
							for lit in terms.iter().map(|tup| tup.0.clone()) {
								emit_clause!(db, &[y.negate(), lit.negate()]).unwrap();
							}

							// this term will cancel out later when we add q*min_lit to the LHS
							terms.remove(min_index);

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
								.map(|(lit, coef)| (lit, coef.into()))
								.collect(),
						)]
					}
					Part::Ic(terms) => {
						// normalize by splitting up the chain into two chains by coef polarity, inverting the coefs of the neg
						let (pos_chain, neg_chain): (_, Vec<(DB::Lit, C)>) =
							terms.into_iter().partition(|(_, coef)| coef.is_positive());
						vec![
							Part::Ic(
								pos_chain
									.into_iter()
									.map(|(lit, coef)| (lit, coef.into()))
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
							l.into(),
							u.into(),
						)]
					}
				}
			})
			.map(|part| {
				// This step has to come *after* Amo normalization
				let filter_zero_coefficients = |terms: Vec<(DB::Lit, PosCoeff<C>)>| -> Vec<(DB::Lit, PosCoeff<C>)> {
					terms
						.into_iter()
						.filter(|(_, coef)| **coef != C::zero())
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
					emit_clause!(db, &[lit.negate()])?
				}
			}
			return Ok(LinVariant::Trivial);
		}

		let mut k = k.into();

		// Remove terms with coefs higher than k
		let partition = partition
			.into_iter()
			.map(|part| match part {
				Part::Amo(terms) => Part::Amo(
					terms
						.into_iter()
						.filter(|(lit, coef)| {
							if coef > &k {
								emit_clause!(db, &[lit.negate()]).unwrap();
								false
							} else {
								true
							}
						})
						.collect(),
				),
				Part::Ic(terms) => {
					// for IC, we can compare the running sum to k
					let mut acc = C::zero();
					Part::Ic(
						terms
							.into_iter()
							.filter(|(lit, coef)| {
								acc += **coef;
								if acc > *k {
									emit_clause!(db, &[lit.negate()]).unwrap();
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
								emit_clause!(db, &[lit.negate()]).unwrap();
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
							.fold(C::zero(), |a, b| a + **b)
							.into(),
					);
					Part::Dom(terms, l, u)
				}
			})
			.filter(|part| part.iter().next().is_some()) // filter out empty groups
			.collect::<Vec<Part<DB::Lit, PosCoeff<C>>>>();

		// Check whether some literals can violate / satisfy the constraint
		let lhs_ub: PosCoeff<C> = partition
			.iter()
			.fold(C::zero(), |acc, part| match part {
				Part::Amo(terms) => {
					acc + terms.iter().map(|tup| *tup.1).max().unwrap_or_else(C::zero)
				}
				Part::Ic(terms) | Part::Dom(terms, _, _) => {
					acc + terms.iter().fold(C::zero(), |acc, (_, coef)| acc + **coef)
					// TODO max(k, acc + ..)
				}
			})
			.into();

		match cmp {
			LimitComp::LessEq => {
				if lhs_ub <= k {
					return Ok(LinVariant::Trivial);
				}

				// If we have only 2 (unassigned) lits, which together (but not individually) exceed k, then -x1\/-x2
				if partition.iter().flat_map(|part| part.iter()).count() == 2 {
					emit_clause!(
						db,
						&partition
							.iter()
							.flat_map(|part| part.iter())
							.map(|(lit, _)| lit.negate())
							.collect::<Vec<DB::Lit>>()
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
								emit_clause!(
									db,
									&[terms
										.iter()
										.max_by(|(_, a), (_, b)| a.cmp(b))
										.unwrap()
										.0
										.clone()]
								)?;
							}
							Part::Ic(terms) | Part::Dom(terms, _, _) => {
								for (lit, _) in terms {
									emit_clause!(db, &[lit.clone()])?;
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
			if cmp == LimitComp::Equal && *k % **val != C::zero() {
				return Err(Unsatisfiable);
			}

			*k /= **val;
			let partition = partition
				.iter()
				.flat_map(|part| part.iter())
				.map(|(lit, _)| lit.clone())
				.collect::<Vec<DB::Lit>>();
			if *k == C::one() {
				// Cardinality One constraint
				return Ok(LinVariant::CardinalityOne(CardinalityOne {
					lits: partition,
					cmp,
				}));
			}

			// At most n-1 out of n is equivalent to at least *not* one
			// Ex. at most 2 out of 3 true = at least 1 out of 3 false
			if (0..partition.len()).fold(C::zero(), |acc, _| acc + C::one()) == *k + C::one() {
				let neg = partition.iter().map(|l| l.negate()).collect::<Vec<_>>();
				emit_clause!(db, &neg)?;

				if cmp == LimitComp::LessEq {
					return Ok(LinVariant::Trivial);
				} else {
					// we still need to constrain x1 + x2 .. >= n-1
					//   == (1 - ~x1) + (1 - ~x2) + .. >= n-1
					//   == - ~x1 - ~x2 - .. <= n-1-n ( == .. <= -1)
					//   == ~x1 + ~x2 + .. <= 1
					return Ok(LinVariant::CardinalityOne(CardinalityOne {
						lits: neg,
						cmp: LimitComp::LessEq,
					}));
				}
			}

			// Encode count constraint
			return Ok(LinVariant::Cardinality(Cardinality {
				lits: partition,
				cmp,
				k,
			}));
		}

		// Do not interfere with a cardinality constraint
		let n = partition.len();
		let (free_lits, mut partition): (Vec<_>, Vec<_>) = partition.into_iter().partition(
			|part| matches!(part, Part::Amo(x) | Part::Ic(x) | Part::Dom(x, _, _) if x.len() == 1),
		);

		for (coef, group) in &free_lits
			.into_iter()
			.map(|part| match part {
				Part::Amo(x) | Part::Ic(x) | Part::Dom(x, _, _) if x.len() == 1 => x[0].clone(),
				_ => unreachable!(),
			})
			.sorted_by(|(_, a), (_, b)| a.cmp(b))
			.group_by(|x| x.1.clone())
		{
			let xs = group.map(|x| x.0).collect::<Vec<_>>();

			if self.sort_same_coefficients >= 2
				&& xs.len() >= self.sort_same_coefficients
				&& xs.len() < n
			{
				let c = (*k / *coef).to_usize().unwrap();

				let ys = xs
					.iter()
					.take(c)
					.map(|_x| new_var!(db, format!("s_{_x:?}"))) // TODO: Use label of _x
					.collect::<Vec<_>>();
				SortedEncoder::default()
					.add_consistency(self.add_sorted_consistency)
					.encode(db, &Sorted::new(&xs, LimitComp::LessEq, &ys))
					.unwrap();
				partition.push(Part::Ic(
					ys.into_iter().map(|y| (y, coef.clone())).collect(),
				));
			} else {
				for x in xs {
					partition.push(Part::Amo(vec![(x, coef.clone())]));
				}
			}
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
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{helpers::tests::TestDB, linear::tests::construct_terms, LinExp};

	#[test]
	fn test_combine() {
		let mut db = TestDB::new(3).expect_clauses(vec![]);
		// Simple aggregation of multiple occurrences of the same literal
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (1, 2) + (2, 1) + (3, 2),
					Comparator::LessEq,
					3
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 3), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 3.into()
			}))
		);

		// Aggregation of positive and negative occurrences of the same literal
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (-1, 2) + (2, 1) + (3, 2),
					Comparator::LessEq,
					2
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(-1, 1), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 3.into()
			}))
		);

		// Aggregation of positive and negative coefficients of the same literal
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (1, -2) + (2, 1) + (3, 2),
					Comparator::LessEq,
					2,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(-1, 1), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 3.into()
			}))
		);
		db.check_complete()
	}

	#[test]
	fn test_detection() {
		let mut db = TestDB::new(3);

		// Correctly detect at most one
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 1) + (3, 1),
					Comparator::LessEq,
					1
				)
			),
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vec![1, 2, 3],
				cmp: LimitComp::LessEq
			}))
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 2)) + (2, 2) + (3, 2),
					Comparator::LessEq,
					2
				)
			),
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vec![1, 2, 3],
				cmp: LimitComp::LessEq
			}))
		);

		// Correctly detect at most k
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 1) + (3, 1) + (4, 1),
					Comparator::LessEq,
					2
				)
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3, 4],
				cmp: LimitComp::LessEq,
				k: 2.into(),
			}))
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 3)) + (2, 3) + (3, 3) + (4, 3),
					Comparator::LessEq,
					7
				)
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3, 4],
				cmp: LimitComp::LessEq,
				k: 2.into(),
			}))
		);

		// Correctly detect equal k
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 1) + (3, 1) + (4, 1),
					Comparator::Equal,
					2
				)
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3, 4],
				cmp: LimitComp::Equal,
				k: 2.into(),
			}))
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 3)) + (2, 3) + (3, 3) + (4, 3),
					Comparator::Equal,
					6
				)
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![1, 2, 3, 4],
				cmp: LimitComp::Equal,
				k: 2.into(),
			}))
		);

		// Is still normal Boolean linear in-equality
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 2) + (3, 2),
					Comparator::LessEq,
					2
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 1), (2, 2), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: 2.into(),
			}))
		);

		// Is still normal Boolean linear equality
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 2) + (3, 2),
					Comparator::Equal,
					2
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 1), (2, 2), (3, 2)]),
				cmp: LimitComp::Equal,
				k: 2.into(),
			}))
		);

		// Correctly identify that the AMO is limiting the LHS ub
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((3, -1)).add_choice(&[(1, -1), (2, -1)]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(LinVariant::Trivial)
		);
	}

	#[test]
	fn test_sort_same_coefficients() {
		let mut db = TestDB::new(4);
		assert_eq!(
			LinearAggregator::default()
				.sort_same_coefficients(2)
				.aggregate(
					&mut db,
					&LinearConstraint::new(
						LinExp::from((1, 3)) + (2, 3) + (4, 5) + (3, 3),
						Comparator::LessEq,
						10
					)
				),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Ic(vec![(5, 3.into()), (6, 3.into()), (7, 3.into())]),
					Part::Amo(vec![(4, 5.into())]),
				],
				cmp: LimitComp::LessEq,
				k: 10.into(),
			}))
		);
		db.check_complete()
	}

	#[test]
	fn test_sort_same_coefficients_using_minimal_chain() {
		let mut db = TestDB::new(5);
		assert_eq!(
			LinearAggregator::default()
				.sort_same_coefficients(2)
				.aggregate(
					&mut db,
					&LinearConstraint::new(
						LinExp::from((1, 5)) + (2, 5) + (3, 5) + (4, 5) + (5, 4),
						Comparator::LessEq,
						12 // only need 2 to sort
					)
				),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Amo(vec![(5, 4.into())]),
					Part::Ic(vec![(6, 5.into()), (7, 5.into())]),
				],
				cmp: LimitComp::LessEq,
				k: 12.into(),
			}))
		);
		db.check_complete()
	}

	#[test]
	fn test_equal_one() {
		let mut db = TestDB::new(3).expect_clauses(vec![]);
		// An exactly one constraint adds an at most one constraint + a clause for all literals
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 1) + (3, 1),
					Comparator::Equal,
					1
				)
			),
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vec![1, 2, 3],
				cmp: LimitComp::Equal
			}))
		);
		db.check_complete()
	}

	#[test]
	fn test_neg_coeff() {
		let mut db = TestDB::new(3);

		// Correctly convert a negative coefficient
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 2)) + (2, 3) + (3, -2),
					Comparator::LessEq,
					2
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 2), (2, 3), (-3, 2)]),
				cmp: LimitComp::LessEq,
				k: 4.into(),
			}))
		);

		// Correctly convert multiple negative coefficients
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, -1)) + (2, -1) + (3, -1),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vec![-1, -2, -3],
				cmp: LimitComp::LessEq
			}))
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, -1)) + (2, -2) + (3, -3),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(-1, 1), (-2, 2), (-3, 3)]),
				cmp: LimitComp::LessEq,
				k: 4.into(),
			}))
		);

		// Correctly convert multiple negative coefficients with AMO constraints
		let mut db = TestDB::new(6);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::default()
						.add_choice(&[(1, -1), (2, -3), (3, -4)])
						.add_choice(&[(4, -2), (5, -3), (6, -5)]),
					Comparator::LessEq,
					-4,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Amo(vec![(1, 3.into()), (2, 1.into()), (7, 4.into())]),
					Part::Amo(vec![(4, 3.into()), (5, 2.into()), (8, 5.into())]),
				],
				cmp: LimitComp::LessEq,
				k: 5.into(),
			}))
		);

		// Correctly convert multiple negative coefficients with side constraints
		let mut db = TestDB::new(6);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::default().add_chain(&[
						(1, 1),
						(2, -3),
						(3, -2),
						(4, 2),
						(5, 5),
						(6, -3)
					]),
					Comparator::LessEq,
					3
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Ic(vec![(1, 1.into()), (4, 2.into()), (5, 5.into())]),
					Part::Ic(vec![(-6, 3.into()), (-3, 2.into()), (-2, 3.into())]),
				],
				cmp: LimitComp::LessEq,
				k: 11.into(),
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut db = TestDB::new(6);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::default()
						.add_choice(&[(1, 1), (2, 2), (3, 3), (4, 4)])
						.add_choice(&[(5, 1), (6, 3)]),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Amo(vec![
						(1, 3.into()),
						(2, 2.into()),
						(3, 1.into()),
						(7, 4.into())
					]),
					Part::Amo(vec![(5, 2.into()), (8, 3.into())]),
				],
				cmp: LimitComp::LessEq,
				k: 4.into(), // -3 + 4 + 3
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut db = TestDB::new(6);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::default()
						.add_chain(&[(1, 1), (2, 1), (3, 1), (4, 1)])
						.add_chain(&[(5, 1), (6, 2)]),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Ic(vec![
						(-4, 1.into()),
						(-3, 1.into()),
						(-2, 1.into()),
						(-1, 1.into()),
					]),
					Part::Ic(vec![(-6, 2.into()), (-5, 1.into())]),
				],
				cmp: LimitComp::LessEq,
				k: 4.into(),
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut db = TestDB::new(5);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::default()
						.add_bounded_log_encoding(&[(1, 1), (2, 2), (3, 4)], 0, 5)
						.add_bounded_log_encoding(&[(4, 3), (5, 6)], 0, 2),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Dom(
						vec![(-1, 1.into()), (-2, 2.into()), (-3, 4.into())],
						2.into(),
						7.into()
					),
					Part::Dom(vec![(-4, 3.into()), (-5, 6.into())], 7.into(), 9.into()),
				],
				cmp: LimitComp::LessEq,
				k: 13.into(),
			}))
		);
	}

	#[test]
	fn test_at_least_one_negated() {
		let mut db = TestDB::new(4).expect_clauses(vec![vec![-1, -2, -3, -4]]);
		// An exactly one constraint adds an at most one constraint + a clause for all literals
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 1) + (3, 1) + (4, 1),
					Comparator::LessEq,
					3
				)
			),
			Ok(LinVariant::Trivial)
		);
		db.check_complete();

		// Correctly detect equal k
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut TestDB::new(3),
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 1) + (3, 1),
					Comparator::Equal,
					2
				)
			),
			// actually leaves over a CardinalityOne constraint
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vec![-1, -2, -3],
				cmp: LimitComp::LessEq,
			}))
		);
	}

	#[test]
	fn test_unsat() {
		let mut db = TestDB::new(3);

		// Constant cannot be reached
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 2) + (3, 2),
					Comparator::Equal,
					6
				)
			),
			Err(Unsatisfiable),
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 2) + (3, 2),
					Comparator::GreaterEq,
					6,
				)
			),
			Err(Unsatisfiable),
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 1)) + (2, 2) + (3, 2),
					Comparator::LessEq,
					-1
				)
			),
			Err(Unsatisfiable),
		);

		// Scaled counting constraint with off-scaled Constant
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from((1, 4)) + (2, 4) + (3, 4),
					Comparator::Equal,
					6
				)
			),
			Err(Unsatisfiable),
		);
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

	impl PartialEq for LinVariant<i32, i32> {
		fn eq(&self, other: &Self) -> bool {
			let liteq =
				|a: &Vec<i32>, b: &Vec<i32>| itertools::equal(a.iter().sorted(), b.iter().sorted());
			let parteq = |a: &Vec<Part<i32, PosCoeff<i32>>>, b: &Vec<Part<i32, PosCoeff<i32>>>| {
				itertools::equal(
					a.iter()
						.map(|p| p.iter().sorted().collect::<Vec<&(i32, PosCoeff<i32>)>>())
						.sorted(),
					b.iter()
						.map(|p| p.iter().sorted().collect::<Vec<&(i32, PosCoeff<i32>)>>())
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
				LinVariant::CardinalityOne(amo) => {
					if let LinVariant::CardinalityOne(oamo) = other {
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
