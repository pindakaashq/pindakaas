use itertools::Itertools;
use rustc_hash::{FxBuildHasher, FxHashMap};

use crate::{
	helpers::{emit_clause, is_powers_of_two, new_var},
	int::IntVarOrd,
	linear::{Constraint, LimitComp, Part, PosCoeff},
	sorted::{Sorted, SortedEncoder},
	Cardinality, CardinalityOne, ClauseDatabase, Coeff, Comparator, Encoder, LinExp, LinVariant,
	Linear, LinearConstraint, Lit, Result, Unsatisfiable,
};

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LinearAggregator {
	sorted_encoder: SortedEncoder,
	sort_same_coefficients: usize,
}

impl LinearAggregator {
	/// For non-zero `n`, detect groups of minimum size `n` with free literals and same coefficients, sort them (using provided SortedEncoder) and add them as a single implication chain group
	pub fn sort_same_coefficients(&mut self, sorted_encoder: SortedEncoder, n: usize) -> &mut Self {
		self.sorted_encoder = sorted_encoder;
		self.sort_same_coefficients = n;
		self
	}

	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "aggregator", skip_all, fields(constraint = lin.trace_print()))
	)]
	pub fn aggregate<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		lin: &LinearConstraint,
	) -> Result<LinVariant> {
		let mut k = lin.k;
		// Aggregate multiple occurrences of the same
		// variable.
		let mut agg = FxHashMap::with_capacity_and_hasher(lin.exp.terms.len(), FxBuildHasher);
		for term in &lin.exp.terms {
			let var = term.0.var();
			let entry = agg.entry(var).or_insert(0);
			let mut coef = term.1 * lin.exp.mult;
			if term.0.is_negated() {
				k -= coef;
				coef = -coef;
			}
			*entry += coef;
		}

		// Convert ≥ to ≤
		if lin.cmp == Comparator::GreaterEq {
			agg = agg.into_iter().map(|(var, coef)| (var, -coef)).collect();
			k = -k;
		}

		let mut partition: Vec<(Constraint, Vec<(Lit, Coeff)>)> =
			Vec::with_capacity(lin.exp.constraints.len());
		// Adjust side constraints when literals are combined (and currently transform to partition structure)
		let mut iter = lin.exp.terms.iter().skip(lin.exp.num_free);
		for con in &lin.exp.constraints {
			let mut terms = Vec::with_capacity(con.1);
			for _ in 0..con.1 {
				let term = iter.next().unwrap();
				if let Some((var, i)) = agg.remove_entry(&term.0.var()) {
					terms.push((var.into(), i));
				}
			}
			if !terms.is_empty() {
				match con.0 {
					Constraint::Domain { lb, ub } => {
						// Domain constraint can only be enforced when PB is coef*(x1 + 2x2 + 4x3 + ...), where l <= x1 + 2*x2 + 4*x3 + ... <= u
						if terms.len() == con.1 && is_powers_of_two(terms.iter().map(|(_, c)| *c)) {
							// Adjust the bounds to account for coef
							let (lb, ub) = if lin.cmp == Comparator::GreaterEq {
								// 0..range can be encoded by the bits multiplied by coef
								let range = -terms.iter().fold(0, |acc, (_, coef)| acc + *coef);
								// this range is inverted if we have flipped the comparator
								(range - ub, range - lb)
							} else {
								// in both cases, l and u now represent the true constraint
								(terms[0].1 * lb, terms[0].1 * ub)
							};
							partition.push((Constraint::Domain { lb, ub }, terms));
						} else {
							for term in terms {
								partition.push((Constraint::AtMostOne, vec![term]));
							}
						}
					}
					_ => partition.push((con.0.clone(), terms)),
				}
			}
		}

		// Add remaining (unconstrained) terms
		debug_assert!(agg.len() <= lin.exp.num_free);
		for (var, coeff) in agg.drain() {
			partition.push((Constraint::AtMostOne, vec![(var.into(), coeff)]));
		}

		k -= lin.exp.add;
		let cmp = match lin.cmp {
			Comparator::LessEq | Comparator::GreaterEq => LimitComp::LessEq,
			Comparator::Equal => LimitComp::Equal,
		};

		let convert_term_if_negative = |term: (Lit, Coeff), k: &mut Coeff| -> (Lit, PosCoeff) {
			let (mut lit, mut coef) = term;
			if coef.is_negative() {
				coef = -coef;
				lit = !lit;
				*k += coef;
			};
			(lit, PosCoeff::new(coef))
		};

		let partition: Vec<Part> = partition
			.into_iter()
			.filter(|(_, t)| !t.is_empty()) // filter out empty groups
			.flat_map(|part| -> Vec<Part> {
				// convert terms with negative coefficients
				match part {
					(Constraint::AtMostOne, mut terms) => {
						if terms.len() == 1 {
							return vec![Part::Amo(
								terms
									.into_iter()
									.filter(|&(_, coef)| coef != 0)
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
							let y = new_var!(db);

							// ~x1 /\ ~x2 /\ .. -> y == x1 \/ x2 \/ .. \/ y
							emit_clause!(
								db,
								terms
									.iter()
									.map(|(lit, _)| *lit)
									.chain(std::iter::once(y))
							)
							.unwrap();

														// y -> ( ~x1 /\ ~x2 /\ .. ) == ~y \/ ~x1, ~y \/ ~x2, ..
							for lit in terms.iter().map(|tup| tup.0) {
								emit_clause!(db, [!y, !lit]).unwrap();
							}

							// this term will cancel out later when we add q*min_lit to the LHS
							let _ =terms.remove(min_index);

							// since y + x1 + x2 + ... = 1 (exactly-one), we have q*y + q*x1 + q*x2 + ... = q
							// after adding term 0*y, we can add q*y + q*x1 + q*x2 + ... on the LHS, and q on the RHS
							terms.push((y, 0)); // note: it's fine to add y into the same AMO group
							terms = terms
								.iter()
								.map(|(lit, coef)| (*lit, *coef + q))
								.collect();
							k += q;
						}

						// all coefficients should be positive (since we subtracted the most negative coefficient)
						vec![Part::Amo(
							terms
								.into_iter()
								.map(|(lit, coef)| (lit, PosCoeff::new(coef)))
								.collect(),
						)]
					}

					(Constraint::ImplicationChain, terms) => {
						// normalize by splitting up the chain into two chains by coef polarity, inverting the coefs of the neg
						let (pos_chain, neg_chain): (_, Vec<_>) =
							terms.into_iter().partition(|(_, coef)| coef.is_positive());
						vec![
							Part::Ic(
								pos_chain
									.into_iter()
									.map(|(lit, coef)| (lit, PosCoeff::new(coef)))
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
					(Constraint::Domain { lb: l, ub: u },  terms) => {
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
							PosCoeff::new(l),
							PosCoeff::new(u),
						)]
					}
				}
			})
			.map(|part| {
				// This step has to come *after* Amo normalization
				let filter_zero_coefficients = |terms: Vec<(Lit, PosCoeff)>| -> Vec<(Lit, PosCoeff)> {
					terms
						.into_iter()
						.filter(|&(_, coef)| *coef != 0)
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
		if k < 0 {
			return Err(Unsatisfiable);
		}
		// trivial case: no literals can be activated
		if k == 0 {
			for part in partition {
				for (lit, _) in part.iter() {
					emit_clause!(db, [!lit])?;
				}
			}
			return Ok(LinVariant::Trivial);
		}
		let mut k = PosCoeff::new(k);

		// Remove terms with coefs higher than k
		let partition = partition
			.into_iter()
			.map(|part| match part {
				Part::Amo(terms) => Part::Amo(
					terms
						.into_iter()
						.filter(|(lit, coef)| {
							if coef > &k {
								emit_clause!(db, [!lit]).unwrap();
								false
							} else {
								true
							}
						})
						.collect(),
				),
				Part::Ic(terms) => {
					// for IC, we can compare the running sum to k
					let mut acc = 0;
					Part::Ic(
						terms
							.into_iter()
							.filter(|&(lit, coef)| {
								acc += *coef;
								if acc > *k {
									emit_clause!(db, [!lit]).unwrap();
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
								emit_clause!(db, [!lit]).unwrap();
								false
							} else {
								true
							}
						})
						.collect_vec();
					// the one or more of the most significant bits have been removed, the upper bound could have dropped to a power of 2 (but not beyond)
					let u = PosCoeff::new(std::cmp::min(
						*u,
						terms.iter().map(|&(_, coef)| *coef).sum(),
					));
					Part::Dom(terms, l, u)
				}
			})
			.filter(|part| part.iter().next().is_some()) // filter out empty groups
			.collect_vec();

		// Check whether some literals can violate / satisfy the constraint
		let lhs_ub = PosCoeff::new(
			partition
				.iter()
				.map(|part| match part {
					Part::Amo(terms) => terms.iter().map(|&(_, i)| *i).max().unwrap_or(0),
					Part::Ic(terms) | Part::Dom(terms, _, _) => {
						terms.iter().map(|&(_, coef)| *coef).sum()
						// TODO max(k, acc + ..)
					}
				})
				.sum(),
		);

		match cmp {
			LimitComp::LessEq => {
				if lhs_ub <= k {
					return Ok(LinVariant::Trivial);
				}

				// If we have only 2 (unassigned) lits, which together (but not individually) exceed k, then -x1\/-x2
				if partition.iter().flat_map(|part| part.iter()).count() == 2 {
					emit_clause!(
						db,
						partition
							.iter()
							.flat_map(|part| part.iter())
							.map(|(lit, _)| !lit)
							.collect_vec()
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
									[terms.iter().max_by(|(_, a), (_, b)| a.cmp(b)).unwrap().0]
								)?;
							}
							Part::Ic(terms) | Part::Dom(terms, _, _) => {
								for (lit, _) in terms {
									emit_clause!(db, [lit])?;
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
			.flat_map(|part| part.iter().map(|&(_, coef)| coef))
			.next()
			.unwrap();

		if partition
			.iter()
			.flat_map(|part| part.iter())
			.all(|&(_, coef)| coef == val)
		{
			// trivial case: k cannot be made from the coefficients
			if cmp == LimitComp::Equal && *k % *val != 0 {
				return Err(Unsatisfiable);
			}

			k = PosCoeff::new(*k / *val);
			let partition = partition
				.iter()
				.flat_map(|part| part.iter())
				.map(|&(lit, _)| lit)
				.collect_vec();
			if *k == 1 {
				// Cardinality One constraint
				return Ok(LinVariant::CardinalityOne(CardinalityOne {
					lits: partition,
					cmp,
				}));
			}

			// At most n-1 out of n is equivalent to at least *not* one
			// Ex. at most 2 out of 3 true = at least 1 out of 3 false
			if partition.len() == (*k + 1) as usize {
				let neg = partition.iter().map(|l| !l);
				emit_clause!(db, neg.clone())?;

				if cmp == LimitComp::LessEq {
					return Ok(LinVariant::Trivial);
				} else {
					// we still need to constrain x1 + x2 .. >= n-1
					//   == (1 - ~x1) + (1 - ~x2) + .. >= n-1
					//   == - ~x1 - ~x2 - .. <= n-1-n ( == .. <= -1)
					//   == ~x1 + ~x2 + .. <= 1
					return Ok(LinVariant::CardinalityOne(CardinalityOne {
						lits: neg.collect_vec(),
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

		let partition = if self.sort_same_coefficients >= 2 {
			let (free_lits, mut partition): (Vec<_>, Vec<_>) = partition.into_iter().partition(
				|part| matches!(part, Part::Amo(x) | Part::Ic(x) | Part::Dom(x, _, _) if x.len() == 1),
			);

			for (coef, lits) in free_lits
				.into_iter()
				.map(|part| match part {
					Part::Amo(x) | Part::Ic(x) | Part::Dom(x, _, _) if x.len() == 1 => x[0],
					_ => unreachable!(),
				})
				.map(|(lit, coef)| (coef, lit))
				.into_group_map()
				.into_iter()
			{
				if self.sort_same_coefficients >= 2 && lits.len() >= self.sort_same_coefficients {
					let c = *k / *coef;

					let y = IntVarOrd::from_bounds(db, 0, c, String::from("s")).into();
					self.sorted_encoder
						.encode(db, &Sorted::new(&lits, cmp.clone(), &y))
						.unwrap();

					let lin_exp = LinExp::from(&y);
					partition.push(Part::Ic(
						lin_exp
							.terms
							.into_iter()
							.map(|(lit, _)| (lit, coef))
							.collect(),
					));
				} else {
					for x in lits {
						partition.push(Part::Amo(vec![(x, coef)]));
					}
				}
			}

			partition
		} else {
			partition
		};

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
	use std::num::NonZeroI32;

	use itertools::Itertools;

	// use traced_test::test;
	use super::*;
	use crate::{
		helpers::tests::{assert_encoding, expect_file},
		linear::{tests::construct_terms, PosCoeff},
		solver::NextVarRange,
		Cnf, LinExp,
	};

	#[test]
	fn test_combine() {
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		// Simple aggregation of multiple occurrences of the same literal
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 2, 1, 2], &[a, a, b, c]),
					Comparator::LessEq,
					3
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(1, 3), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(3)
			}))
		);

		// Aggregation of positive and negative occurrences of the same literal
		// x1 +2*~x1 + ... <= 3
		// x1 +2 -2*x1 + ... <= 3
		// x1 -2*x1 + ... <= 1
		// -1*x1 + ... <= 1
		// +1*~x1 + ... <= 2
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 2, 1, 2], &[a, !a, b, c]),
					Comparator::LessEq,
					3
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(!a, 1), (b, 1), (c, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(2)
			}))
		);

		// Aggregation of positive and negative coefficients of the same literal
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, -2, 1, 2], &[a, a, b, c]),
					Comparator::LessEq,
					2,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(!a, 1), (b, 1), (c, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(3)
			}))
		);

		assert_eq!(cnf.clauses(), 0);
	}

	#[test]
	fn test_detection() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf
			.next_var_range(4)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();

		// Correctly detect at most one
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 1, 1], &[a, b, c]),
					Comparator::LessEq,
					1
				)
			),
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vec![a, b, c],
				cmp: LimitComp::LessEq
			}))
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[2, 2, 2], &[a, b, c]),
					Comparator::LessEq,
					2
				)
			),
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vec![a, b, c],
				cmp: LimitComp::LessEq
			}))
		);

		// Correctly detect at most k
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
					Comparator::LessEq,
					2
				)
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![a, b, c, d],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(2),
			}))
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[3, 3, 3, 3], &[a, b, c, d]),
					Comparator::LessEq,
					7
				)
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![a, b, c, d],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(2),
			}))
		);

		// Correctly detect equal k
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
					Comparator::Equal,
					2
				)
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![a, b, c, d],
				cmp: LimitComp::Equal,
				k: PosCoeff::new(2),
			}))
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[3, 3, 3, 3], &[a, b, c, d]),
					Comparator::Equal,
					6
				)
			),
			Ok(LinVariant::Cardinality(Cardinality {
				lits: vec![a, b, c, d],
				cmp: LimitComp::Equal,
				k: PosCoeff::new(2),
			}))
		);

		// Is still normal Boolean linear in-equality
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 2, 2], &[a, b, c]),
					Comparator::LessEq,
					2
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(a, 1), (b, 2), (c, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(2),
			}))
		);

		// Is still normal Boolean linear equality
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 2, 2], &[a, b, c]),
					Comparator::Equal,
					2
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(a, 1), (b, 2), (c, 2)]),
				cmp: LimitComp::Equal,
				k: PosCoeff::new(2),
			}))
		);

		// Correctly identify that the AMO is limiting the LHS ub
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_terms(&[(c, -1)]).add_choice(&[(a, -1), (b, -1)]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(LinVariant::Trivial)
		);
	}

	#[test]
	fn test_sort_same_coefficients() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf
			.next_var_range(4)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();

		assert_eq!(
			LinearAggregator::default()
				.sort_same_coefficients(SortedEncoder::default(), 2)
				.aggregate(
					&mut cnf,
					&LinearConstraint::new(
						LinExp::from_slices(&[3, 3, 5, 3], &[a, b, d, c]),
						Comparator::LessEq,
						10
					)
				),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Ic(vec![
						(Lit(NonZeroI32::new(5).unwrap()), PosCoeff::new(3)),
						(Lit(NonZeroI32::new(6).unwrap()), PosCoeff::new(3)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(3))
					]),
					Part::Amo(vec![(d, PosCoeff::new(5))]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(10),
			}))
		);
	}

	#[test]
	fn test_sort_same_coefficients_using_minimal_chain() {
		let mut cnf = Cnf::default();
		let vars = cnf.next_var_range(5).unwrap().iter_lits().collect_vec();
		assert_eq!(
			LinearAggregator::default()
				.sort_same_coefficients(SortedEncoder::default(), 2)
				.aggregate(
					&mut cnf,
					&LinearConstraint::new(
						LinExp::from_slices(&[5, 5, 5, 5, 4], &vars),
						Comparator::LessEq,
						12 // only need 2 to sort
					)
				),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Amo(vec![(*vars.last().unwrap(), PosCoeff::new(4))]),
					Part::Ic(vec![
						(Lit(NonZeroI32::new(6).unwrap()), PosCoeff::new(5)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(5))
					]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(12),
			}))
		);
	}

	#[test]
	fn test_equal_one() {
		let mut cnf = Cnf::default();
		let vars = cnf.next_var_range(3).unwrap().iter_lits().collect_vec();
		// An exactly one constraint adds an exactly one constraint
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 1, 1], &vars),
					Comparator::Equal,
					1
				)
			),
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vars,
				cmp: LimitComp::Equal
			}))
		);
		assert_eq!(cnf.clauses(), 0);
	}

	#[test]
	fn test_neg_coeff() {
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();

		// Correctly convert a negative coefficient
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[2, 3, -2], &[a, b, c]),
					Comparator::LessEq,
					2
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(a, 2), (b, 3), (!c, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4),
			}))
		);

		// Correctly convert multiple negative coefficients
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[-1, -1, -1], &[a, b, c]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vec![!a, !b, !c],
				cmp: LimitComp::LessEq
			}))
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[-1, -2, -3], &[a, b, c]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[(!a, 1), (!b, 2), (!c, 3)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4),
			}))
		);

		// Correctly convert multiple negative coefficients with AMO constraints
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf
			.next_var_range(6)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::default()
						.add_choice(&[(a, -1), (b, -3), (c, -4)])
						.add_choice(&[(d, -2), (e, -3), (f, -5)]),
					Comparator::LessEq,
					-4,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Amo(vec![
						(a, PosCoeff::new(3)),
						(b, PosCoeff::new(1)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(4))
					]),
					Part::Amo(vec![
						(d, PosCoeff::new(3)),
						(e, PosCoeff::new(2)),
						(Lit(NonZeroI32::new(8).unwrap()), PosCoeff::new(5))
					]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(5),
			}))
		);

		// Correctly convert multiple negative coefficients with side constraints
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf
			.next_var_range(6)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::default().add_chain(&[
						(a, 1),
						(b, -3),
						(c, -2),
						(d, 2),
						(e, 5),
						(f, -3)
					]),
					Comparator::LessEq,
					3
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Ic(vec![
						(a, PosCoeff::new(1)),
						(d, PosCoeff::new(2)),
						(e, PosCoeff::new(5))
					]),
					Part::Ic(vec![
						(!f, PosCoeff::new(3)),
						(!c, PosCoeff::new(2)),
						(!b, PosCoeff::new(3))
					]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(11),
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf
			.next_var_range(6)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::default()
						.add_choice(&[(a, 1), (b, 2), (c, 3), (d, 4)])
						.add_choice(&[(e, 1), (f, 3)]),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Amo(vec![
						(a, PosCoeff::new(3)),
						(b, PosCoeff::new(2)),
						(c, PosCoeff::new(1)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(4))
					]),
					Part::Amo(vec![
						(e, PosCoeff::new(2)),
						(Lit(NonZeroI32::new(8).unwrap()), PosCoeff::new(3))
					]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4), // -3 + 4 + 3
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf
			.next_var_range(6)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::default()
						.add_chain(&[(a, 1), (b, 1), (c, 1), (d, 1)])
						.add_chain(&[(e, 1), (f, 2)]),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Ic(vec![
						(!d, PosCoeff::new(1)),
						(!c, PosCoeff::new(1)),
						(!b, PosCoeff::new(1)),
						(!a, PosCoeff::new(1)),
					]),
					Part::Ic(vec![(!f, PosCoeff::new(2)), (!e, PosCoeff::new(1))]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4),
			}))
		);

		// Correctly account for the coefficient in the Dom bounds
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::default().add_bounded_log_encoding(&[(a, 1), (b, 2), (c, 4)], 0, 3),
					Comparator::LessEq,
					5,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![Part::Dom(
					vec![
						(a, PosCoeff::new(1)),
						(b, PosCoeff::new(2)),
						(c, PosCoeff::new(4))
					],
					PosCoeff::new(0),
					PosCoeff::new(7)
				),],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(5),
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut cnf = Cnf::default();
		let (a, b, c, d, e) = cnf
			.next_var_range(5)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::default()
						.add_bounded_log_encoding(&[(a, 1), (b, 2), (c, 4)], 0, 5)
						.add_bounded_log_encoding(&[(d, 3), (e, 6)], 0, 2),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: vec![
					Part::Dom(
						vec![
							(!a, PosCoeff::new(1)),
							(!b, PosCoeff::new(2)),
							(!c, PosCoeff::new(4))
						],
						PosCoeff::new(2),
						PosCoeff::new(7),
					),
					Part::Dom(
						vec![(!d, PosCoeff::new(3)), (!e, PosCoeff::new(6))],
						PosCoeff::new(7),
						PosCoeff::new(9),
					),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(13),
			}))
		);
	}

	#[test]
	fn test_false_trivial_unsat() {
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f, g) = cnf
			.next_var_range(7)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 2, 1, 1, 4, 1, 1], &[a, !b, c, d, !e, f, !g]),
					Comparator::GreaterEq,
					7
				)
			),
			Ok(LinVariant::Linear(Linear {
				terms: construct_terms(&[
					(e, 4),
					(b, 2),
					(g, 1),
					(!d, 1),
					(!a, 1),
					(!f, 1),
					(!c, 1)
				]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4),
			}))
		);
		assert_eq!(cnf.clauses(), 0);
	}

	#[test]
	fn test_at_least_one_negated() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf
			.next_var_range(4)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		// Correctly detect that all but one literal can be set to true
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
					Comparator::LessEq,
					3
				)
			),
			Ok(LinVariant::Trivial)
		);
		assert_encoding(
			&cnf,
			&expect_file!["linear/aggregator/test_at_least_one_negated.cnf"],
		);

		// Correctly detect equal k
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 1, 1], &[a, b, c]),
					Comparator::Equal,
					2
				)
			),
			// actually leaves over a CardinalityOne constraint
			Ok(LinVariant::CardinalityOne(CardinalityOne {
				lits: vec![!a, !b, !c],
				cmp: LimitComp::LessEq,
			}))
		);
	}

	#[test]
	fn test_unsat() {
		let mut db = Cnf::default();
		let vars = db.next_var_range(3).unwrap().iter_lits().collect_vec();

		// Constant cannot be reached
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 2, 2], &vars),
					Comparator::Equal,
					6
				)
			),
			Err(Unsatisfiable)
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 2, 2], &vars),
					Comparator::GreaterEq,
					6,
				)
			),
			Err(Unsatisfiable)
		);
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 2, 2], &vars),
					Comparator::LessEq,
					-1
				)
			),
			Err(Unsatisfiable)
		);

		// Scaled counting constraint with off-scaled Constant
		assert_eq!(
			LinearAggregator::default().aggregate(
				&mut db,
				&LinearConstraint::new(
					LinExp::from_slices(&[4, 4, 4], &vars),
					Comparator::Equal,
					6
				)
			),
			Err(Unsatisfiable)
		);
	}

	impl PartialEq for Part {
		fn eq(&self, other: &Self) -> bool {
			let term_eq = |a: &Vec<(_, _)>, b: &Vec<(_, _)>| {
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

	impl PartialOrd for Part {
		fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
			let termcmp = |a: &Vec<(Lit, PosCoeff)>, b: &Vec<(Lit, PosCoeff)>| {
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

	impl PartialEq for LinVariant {
		fn eq(&self, other: &Self) -> bool {
			let liteq =
				|a: &Vec<Lit>, b: &Vec<Lit>| itertools::equal(a.iter().sorted(), b.iter().sorted());
			let parteq = |a: &Vec<Part>, b: &Vec<Part>| {
				itertools::equal(
					a.iter().map(|p| p.iter().sorted().collect_vec()).sorted(),
					b.iter().map(|p| p.iter().sorted().collect_vec()).sorted(),
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
					matches!(other, LinVariant::Trivial)
				}
			}
		}
	}
}
