//! Encoding an integer linear constraint, on whichever view of its variables
//! costs least.
//!
//! Three shapes are recognised: a sum of two binary variables against a third,
//! which a ripple-carry adder states directly; a sum of binary variables
//! against a constant, built from shift-and-add products; and otherwise a walk
//! over the terms in order form, which any variable can produce.

use std::{iter::once, num::NonZero};

use itertools::Itertools;
use rangelist::RangeList;

use crate::{
	constraint::{
		bool_linear::Comparator,
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		int_linear::{Decompose, IntLinear, NormalizedIntLinear, Term},
	},
	decision::integer::{BinaryEncoding, IntVar},
	encoder::adder::AdderEncoder,
	helpers::{
		div_ceil, div_floor,
		scm::{ScmObjective, ScmOperation, ScmSolution},
		shifted,
	},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Result, Unsatisfiable,
};

/// Encoder for [`IntLinear`] constraints.
///
/// The encoder is kept between constraints so that what it learns about a
/// variable while encoding one is available to the next: the encodings a
/// variable has been given, and later the products built for its coefficients.
#[derive(Clone, Debug, Default)]
pub struct IntLinEncoder {
	config: IntLinConfig,
}

/// Encoding a constraint fixes the literals of the variables it mentions, and
/// so also fixes their domains. A constraint encoded later can still narrow a
/// variable that no constraint has reached yet, but not one that is already
/// encoded, which makes the result depend on the order the constraints are
/// given in. Every such result is correct; they differ only in how much was
/// pruned before the literals were committed.
impl<Db: ClauseDatabase + ?Sized> Encoder<Db, IntLinear> for IntLinEncoder {
	fn encode(&self, db: &mut Db, con: &IntLinear) -> Result {
		if self.config.propagate {
			con.propagate()?;
		}
		let terms = &con.exp.terms;
		let binary = |t: &Term| t.x.prefers_binary(self.config.cutoff);

		// A sum of two binary variables against a third is what a ripple-carry
		// adder does directly, and it is the shape a coefficient decomposes
		// into, so it is worth recognising before anything else.
		if let Some((x, y, z)) = con.as_addition() {
			if [x, y, z].iter().all(|t| binary(t)) {
				return Term::encode_addition(db, x, y, z);
			}
		}
		// Binary variables added together, whatever their coefficients: build
		// the sum out of adders and bound it, rather than sending them all
		// through the walk, which would channel each to order form — the very
		// cost binary was chosen to avoid. A sum that is negative throughout is
		// the same constraint read the other way round against `−k`.
		let negated = !terms.is_empty() && terms.iter().all(|t| t.c < 0);
		if !terms.is_empty() && terms.iter().all(|t| binary(t) && (t.c > 0) != negated) {
			let scaled = if negated {
				terms.iter().map(Term::negated).collect()
			} else {
				terms.clone()
			};
			let (cmp, k) = if negated {
				(con.cmp.reverse(), -con.k)
			} else {
				(con.cmp, con.k)
			};
			if let Some(total) = self.binary_sum(db, &scaled)? {
				// The sum reaches what its terms reach together.
				let reach = |f: fn(&Term) -> Coeff| scaled.iter().map(f).sum::<Coeff>();
				let domain = RangeList::from(reach(Term::min)..=reach(Term::max));
				return cmp
					.split()
					.into_iter()
					.try_for_each(|cmp| total.encode_bound(db, cmp, k, &domain));
			}
		}

		// Otherwise walk the terms in order form. Any variable can produce an
		// order encoding, channelling to one it already has if need be, so this
		// is always available even where it is not the cheapest.
		// Every variable is given a view up front, even one the walk turns out
		// not to ask anything of: a variable a constraint mentions is one whose
		// value a solution has to be able to say. A variable already read
		// directly is read that way again, rather than gaining a second view to
		// be tied to the first.
		for t in terms {
			if !t.x.has_direct_encoding() {
				let _ = t.x.order_encoding(db)?;
			}
		}
		let encoded: Vec<Encoded> = terms.iter().map(|t| Encoded { c: t.c, x: &t.x }).collect();

		// An equality holds exactly when both of its inequalities do.
		for cmp in con.cmp.split() {
			for clause in Encoded::walk(db, &encoded, cmp, con.k)? {
				db.add_clause(clause)?;
			}
		}
		Ok(())
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, NormalizedIntLinear> for IntLinEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "int_lin_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		Encoder::encode(self, db, &IntLinear::from(con))
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for IntLinEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		Encoder::encode(self, db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for IntLinEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		Encoder::encode(self, db, &Cardinality::from(con.clone()))
	}
}

/// Configuration for an [`IntLinEncoder`].
#[derive(Clone, Debug)]
pub struct IntLinConfig {
	/// Whether to narrow the domains of the variables of a constraint before
	/// encoding it.
	pub propagate: bool,
	/// The domain size from which a variable is held in binary rather than in
	/// order form. `None` keeps every variable in order form.
	pub cutoff: Option<Coeff>,
}

/// A term of a constraint, together with the view of its variable the walk
/// will guard on.
///
/// Materialising every encoding before the clauses are built keeps the walk
/// over the terms a pure function of what is already there.
#[derive(Clone, Copy, Debug)]
struct Encoded<'a> {
	c: Coeff,
	x: &'a IntVar,
}

impl Default for IntLinConfig {
	fn default() -> Self {
		Self {
			propagate: true,
			cutoff: None,
		}
	}
}

impl IntLinEncoder {
	/// Break `con` apart and encode each piece.
	pub(crate) fn encode_decomposed<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		con: &NormalizedIntLinear,
		decompose: &impl Decompose,
	) -> Result {
		// A decomposition that cannot be built is a constraint that cannot be
		// met, which the database has to be told rather than only the caller.
		let Ok(cons) = decompose.decompose(db, con) else {
			return db.contradiction();
		};
		cons.iter()
			.try_for_each(|con| Encoder::encode(self, db, &IntLinear::from(con)))
	}

	/// The encoding of `Σ cᵢ·xᵢ`, or `None` if some coefficient cannot be
	/// decomposed into shifts and adders.
	fn binary_sum<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		terms: &[Term],
	) -> Result<Option<BinaryEncoding>, Unsatisfiable> {
		let mut total: Option<Vec<BoolVal>> = None;
		for t in terms {
			let Some(bits) = self.scaled_bits(db, &t.x, t.c)? else {
				return Ok(None);
			};
			total = Some(match total {
				None => bits,
				Some(acc) => AdderEncoder::ripple_carry_adder(db, &acc, &bits, None, None)?,
			});
		}
		// The bits of each term count from its own lower bound, so the sum
		// counts from all of them together.
		Ok(Some(BinaryEncoding::from_bits(
			total.unwrap_or_default(),
			terms.iter().map(Term::min).sum(),
		)))
	}

	/// The bits of `c·(x − lb)`, built from shifts and adders.
	///
	/// A shift costs nothing, being leading zero bits on the vector, so what is
	/// left is to find the fewest additions that reach `c`. That is the
	/// single-constant multiplication problem, and [`ScmSolution::synthesize`]
	/// plans it.
	fn scaled_bits<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		x: &IntVar,
		c: Coeff,
	) -> Result<Option<Vec<BoolVal>>, Unsatisfiable> {
		debug_assert!(c > 0, "a product is decomposed only for a positive factor");
		if let Some(bits) = x.product(c) {
			return Ok(Some(bits));
		}
		let Ok(c32) = u32::try_from(c) else {
			return Ok(None);
		};
		let input = x.binary_encoding(db)?.to_vec();
		let Some(width) = NonZero::new(input.len() as u32) else {
			// A variable of one value contributes nothing to the sum.
			return Ok(Some(Vec::new()));
		};

		// Every step of the plan names what it computes by the factor it
		// reaches, which is the same thing the cache is keyed on, so a step
		// shared with an earlier synthesis is picked up rather than rebuilt.
		let plan = ScmSolution::synthesize(c32, ScmObjective::MinAdders(width));
		x.set_product(1, input);
		for op in plan.operations {
			let factor = Coeff::from(op.result().get());
			if x.product(factor).is_some() {
				continue;
			}
			let bits = match op {
				ScmOperation::ShiftLeft { source, shift } => {
					shifted(&Self::product(x, source.get()), shift)
				}
				ScmOperation::ShiftAdd { left, right, shift } => {
					let left = shifted(&Self::product(x, left.get()), shift);
					AdderEncoder::ripple_carry_adder(
						db,
						&left,
						&Self::product(x, right.get()),
						None,
						None,
					)?
				}
				ScmOperation::ShiftSub { left, right, shift } => {
					let left = shifted(&Self::product(x, left.get()), shift);
					self.difference(db, &left, &Self::product(x, right.get()), factor, &width)?
				}
				ScmOperation::SubShift { left, right, shift } => {
					let right = shifted(&Self::product(x, right.get()), shift);
					let left = Self::product(x, left.get());
					self.difference(db, &left, &right, factor, &width)?
				}
			};
			x.set_product(factor, bits);
		}
		Ok(Some(Self::product(x, c32)))
	}

	/// The bits of a difference `a − b`, which is known to be positive.
	///
	/// Subtraction is addition read the other way round: the bits are created
	/// and then constrained so that adding `b` back gives `a`.
	fn difference<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		a: &[BoolVal],
		b: &[BoolVal],
		factor: Coeff,
		width: &NonZero<u32>,
	) -> Result<Vec<BoolVal>, Unsatisfiable> {
		let span = factor * ((1 << width.get()) - 1);
		let bits: Vec<BoolVal> = (0..BinaryEncoding::required_bits(span))
			.map(|_| BoolVal::Lit(db.new_lit()))
			.collect();
		let _ = AdderEncoder::ripple_carry_adder(db, b, &bits, None, Some(a))?;
		Ok(bits)
	}

	/// The bits of a product already built.
	fn product(x: &IntVar, factor: u32) -> Vec<BoolVal> {
		x.product(Coeff::from(factor))
			.expect("the plan builds every product before it is used")
	}

	/// Create an encoder with the given configuration.
	pub fn with_config(config: IntLinConfig) -> Self {
		Self { config }
	}
}

impl Encoded<'_> {
	/// The clauses for `Σ terms ≷ k`, by taking the terms one at a time.
	///
	/// The head term is walked over the values it can take. Reaching a value
	/// costs the sum a known amount, so what is left for the remaining terms
	/// is a smaller constraint of the same shape, and the clauses for it need
	/// only hold when that value is in fact reached.
	fn walk<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		terms: &[Encoded],
		cmp: Comparator,
		k: Coeff,
	) -> Result<Vec<Vec<BoolVal>>, Unsatisfiable> {
		let Some((head, tail)) = terms.split_first() else {
			// Nothing left to give, so the empty sum either satisfies what
			// remains of the constraint or nothing can.
			let holds = match cmp {
				Comparator::LessEq => 0 <= k,
				Comparator::GreaterEq => 0 >= k,
				Comparator::Equal => unreachable!("an equality is split before it is encoded"),
			};
			return Ok(if holds { Vec::new() } else { vec![Vec::new()] });
		};
		if tail.is_empty() {
			return head.bound(db, cmp, k);
		}
		// Guard on the head reaching a value from whichever side pushes the sum
		// towards breaking the constraint.
		let geq = (head.c >= 0) == matches!(cmp, Comparator::LessEq);
		let mut clauses = Vec::new();
		let mut last: Option<Vec<Vec<BoolVal>>> = None;
		// A variable a group of terms arrived on is read on the direct literals
		// it came with; any other on its order encoding.
		let steps = if head.x.has_direct_encoding() {
			head.x.lit_direct_steps(db, geq)?
		} else {
			head.x.lit_order_steps(db, geq)?
		};
		for (d, guard) in steps {
			let sub = Self::walk(db, tail, cmp, k - head.c * d)?;
			// Advancing the walk only weakens the guard, so a step that asks of
			// the remaining terms exactly what the step before it asked is
			// already covered by that one. Consecutive steps land on the
			// same demand often: dividing by a coefficient rounds to the
			// same bound, and the order literals snap to the values the
			// domain actually has.
			if last.as_ref() == Some(&sub) {
				continue;
			}
			clauses.extend(
				sub.iter()
					.map(|clause| once(guard).chain(clause.iter().copied()).collect()),
			);
			last = Some(sub);
		}
		Ok(clauses)
	}

	/// The clauses for `c·x ≷ k`, this term being the only one left.
	fn bound<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		cmp: Comparator,
		k: Coeff,
	) -> Result<Vec<Vec<BoolVal>>, Unsatisfiable> {
		// Dividing by a negative coefficient turns the comparison around.
		let cmp = if self.c >= 0 { cmp } else { cmp.reverse() };
		if self.x.has_direct_encoding() {
			// Nothing says it in one literal, so rule out each value that would
			// break the bound instead.
			let breaks = self
				.x
				.lit_direct_steps(db, true)?
				.into_iter()
				.filter(|&(d, _)| match cmp {
					Comparator::LessEq => self.c * d > k,
					_ => self.c * d < k,
				})
				.map(|(d, _)| d)
				.collect_vec();
			breaks
				.into_iter()
				.map(|d| Ok(vec![!self.x.lit_equals(db, d)?]))
				.collect()
		} else {
			// One literal says where the variable stands against the bound.
			Ok(vec![vec![match cmp {
				Comparator::LessEq => self.x.lit_at_most(db, div_floor(k, self.c))?,
				Comparator::GreaterEq => self.x.lit_at_least(db, div_ceil(k, self.c))?,
				Comparator::Equal => unreachable!("an equality is split before it is encoded"),
			}]])
		}
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use rangelist::RangeList;
	use traced_test::test;

	use crate::{
		constraint::{
			bool_linear::{Comparator, LimitComp, PosCoeff},
			cardinality_one::{CardinalityOne, PairwiseEncoder},
			int_linear::{IntLinConfig, IntLinEncoder, IntLinear, Term},
		},
		decision::integer::IntVar,
		solver::{cadical::Cadical, SolveResult, Solver},
		ClauseDatabaseTools, Cnf, Coeff, Encoder, Lit, Valuation,
	};

	/// Encode `Σ cᵢ·xᵢ ≷ k` over the given domains and return the assignments
	/// its models stand for, in order.
	fn solutions_of(
		coeffs: &[Coeff],
		doms: &[RangeList<Coeff>],
		cmp: Comparator,
		k: Coeff,
		propagate: bool,
	) -> Vec<Vec<Coeff>> {
		solutions_with(coeffs, doms, cmp, k, propagate, None).0
	}

	/// As [`solutions_of`], choosing how the variables are encoded.
	fn solutions_with(
		coeffs: &[Coeff],
		doms: &[RangeList<Coeff>],
		cmp: Comparator,
		k: Coeff,
		propagate: bool,
		cutoff: Option<Coeff>,
	) -> (Vec<Vec<Coeff>>, Vec<IntVar>) {
		let mut cnf = Cnf::default();
		let enc = IntLinEncoder::with_config(IntLinConfig { propagate, cutoff });
		let xs = doms
			.iter()
			.enumerate()
			.map(|(i, domain)| IntVar::new(domain.clone()).with_label(format!("x{i}")))
			.collect_vec();
		let terms = coeffs
			.iter()
			.zip(&xs)
			.map(|(&c, x)| Term::new(c, x.clone()))
			.collect_vec();

		let con = IntLinear::new(terms, cmp, k);
		if enc.encode(&mut cnf, &con).is_err() {
			return (Vec::new(), xs);
		}
		// Every model is ruled out in turn and read for what the variables
		// come to, so an assignment reachable more than one way is seen more
		// than once. A constraint whose variables were all narrowed to a
		// single value has no literals at all, and the empty nogood correctly
		// stops after one.
		let vars = cnf.get_variables();
		let mut slv = Cadical::from(&cnf);
		let mut solutions = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			solutions.push(xs.iter().map(|x| x.value(&value)).collect_vec());
			let no_good = vars
				.map(|v| {
					let l = v.into();
					if value.value(l) {
						!l
					} else {
						l
					}
				})
				.collect_vec();
			if slv.add_clause(no_good).is_err() {
				break;
			}
		}
		solutions.sort();
		solutions.dedup();
		(solutions, xs)
	}

	/// Every assignment over `doms` that satisfies `Σ cᵢ·xᵢ ≷ k`.
	fn brute_force(
		coeffs: &[Coeff],
		doms: &[RangeList<Coeff>],
		cmp: Comparator,
		k: Coeff,
	) -> Vec<Vec<Coeff>> {
		doms.iter()
			.map(|d| d.iter().flatten().collect_vec())
			.multi_cartesian_product()
			.filter(|assign| {
				let sum: Coeff = coeffs.iter().zip(assign).map(|(c, v)| c * v).sum();
				match cmp {
					Comparator::LessEq => sum <= k,
					Comparator::Equal => sum == k,
					Comparator::GreaterEq => sum >= k,
				}
			})
			.sorted()
			.collect()
	}

	#[test]
	fn order_encoding_admits_exactly_the_solutions() {
		let contiguous = RangeList::from(0..=3);
		let holey = RangeList::from_elements([0, 1, 3]);
		let negative = RangeList::from_elements([-2, -1, 1]);
		let cases: Vec<(Vec<Coeff>, Vec<RangeList<Coeff>>)> = vec![
			(vec![1, 1], vec![contiguous.clone(), contiguous.clone()]),
			(vec![2, -3], vec![contiguous.clone(), holey.clone()]),
			(vec![1, 1, 1], vec![holey.clone(); 3]),
			(vec![3, -1, 2], vec![negative.clone(), contiguous, holey]),
			(vec![-2, -5], vec![negative.clone(), negative]),
		];
		for (coeffs, doms) in cases {
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				for k in -6..=6 {
					// Propagation must not change which assignments survive,
					// only how much of the domain is left when the literals are
					// made, so both settings are checked against brute force.
					for propagate in [false, true] {
						assert_eq!(
							solutions_of(&coeffs, &doms, cmp, k, propagate),
							brute_force(&coeffs, &doms, cmp, k),
							"{coeffs:?} {cmp:?} {k} over {doms:?} (propagate: {propagate})"
						);
					}
				}
			}
		}
	}

	/// Every model of `cnf`, as the value `x` takes together with which of
	/// `lits` were chosen.
	fn group_solutions(cnf: &Cnf, x: &IntVar, lits: &[Lit]) -> Vec<(Coeff, Vec<bool>)> {
		let mut slv = Cadical::from(cnf);
		let vars = cnf.get_variables();
		let mut solutions = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			solutions.push((
				x.value(&value),
				lits.iter().map(|&l| value.value(l)).collect(),
			));
			let no_good: Vec<_> = vars
				.map(|v| {
					let l = v.into();
					if value.value(l) {
						!l
					} else {
						l
					}
				})
				.collect();
			if slv.add_clause(no_good).is_err() {
				break;
			}
		}
		solutions.sort();
		solutions
	}

	#[test]
	fn a_group_of_exclusive_terms_becomes_its_largest_chosen_value() {
		for exact in [false, true] {
			let mut cnf = Cnf::default();
			let lits: Vec<Lit> = (0..3).map(|_| cnf.new_lit()).collect();
			// The terms are mutually exclusive, which is what lets the group be
			// read as one integer.
			PairwiseEncoder::default()
				.encode(
					&mut cnf,
					&CardinalityOne {
						lits: lits.clone(),
						cmp: LimitComp::LessEq,
					},
				)
				.unwrap();
			let t = Term::from_at_most_one(
				&mut cnf,
				&[
					(lits[0], PosCoeff::new(2)),
					(lits[1], PosCoeff::new(5)),
					(lits[2], PosCoeff::new(2)),
				],
				"x",
				exact,
			)
			.unwrap();
			let x = &t.x;
			let _ = x.order_encoding(&mut cnf).unwrap();

			let solutions = group_solutions(&cnf, x, &lits);
			let choices: Vec<_> = solutions
				.iter()
				.map(|(_, chosen)| chosen.clone())
				.sorted()
				.dedup()
				.collect();
			assert_eq!(
				choices.len(),
				4,
				"reading the group as an integer must not rule out a choice of terms"
			);
			for (value, chosen) in solutions {
				let worth: Coeff = chosen
					.iter()
					.zip([2, 5, 2])
					.filter(|(c, _)| **c)
					.map(|(_, w)| w)
					.sum();
				if exact {
					// With the upper bound the group is exactly its chosen
					// term.
					assert_eq!(value, worth, "chose {chosen:?}");
				} else {
					// Without it, choosing a term only forces the group up, so
					// it may over-state and never under-states. That is sound
					// for a `≤`, which is all a group without the bound is for,
					// and costs no solutions: the terms are still free.
					assert!(value >= worth, "{value} under {worth} for {chosen:?}");
				}
			}
		}
	}

	#[test]
	fn a_chain_of_terms_becomes_its_running_sum() {
		let mut cnf = Cnf::default();
		let lits: Vec<Lit> = (0..3).map(|_| cnf.new_lit()).collect();
		// Each term implies the one before it, which is what the group means.
		for (a, b) in lits.iter().zip(lits.iter().skip(1)) {
			cnf.add_clause([!*b, *a]).unwrap();
		}
		let t = Term::from_implication_chain(
			&mut cnf,
			&[
				(lits[0], PosCoeff::new(2)),
				(lits[1], PosCoeff::new(3)),
				(lits[2], PosCoeff::new(4)),
			],
			"x",
		)
		.unwrap();
		let x = &t.x;
		let _ = x.order_encoding(&mut cnf).unwrap();

		let solutions = group_solutions(&cnf, x, &lits);
		// The chain admits four assignments, worth nothing, two, five and nine.
		assert_eq!(
			solutions.iter().map(|(v, _)| *v).collect::<Vec<_>>(),
			vec![0, 2, 5, 9]
		);
		for (value, chosen) in solutions {
			let worth: Coeff = chosen
				.iter()
				.zip([2, 3, 4])
				.filter(|(c, _)| **c)
				.map(|(_, w)| w)
				.sum();
			assert_eq!(value, worth, "chose {chosen:?}");
		}
	}

	#[test]
	fn a_plain_constraint_weighs_the_literals_it_came_from() {
		// Reading a pseudo-Boolean constraint as integers and weighing it back
		// out has to give what went in, or an encoder that works on literals
		// would pay for the detour.
		let mut cnf = Cnf::default();
		let lits: Vec<Lit> = (0..3).map(|_| cnf.new_lit()).collect();
		let coeffs = [1, 2, 5];
		let terms = lits
			.iter()
			.zip(coeffs)
			.map(|(&l, c)| Term::from_at_most_one(&mut cnf, &[(l, PosCoeff::new(c))], "x", true))
			.collect::<Result<Vec<_>, _>>()
			.unwrap();
		let con = IntLinear::new(terms, Comparator::LessEq, 6);

		let (weighed, constant) = con.as_weighted(&mut cnf).unwrap();
		assert_eq!(constant, 0);
		assert_eq!(
			weighed,
			lits.iter().copied().zip(coeffs).collect_vec(),
			"the literals and coefficients should be the ones given"
		);
	}

	#[test]
	fn a_lone_term_is_a_group_that_costs_nothing() {
		// Every term of a pseudo-Boolean constraint that nothing groups arrives
		// as a group of one, so this is the common case rather than a corner:
		// the term is worth its coefficient when chosen and nothing when not,
		// which its own literal already says both ways.
		for exact in [false, true] {
			let mut cnf = Cnf::default();
			let lit = cnf.new_lit();
			let (vars, clauses) = (cnf.num_vars(), cnf.num_clauses());

			let t =
				Term::from_at_most_one(&mut cnf, &[(lit, PosCoeff::new(5))], "x", exact).unwrap();
			assert_eq!(
				(cnf.num_vars(), cnf.num_clauses()),
				(vars, clauses),
				"a group of one term should need nothing of its own"
			);

			// And it still reads as the integer it stands for.
			let x = &t.x;
			let mut slv = Cadical::from(&cnf);
			let mut seen = Vec::new();
			while let SolveResult::Satisfied(value) = slv.solve() {
				seen.push((value.value(lit), x.value(&value)));
				if slv
					.add_clause([if value.value(lit) { !lit } else { lit }])
					.is_err()
				{
					break;
				}
			}
			seen.sort();
			assert_eq!(seen, vec![(false, 0), (true, 5)]);
		}
	}

	#[test]
	fn a_group_of_distinct_coefficients_can_still_take_them() {
		// Every value is reached by exactly one term, so nothing forces a fresh
		// literal to stand for it.
		let mut cnf = Cnf::default();
		let lits: Vec<Lit> = (0..3).map(|_| cnf.new_lit()).collect();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: lits.clone(),
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();
		let group = lits
			.iter()
			.zip([2, 5, 7])
			.map(|(&l, c)| (l, PosCoeff::new(c)))
			.collect_vec();
		let t = Term::from_at_most_one(&mut cnf, &group, "x", false).unwrap();
		let x = &t.x;
		let _ = x.order_encoding(&mut cnf).unwrap();

		let mut slv = Cadical::from(&cnf);
		let mut reachable = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			reachable.push(
				lits.iter()
					.zip([2, 5, 7])
					.find(|(&l, _)| value.value(l))
					.map_or(0, |(_, c)| c),
			);
			let no_good: Vec<_> = lits
				.iter()
				.map(|&l| if value.value(l) { !l } else { l })
				.collect();
			if slv.add_clause(no_good).is_err() {
				break;
			}
		}
		reachable.sort();
		reachable.dedup();
		assert_eq!(
			reachable,
			vec![0, 2, 5, 7],
			"every term must still be choosable"
		);
	}

	#[test]
	fn a_group_on_its_own_is_bounded_on_its_own_literals() {
		// One term left and read directly: no literal says where the group
		// stands against the bound, so the values that break it are ruled out
		// one by one.
		for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
			for k in -1..=9 {
				let mut cnf = Cnf::default();
				let lits: Vec<Lit> = (0..3).map(|_| cnf.new_lit()).collect();
				PairwiseEncoder::default()
					.encode(
						&mut cnf,
						&CardinalityOne {
							lits: lits.clone(),
							cmp: LimitComp::LessEq,
						},
					)
					.unwrap();
				let group = lits
					.iter()
					.zip([2, 5, 7])
					.map(|(&l, c)| (l, PosCoeff::new(c)))
					.collect_vec();
				let t = Term::from_at_most_one(&mut cnf, &group, "x", true).unwrap();
				let mut enc = IntLinEncoder::default();
				let ok = enc
					.encode(&mut cnf, &IntLinear::new(vec![t.clone()], cmp, k))
					.is_ok();
				assert!(
					!t.x.has_order_encoding(),
					"read on the group's own literals"
				);

				let mut seen = Vec::new();
				if ok {
					let mut slv = Cadical::from(&cnf);
					while let SolveResult::Satisfied(value) = slv.solve() {
						seen.push(
							lits.iter()
								.zip([2, 5, 7])
								.find(|(&l, _)| value.value(l))
								.map_or(0, |(_, c)| c),
						);
						let no_good: Vec<_> = lits
							.iter()
							.map(|&l| if value.value(l) { !l } else { l })
							.collect();
						if slv.add_clause(no_good).is_err() {
							break;
						}
					}
				}
				seen.sort();
				seen.dedup();
				let expected: Vec<Coeff> = [0, 2, 5, 7]
					.into_iter()
					.filter(|&v| match cmp {
						Comparator::LessEq => v <= k,
						Comparator::Equal => v == k,
						Comparator::GreaterEq => v >= k,
					})
					.collect();
				assert_eq!(seen, expected, "group {cmp:?} {k}");
			}
		}
	}

	#[test]
	fn a_group_is_encoded_on_the_literals_it_arrived_on() {
		// The whole point of reading a group as an integer: the walk guards on
		// whichever view the group came with, so no second view is built and
		// nothing has to be channelled.
		let mut cnf = Cnf::default();
		let lits: Vec<Lit> = (0..3).map(|_| cnf.new_lit()).collect();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: lits.clone(),
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();
		let group = lits
			.iter()
			.zip([2, 5, 7])
			.map(|(&l, c)| (l, PosCoeff::new(c)))
			.collect_vec();
		let t = Term::from_at_most_one(&mut cnf, &group, "x", true).unwrap();
		let y = IntVar::new(0..=3).enforce_consistency(true).with_label("y");

		let mut enc = IntLinEncoder::default();
		let con = IntLinear::new(
			vec![t.clone(), Term::new(1, y.clone())],
			Comparator::LessEq,
			8,
		);
		enc.encode(&mut cnf, &con).unwrap();

		assert!(
			!t.x.has_order_encoding(),
			"the group came with a direct encoding and should be read on it"
		);

		// And it still encodes the constraint.
		let mut slv = Cadical::from(&cnf);
		let mut seen = Vec::new();
		let watched = cnf.get_variables();
		while let SolveResult::Satisfied(value) = slv.solve() {
			let group: Coeff = lits
				.iter()
				.zip([2, 5, 7])
				.find(|(&l, _)| value.value(l))
				.map_or(0, |(_, c)| c);
			seen.push((group, y.value(&value)));
			let no_good: Vec<_> = watched
				.map(|v| {
					let l = v.into();
					if value.value(l) {
						!l
					} else {
						l
					}
				})
				.collect();
			if slv.add_clause(no_good).is_err() {
				break;
			}
		}
		seen.sort();
		seen.dedup();
		let expected: Vec<(Coeff, Coeff)> = [0, 2, 5, 7]
			.into_iter()
			.flat_map(|g| (0..=3).map(move |v| (g, v)))
			.filter(|(g, v)| g + v <= 8)
			.collect();
		assert_eq!(seen, expected);
	}

	#[test]
	fn a_log_encoded_group_keeps_its_bits() {
		// The caller declared these literals to be the bits of an integer, so
		// the group is that integer: the bits are its encoding and the multiple
		// its coefficients are built from stays on the term.
		for multiple in [1, 3] {
			let mut cnf = Cnf::default();
			let lits: Vec<Lit> = (0..3).map(|_| cnf.new_lit()).collect();
			let terms = lits
				.iter()
				.enumerate()
				.map(|(i, &l)| (l, PosCoeff::new(multiple << i)))
				.collect_vec();
			// Bounds come already scaled by the multiple, as the aggregator
			// leaves them.
			let t = Term::from_binary_digits(
				&mut cnf,
				&terms,
				PosCoeff::new(2 * multiple),
				PosCoeff::new(5 * multiple),
				"x",
			)
			.unwrap();
			assert_eq!(t.c, multiple, "the multiple belongs on the term");
			assert_eq!((t.x.min(), t.x.max()), (2, 5), "the declared bounds hold");
			// The caller declared the bits stay within those bounds; asking for
			// them to be enforced is what makes that true of the encoding.
			t.x.constrain(&mut cnf).unwrap();
			assert!(
				!t.x.has_order_encoding(),
				"the bits are already there, so nothing should be channelled"
			);
			let vars_before = cnf.num_vars();
			let _ = t.x.binary_encoding(&mut cnf).unwrap();
			assert_eq!(
				cnf.num_vars(),
				vars_before,
				"the encoding should be the literals it was given"
			);

			// The group takes exactly the declared values, and the bits say
			// which.
			let mut slv = Cadical::from(&cnf);
			let mut seen = Vec::new();
			while let SolveResult::Satisfied(value) = slv.solve() {
				let bits: Coeff = lits
					.iter()
					.enumerate()
					.filter(|(_, &l)| value.value(l))
					.map(|(i, _)| 1 << i)
					.sum();
				assert_eq!(t.x.value(&value), bits, "the value is what the bits say");
				seen.push(bits);
				let no_good: Vec<_> = lits
					.iter()
					.map(|&l| if value.value(l) { !l } else { l })
					.collect();
				if slv.add_clause(no_good).is_err() {
					break;
				}
			}
			seen.sort();
			assert_eq!(seen, vec![2, 3, 4, 5], "multiple {multiple}");
		}
	}

	#[test]
	fn a_constraint_without_terms_compares_zero() {
		// The empty sum is zero, so whether it holds is decided outright. It is
		// reached by construction rather than through the walk over the terms,
		// which is why it is worth checking on its own.
		for (cmp, k, holds) in [
			(Comparator::LessEq, 0, true),
			(Comparator::LessEq, -1, false),
			(Comparator::LessEq, 1, true),
			(Comparator::GreaterEq, 0, true),
			(Comparator::GreaterEq, 1, false),
			(Comparator::GreaterEq, -1, true),
			(Comparator::Equal, 0, true),
			(Comparator::Equal, 2, false),
		] {
			let mut cnf = Cnf::default();
			let mut enc = IntLinEncoder::default();
			let con = IntLinear::new(Vec::new(), cmp, k);
			assert_eq!(
				enc.encode(&mut cnf, &con).is_ok(),
				holds,
				"0 {cmp:?} {k} should be {holds}"
			);
		}
	}

	#[test]
	fn a_single_term_is_bounded_directly() {
		let domain = RangeList::from_elements([-2, 0, 3, 4]);
		for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
			for c in [-3, -1, 1, 2] {
				for k in -8..=8 {
					assert_eq!(
						solutions_of(&[c], std::slice::from_ref(&domain), cmp, k, false),
						brute_force(&[c], std::slice::from_ref(&domain), cmp, k),
						"{c}·x {cmp:?} {k}"
					);
				}
			}
		}
	}

	#[test]
	fn binary_variables_admit_exactly_the_solutions() {
		// `Some(0)` puts every variable in binary, so the same constraints run
		// through the binary bound and adder paths instead of the term walk.
		let contiguous = RangeList::from(0..=3);
		let holey = RangeList::from_elements([0, 1, 3]);
		let wide = RangeList::from(2..=9);
		let cases: Vec<(Vec<Coeff>, Vec<RangeList<Coeff>>)> = vec![
			(vec![1], vec![contiguous.clone()]),
			(vec![-2], vec![holey.clone()]),
			(vec![3], vec![wide.clone()]),
			(vec![1, 1], vec![contiguous.clone(), contiguous.clone()]),
			(vec![1, 1, -1], vec![contiguous.clone(), contiguous, wide]),
			(vec![1, 1, -1], vec![holey.clone(), holey.clone(), holey]),
		];
		for (coeffs, doms) in cases {
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				for k in -4..=8 {
					assert_eq!(
						solutions_with(&coeffs, &doms, cmp, k, false, Some(0)).0,
						brute_force(&coeffs, &doms, cmp, k),
						"{coeffs:?} {cmp:?} {k} over {doms:?} in binary"
					);
				}
			}
		}
	}

	#[test]
	fn the_walk_drops_the_steps_it_repeats() {
		// Clause counts for these, with the repeated steps kept, are 42, 42, 86
		// and 33. The bounds below sit between the two, so they catch the walk
		// emitting every step again without pinning an exact encoding.
		for (coeffs, span, k, budget) in [
			(vec![1, 1, 1], 5, 7, 40),
			(vec![2, 3, 5], 7, 12, 30),
			(vec![1, 2, 4, 8], 4, 15, 40),
			(vec![3, 3, 3], 9, 14, 30),
		] {
			let doms = vec![RangeList::from(0..=span); coeffs.len()];
			let mut cnf = Cnf::default();
			let mut enc = IntLinEncoder::default();
			let xs = doms
				.iter()
				.enumerate()
				.map(|(i, d)| IntVar::new(d.clone()).with_label(format!("x{i}")))
				.collect_vec();
			let terms = coeffs
				.iter()
				.zip(&xs)
				.map(|(&c, x)| Term::new(c, x.clone()))
				.collect_vec();
			enc.encode(&mut cnf, &IntLinear::new(terms, Comparator::LessEq, k))
				.unwrap();
			assert!(
				cnf.num_clauses() <= budget,
				"{coeffs:?} <= {k} over 0..{span} took {} clauses, over the {budget} expected",
				cnf.num_clauses()
			);
		}
	}

	#[test]
	fn coefficients_decompose_into_shifts_and_adders() {
		// The database this replaces stopped at a hundred, so the point of
		// synthesising a plan instead is that nothing here is out of reach.
		let domain = RangeList::from(0..=7);
		for c in [
			1, 2, 3, 5, 7, 9, 11, 15, 23, 45, 99, 101, 127, 255, 341, 569, 1023,
		] {
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				// Around each value the product can take, and just off it.
				for k in (0..=7).flat_map(|v: Coeff| [c * v - 1, c * v, c * v + 1]) {
					let (solutions, xs) =
						solutions_with(&[c], std::slice::from_ref(&domain), cmp, k, false, Some(0));
					assert_eq!(
						solutions,
						brute_force(&[c], std::slice::from_ref(&domain), cmp, k),
						"{c}·x {cmp:?} {k}"
					);
					assert!(
						!xs.iter().any(|x| x.has_order_encoding()),
						"{c}·x {cmp:?} {k} fell back to the walk"
					);
				}
			}
		}
	}

	#[test]
	fn a_sum_that_is_negative_throughout_reads_positive() {
		let doms = [RangeList::from(0..=3), RangeList::from_elements([1, 2, 5])];
		for coeffs in [vec![-1, -1], vec![-3, -5], vec![-1, -45]] {
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				for k in (-14..=2).map(|v: Coeff| v * 7) {
					let (solutions, xs) = solutions_with(&coeffs, &doms, cmp, k, false, Some(0));
					assert_eq!(
						solutions,
						brute_force(&coeffs, &doms, cmp, k),
						"{coeffs:?} {cmp:?} {k}"
					);
					assert!(
						!xs.iter().any(|x| x.has_order_encoding()),
						"{coeffs:?} {cmp:?} {k} fell back to the walk"
					);
				}
			}
		}
	}

	#[test]
	fn products_combine_with_each_other() {
		let doms = [
			RangeList::from(0..=3),
			RangeList::from_elements([0, 1, 4]),
			RangeList::from(2..=5),
		];
		for coeffs in [
			vec![3, 5, 7],
			vec![1, 45, 2],
			vec![11, 11, 11],
			vec![101, 1, 23],
		] {
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				for k in (0..=12).map(|v: Coeff| v * 13) {
					assert_eq!(
						solutions_with(&coeffs, &doms, cmp, k, false, Some(0)).0,
						brute_force(&coeffs, &doms, cmp, k),
						"{coeffs:?} {cmp:?} {k}"
					);
				}
			}
		}
	}

	#[test]
	fn a_product_is_shared_between_encoders() {
		// The product belongs to the variable, not to whichever encoder
		// happened to build it, so a second encoder — of any kind — finds it
		// already there.
		let domain = RangeList::from(0..=15);
		let mut cnf = Cnf::default();
		let x = IntVar::new(domain).with_label("x");
		let con = |k| IntLinear::new(vec![Term::new(45, x.clone())], Comparator::LessEq, k);
		let config = || IntLinConfig {
			propagate: false,
			cutoff: Some(0),
		};

		IntLinEncoder::with_config(config())
			.encode(&mut cnf, &con(300))
			.unwrap();
		let vars = cnf.num_vars();
		// A different encoder entirely, with no memory of the first.
		IntLinEncoder::with_config(config())
			.encode(&mut cnf, &con(200))
			.unwrap();
		assert_eq!(
			cnf.num_vars(),
			vars,
			"the second encoder should find the product on the variable"
		);
	}

	#[test]
	fn a_product_is_built_once() {
		// The same coefficient over the same variable, in two constraints. The
		// second should cost nothing beyond its own bound.
		let domain = RangeList::from(0..=15);
		let mut cnf = Cnf::default();
		let mut enc = IntLinEncoder::with_config(IntLinConfig {
			propagate: false,
			cutoff: Some(0),
		});
		let x = IntVar::new(domain).with_label("x");

		let con = |k| IntLinear::new(vec![Term::new(45, x.clone())], Comparator::LessEq, k);
		enc.encode(&mut cnf, &con(300)).unwrap();
		let (vars, clauses) = (cnf.num_vars(), cnf.num_clauses());
		enc.encode(&mut cnf, &con(200)).unwrap();

		assert_eq!(
			cnf.num_vars(),
			vars,
			"the second constraint should reuse the product, not rebuild it"
		);
		assert!(
			cnf.num_clauses() - clauses < 10,
			"the second constraint added {} clauses, so more than a bound",
			cnf.num_clauses() - clauses
		);
	}

	#[test]
	fn binary_sums_chain_into_adders() {
		// Several binary variables added together go through a chain of adders
		// and one bound, rather than the walk over terms.
		let cases: Vec<Vec<RangeList<Coeff>>> = vec![
			vec![RangeList::from(0..=3); 3],
			vec![RangeList::from(0..=1); 4],
			vec![
				RangeList::from(2..=5),
				RangeList::from_elements([0, 1, 4]),
				RangeList::from(1..=3),
			],
			vec![
				RangeList::from(-3..=0),
				RangeList::from(1..=2),
				RangeList::from_elements([-1, 5]),
			],
		];
		for doms in cases {
			let coeffs = vec![1; doms.len()];
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				for k in -4..=10 {
					let (solutions, xs) = solutions_with(&coeffs, &doms, cmp, k, false, Some(0));
					assert_eq!(
						solutions,
						brute_force(&coeffs, &doms, cmp, k),
						"sum of {doms:?} {cmp:?} {k}"
					);
					// Had the chain declined, the walk would have taken the
					// constraint and channelled every variable to order form.
					assert!(
						!xs.iter().any(|x| x.has_order_encoding()),
						"sum of {doms:?} {cmp:?} {k} fell back to the walk"
					);
				}
			}
		}
	}

	#[test]
	fn an_addition_lines_up_with_the_bound_of_its_result() {
		// `x + y = z` is only handed to the adder when `z` starts where the sum
		// of the other two does; otherwise the term walk has to take it, and
		// either way the solutions are the same.
		let from = |lb: Coeff| RangeList::from(lb..=(lb + 3));
		for (lx, ly, lz) in [(0, 0, 0), (1, 2, 3), (1, 2, 0), (-2, 1, -1), (-2, 1, 5)] {
			let doms = [from(lx), from(ly), from(lz)];
			assert_eq!(
				solutions_with(&[1, 1, -1], &doms, Comparator::Equal, 0, false, Some(0)).0,
				brute_force(&[1, 1, -1], &doms, Comparator::Equal, 0),
				"x+y=z over lower bounds {lx}, {ly}, {lz}"
			);
		}
	}

	#[test]
	fn an_addition_bounds_a_result_wider_than_its_inputs() {
		// The result has room for far more than the inputs can reach, so its
		// top bits are only driven to zero if the adder is sized by the widest
		// of the three rather than by its inputs.
		let doms = [
			RangeList::from(0..=1),
			RangeList::from(0..=1),
			RangeList::from(0..=15),
		];
		assert_eq!(
			solutions_with(&[1, 1, -1], &doms, Comparator::Equal, 0, false, Some(0)).0,
			brute_force(&[1, 1, -1], &doms, Comparator::Equal, 0),
		);
	}

	#[test]
	fn propagation_narrows_the_domains_it_can() {
		// `3x + y ≤ 5` with `y ≥ 0` leaves `x` no room above one.
		let mut enc = IntLinEncoder::default();
		let domain = RangeList::from(0..=3);
		let (x, y) = (
			IntVar::new(domain.clone()).with_label("x"),
			IntVar::new(domain).with_label("y"),
		);
		let con = IntLinear::new(
			vec![Term::new(3, x.clone()), Term::new(1, y.clone())],
			Comparator::LessEq,
			5,
		);

		let mut cnf = Cnf::default();
		enc.encode(&mut cnf, &con).unwrap();
		assert_eq!(x.max(), 1, "3x ≤ 5 leaves x at most one");
		assert_eq!(y.max(), 3, "y is already tight");
	}
}
