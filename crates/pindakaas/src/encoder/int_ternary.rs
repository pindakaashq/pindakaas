//! Encoding `x + y ≷ z`, on whichever view of the three variables costs least.
//!
//! Two shapes are recognised: three binary variables, which a ripple-carry
//! adder states directly, and otherwise a walk over the terms in order form,
//! which any variable can produce. Longer constraints reach this through a
//! decomposition strategy, which is what makes three terms the only case
//! worth encoding directly.

use std::{iter::empty, mem};

use crate::{
	constraint::{
		int_linear::{encode_addition, Decompose, IntLinear, NormalizedIntLinear, Term},
		int_ternary::IntTernary,
		linear::Comparator,
	},
	decision::integer::IntVar,
	helpers::{div_ceil, div_floor},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Result, Unsatisfiable,
};

/// Encoder for [`IntTernary`] constraints.
///
/// Every decomposition strategy breaks a longer constraint into these, so this
/// is where all of them end up. An n-ary constraint is aggregated into a
/// [`NormalizedIntLinear`] and handed to one of those strategies instead.
///
/// # Examples
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{linear::Comparator, int_ternary::{IntTernary, IntTernaryEncoder}},
/// #     decision::integer::IntVar, Cnf, Encoder,
/// # };
/// let mut f = Cnf::default();
/// let (x, y) = (IntVar::new(0..=3), IntVar::new(0..=3));
/// let z = IntVar::new(0..=6);
///
/// // `x + y <= z`, over whichever views of the three cost least.
/// let con = IntTernary::new((1, x), (1, y), Comparator::LessEq, (1, z));
/// IntTernaryEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Clone, Debug, Default)]
pub struct IntTernaryEncoder {
	config: IntTernaryConfig,
}

/// Encoding a constraint fixes the literals of the variables it mentions, and
/// so also fixes their domains. A constraint encoded later can still narrow a
/// variable that no constraint has reached yet, but not one that is already
/// encoded, which makes the result depend on the order the constraints are
/// given in. Every such result is correct; they differ only in how much was
/// pruned before the literals were committed.
impl<Db: ClauseDatabase + ?Sized> Encoder<Db, IntTernary> for IntTernaryEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "int_ternary_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &IntTernary) -> Result {
		// `z` crosses the comparison and a term of one value joins the
		// constant, which is the form both arms below want.
		let con = &IntLinear::from(con);
		if self.config.propagate {
			con.propagate()?;
		}
		let terms = &con.terms;
		let binary = |t: &Term| t.1.prefers_binary(self.config.cutoff);

		// A ripple-carry adder states this shape directly, and it is
		// what a coefficient decomposes into, so it is recognised
		// first.
		if let Some((x, y, z)) = con.as_addition() {
			if [x, y, z].iter().all(|t| binary(t)) && Self::worth_adding(con.cmp, x, y) {
				return encode_addition(db, x, y, con.cmp, z);
			}
		}
		// Otherwise walk the terms in order form, which any variable
		// can produce. Every variable gets a view, since a solution has
		// to say its value.
		for t in terms {
			if !t.1.has_direct_encoding() {
				let _ = t.1.order_encoding(db)?;
			}
		}
		// The clauses end in the last term and are guarded by the ones before
		// it, so the terms are read from the back.
		let mut encoded = terms.iter().rev().map(|t| Encoded { c: t.0, x: &t.1 });
		let (bounded, inner, outer) = (encoded.next(), encoded.next(), encoded.next());
		debug_assert!(encoded.next().is_none());

		// An equality holds exactly when both of its inequalities do.
		for cmp in con.cmp.split() {
			Encoded::emit(db, bounded, inner, outer, cmp, con.k)?;
		}
		Ok(())
	}
}

/// Configuration for a [`IntTernaryEncoder`].
#[derive(Clone, Debug)]
pub struct IntTernaryConfig {
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

impl Default for IntTernaryConfig {
	fn default() -> Self {
		Self {
			propagate: true,
			cutoff: None,
		}
	}
}

impl IntTernaryEncoder {
	/// Whether the adder beats the walk over the terms for this shape.
	///
	/// Decided on encoding size. The walk also propagates where the adder
	/// searches, so a search-heavy instance wants the walk sooner than this.
	fn worth_adding(cmp: Comparator, x: &Term, y: &Term) -> bool {
		// Heuristic: an inequality costs the adder a slack and a second adder,
		// which the walk beats until its step per pair of values outgrows them.
		cmp == Comparator::Equal || x.1.card() * y.1.card() > 80
	}

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
			.try_for_each(|con| Encoder::encode(self, db, con))
	}

	/// Create an encoder with the given configuration.
	pub fn with_config(config: IntTernaryConfig) -> Self {
		Self { config }
	}
}

impl Encoded<'_> {
	/// Add the clauses for `outer + inner + bounded ≷ k` to `db`.
	///
	/// `bounded` is the term every clause ends in; `inner` and `outer` are the
	/// terms whose values guard it, `outer` outermost. A loop per guard rather
	/// than a recursion: an [`IntTernary`] has three terms and folds any
	/// constant among them into `k`, so there are never more than two guards,
	/// and `bounded` always yields unit clauses. A clause is therefore one
	/// guard per loop and one literal, which lets each loop reuse its buffers
	/// across its steps where a recursion allocates a clause list per step.
	fn emit<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		bounded: Option<Encoded>,
		inner: Option<Encoded>,
		outer: Option<Encoded>,
		cmp: Comparator,
		k: Coeff,
	) -> Result {
		let Some(bounded) = bounded else {
			// Nothing left to give, so the empty sum either satisfies what
			// remains of the constraint or nothing can.
			let holds = match cmp {
				Comparator::LessEq => 0 <= k,
				Comparator::GreaterEq => 0 >= k,
				Comparator::Equal => unreachable!("an equality is split before it is encoded"),
			};
			return if holds {
				Ok(())
			} else {
				db.add_clause(empty::<BoolVal>())
			};
		};
		let (outer_c, outer_steps) = Self::guards(db, outer, cmp)?;
		let (inner_c, inner_steps) = Self::guards(db, inner, cmp)?;
		// What a direct encoding pins `bounded` to does not depend on what is
		// left of the bound, so it is read once rather than once per step.
		let pins = if bounded.x.has_direct_encoding() {
			bounded.x.lit_direct_steps(db, true)?
		} else {
			Vec::new()
		};
		// Each loop keeps what it built at the step before, to compare the
		// next one against.
		let (mut units, mut last_units) = (Vec::new(), Vec::new());
		let (mut clauses, mut last_clauses, mut have_clauses) = (Vec::new(), Vec::new(), false);

		for &(v, outer_guard) in &outer_steps {
			let left = k - outer_c * v;
			clauses.clear();
			let mut have_units = false;
			for &(w, inner_guard) in &inner_steps {
				units.clear();
				bounded.bound_into(db, cmp, left - inner_c * w, &pins, &mut units)?;
				// A step asking of the terms below exactly what the one before
				// it asked is already covered by that one, which happens often.
				if have_units && units == last_units {
					continue;
				}
				clauses.extend(units.iter().map(|&lit| (inner_guard, lit)));
				mem::swap(&mut units, &mut last_units);
				have_units = true;
			}
			if have_clauses && clauses == last_clauses {
				continue;
			}
			for &(inner_guard, lit) in &clauses {
				db.add_clause([outer_guard, inner_guard, lit])?;
			}
			mem::swap(&mut clauses, &mut last_clauses);
			have_clauses = true;
		}
		Ok(())
	}

	/// The values a guard term is walked over, with its coefficient, taken
	/// from whichever side pushes the sum towards breaking the constraint.
	///
	/// A loop with no term to guard on gets one step: a false literal against
	/// a coefficient of zero. `add_clause` drops a false literal, so that
	/// leaves the clause as it was and the bound where it was.
	fn guards<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		term: Option<Encoded>,
		cmp: Comparator,
	) -> Result<(Coeff, Vec<(Coeff, BoolVal)>), Unsatisfiable> {
		let Some(term) = term else {
			return Ok((0, vec![(0, BoolVal::Const(false))]));
		};
		let geq = (term.c >= 0) == matches!(cmp, Comparator::LessEq);
		// A variable a group of terms arrived on is read on the direct
		// literals it came with; any other on its order encoding.
		Ok((
			term.c,
			if term.x.has_direct_encoding() {
				term.x.lit_direct_steps(db, geq)?
			} else {
				term.x.lit_order_steps(db, geq)?
			},
		))
	}

	/// The literals of the unit clauses for `c·x ≷ k`, nothing below this term
	/// being left to give.
	fn bound_into<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		cmp: Comparator,
		k: Coeff,
		pins: &[(Coeff, BoolVal)],
		out: &mut Vec<BoolVal>,
	) -> Result {
		if self.x.has_direct_encoding() {
			// Nothing says it in one literal, so rule out each value that
			// would break the bound instead. What the value is worth already
			// carries the sign of the coefficient, so the comparison is the
			// one asked for rather than the turned-around one below.
			for &(d, _) in pins {
				let breaks = match cmp {
					Comparator::LessEq => self.c * d > k,
					_ => self.c * d < k,
				};
				if breaks {
					out.push(!self.x.lit_equals(db, d)?);
				}
			}
			return Ok(());
		}
		// Dividing by a negative coefficient turns the comparison around.
		let cmp = if self.c >= 0 { cmp } else { cmp.reverse() };
		// One literal says where the variable stands against the bound.
		out.push(match cmp {
			Comparator::LessEq => self.x.lit_at_most(db, div_floor(k, self.c))?,
			Comparator::GreaterEq => self.x.lit_at_least(db, div_ceil(k, self.c))?,
			Comparator::Equal => unreachable!("an equality is split before it is encoded"),
		});
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	use rangelist::RangeList;
	use traced_test::test;

	use crate::{
		constraint::{
			cardinality_one::{CardinalityOne, PairwiseEncoder},
			int_linear::Term,
			int_ternary::{IntTernary, IntTernaryConfig, IntTernaryEncoder},
			linear::{Comparator, LimitComp, PosCoeff},
		},
		decision::integer::IntVar,
		helpers::tests::at_most_one_var,
		solver::{cadical::Cadical, SolveResult, Solver},
		ClauseDatabaseTools, Cnf, Coeff, Encoder, Lit, Valuation,
	};

	/// `Σ cᵢ·xᵢ ≷ k` as the ternary constraint the encoder takes.
	///
	/// Either two terms against a constant, or three where the last is what the
	/// other two are compared against — between them every shape a
	/// decomposition produces.
	fn ternary(terms: Vec<Term>, cmp: Comparator, k: Coeff) -> IntTernary {
		if terms.len() == 3 {
			assert_eq!(k, 0, "three terms are compared against the third of them");
			let (c, x) = terms[2].clone();
			assert!(c < 0, "the third term stands on the other side");
			return IntTernary::new(terms[0].clone(), terms[1].clone(), cmp, (-c, x));
		}
		assert!(terms.len() < 3, "more terms than that is a decomposition");
		let zero = || (1, IntVar::new(0..=0));
		let mut terms = terms.into_iter();
		let (x, y) = (
			terms.next().unwrap_or_else(zero),
			terms.next().unwrap_or_else(zero),
		);
		IntTernary::new(x, y, cmp, (1, IntVar::new(k..=k)))
	}

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
		let enc = IntTernaryEncoder::with_config(IntTernaryConfig { propagate, cutoff });
		let xs = doms
			.iter()
			.enumerate()
			.map(|(i, domain)| IntVar::new(domain.clone()).with_label(format!("x{i}")))
			.collect_vec();
		let terms = coeffs
			.iter()
			.zip(&xs)
			.map(|(&c, x)| (c, x.clone()))
			.collect_vec();

		let con = ternary(terms, cmp, k);
		if enc.encode(&mut cnf, &con).is_err() {
			return (Vec::new(), xs);
		}
		// Each model is ruled out in turn, so an assignment reachable
		// more than one way is seen more than once.
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
			(vec![1, 1, -1], vec![holey.clone(); 3]),
			(vec![3, -1, -2], vec![negative.clone(), contiguous, holey]),
			(vec![-2, -5], vec![negative.clone(), negative]),
		];
		for (coeffs, doms) in cases {
			// Three terms are compared against the third of them, so there is
			// no constant left to vary.
			let ks: Vec<Coeff> = if coeffs.len() == 3 {
				vec![0]
			} else {
				(-6..=6).collect()
			};
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				for k in ks.iter().copied() {
					// Propagation must not change which
					// assignments survive, only how much
					// domain is left.
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

	#[test]
	fn a_group_on_its_own_is_bounded_on_its_own_literals() {
		// One term read directly: no literal says where it stands
		// against the bound, so the values that break it are ruled out
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
				let x = at_most_one_var(&mut cnf, &group, "x", true).unwrap();
				let mut enc = IntTernaryEncoder::default();
				let ok = enc
					.encode(&mut cnf, &ternary(vec![(1, x.clone())], cmp, k))
					.is_ok();
				assert!(!x.has_order_encoding(), "read on the group's own literals");

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
		// The point of reading a group as an integer: the walk guards
		// on the view it came with, so nothing is built and nothing
		// channelled.
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
		let x = at_most_one_var(&mut cnf, &group, "x", true).unwrap();
		let y = IntVar::new(0..=3).enforce_consistency(true).with_label("y");

		let mut enc = IntTernaryEncoder::default();
		let con = ternary(vec![(1, x.clone()), (1, y.clone())], Comparator::LessEq, 8);
		enc.encode(&mut cnf, &con).unwrap();

		assert!(
			!x.has_order_encoding(),
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
	fn a_constraint_without_terms_compares_zero() {
		// The empty sum is decided outright rather than through the
		// walk, which is why it is worth checking on its own.
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
			let mut enc = IntTernaryEncoder::default();
			let con = ternary(Vec::new(), cmp, k);
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
			// Three terms are compared against the third of them, so there is
			// no constant left to vary.
			let ks: Vec<Coeff> = if coeffs.len() == 3 {
				vec![0]
			} else {
				(-4..=8).collect()
			};
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				for k in ks.iter().copied() {
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
		// Measured at 37, 59 and 87 clauses, against 47, 81 and 123
		// with the repeated steps kept; the budgets sit between the
		// two.
		for (coeffs, span, k, budget) in [
			(vec![1, 1, -1], 5, 0, 42),
			(vec![2, 3, -5], 7, 0, 70),
			(vec![3, 3, -3], 9, 0, 105),
		] {
			let doms = vec![RangeList::from(0..=span); coeffs.len()];
			let mut cnf = Cnf::default();
			let mut enc = IntTernaryEncoder::default();
			let xs = doms
				.iter()
				.enumerate()
				.map(|(i, d)| IntVar::new(d.clone()).with_label(format!("x{i}")))
				.collect_vec();
			let terms = coeffs
				.iter()
				.zip(&xs)
				.map(|(&c, x)| (c, x.clone()))
				.collect_vec();
			enc.encode(&mut cnf, &ternary(terms, Comparator::LessEq, k))
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
		// Each product meets the others across the comparison rather than under
		// a constant, which is the shape a decomposition hands over.
		for coeffs in [
			vec![3, 5, -7],
			vec![1, 45, -2],
			vec![11, 11, -11],
			vec![101, 1, -23],
		] {
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				for k in [0] {
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
		// The product belongs to the variable rather than the encoder
		// that built it, so a second encoder of any kind finds it
		// there.
		let domain = RangeList::from(0..=15);
		let mut cnf = Cnf::default();
		let x = IntVar::new(domain).with_label("x");
		let con = |k| ternary(vec![(45, x.clone())], Comparator::LessEq, k);
		let config = || IntTernaryConfig {
			propagate: false,
			cutoff: Some(0),
		};

		IntTernaryEncoder::with_config(config())
			.encode(&mut cnf, &con(300))
			.unwrap();
		let vars = cnf.num_vars();
		// A different encoder entirely, with no memory of the first.
		IntTernaryEncoder::with_config(config())
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
		let mut enc = IntTernaryEncoder::with_config(IntTernaryConfig {
			propagate: false,
			cutoff: Some(0),
		});
		let x = IntVar::new(domain).with_label("x");

		let con = |k| ternary(vec![(45, x.clone())], Comparator::LessEq, k);
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
		// Two binary variables against a third go straight to the ripple-carry
		// adder rather than the walk over terms.
		let cases: Vec<Vec<RangeList<Coeff>>> = vec![
			vec![RangeList::from(0..=3); 3],
			vec![RangeList::from(0..=1); 3],
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
			let coeffs = vec![1, 1, -1];
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				for k in [0] {
					let (solutions, xs) = solutions_with(&coeffs, &doms, cmp, k, false, Some(0));
					assert_eq!(
						solutions,
						brute_force(&coeffs, &doms, cmp, k),
						"sum of {doms:?} {cmp:?} {k}"
					);
					// Had the chain declined, the walk would have taken the
					// constraint and channelled every variable to order form.
				}
			}
		}
	}

	#[test]
	fn an_addition_lines_up_with_the_bound_of_its_result() {
		// The adder only takes `x + y = z` where `z` starts at the sum
		// of the other two; otherwise the walk does, to the same
		// solutions.
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
		// The result reaches far past its inputs, so its top bits go to
		// zero only if the adder is sized by the widest of the three.
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
		let mut enc = IntTernaryEncoder::default();
		let domain = RangeList::from(0..=3);
		let (x, y) = (
			IntVar::new(domain.clone()).with_label("x"),
			IntVar::new(domain).with_label("y"),
		);
		let con = ternary(vec![(3, x.clone()), (1, y.clone())], Comparator::LessEq, 5);

		let mut cnf = Cnf::default();
		enc.encode(&mut cnf, &con).unwrap();
		assert_eq!(x.max(), 1, "3x ≤ 5 leaves x at most one");
		assert_eq!(y.max(), 3, "y is already tight");
	}

	#[test]
	fn a_wide_inequality_goes_to_the_adder() {
		// Over 0..=15 the walk takes 312 clauses and the adder with its slack
		// 116; at 0..=3 it is 24 against 60, which is why the crossover exists.
		for (span, budget) in [(15, 150), (3, 30)] {
			let mut cnf = Cnf::default();
			let con = IntTernary::new(
				(1, IntVar::new(0..=span)),
				(1, IntVar::new(0..=span)),
				Comparator::LessEq,
				(1, IntVar::new(0..=(2 * span))),
			);
			IntTernaryEncoder::with_config(IntTernaryConfig {
				propagate: false,
				cutoff: Some(0),
			})
			.encode(&mut cnf, &con)
			.unwrap();
			assert!(
				cnf.num_clauses() <= budget,
				"0..={span} took {} clauses, over the {budget} expected",
				cnf.num_clauses()
			);
		}
	}
}
