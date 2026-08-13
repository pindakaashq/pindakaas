use std::{
	hash::{Hash, Hasher},
	num::NonZero,
	rc::{Rc, Weak},
};

use rangelist::RangeList;
use rustc_hash::FxHashMap;

use crate::{
	bool_linear::{AdderEncoder, Comparator},
	helpers::{
		div_ceil, div_floor,
		scm::{ScmObjective, ScmOperation, ScmSolution},
		shifted,
	},
	integer::var::{BinEnc, IntVar, OrdEnc},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Result, Unsatisfiable,
};

impl Eq for VarKey {}

impl Hash for VarKey {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.0.as_ptr().hash(state);
	}
}

impl PartialEq for VarKey {
	fn eq(&self, other: &Self) -> bool {
		Weak::ptr_eq(&self.0, &other.0)
	}
}

/// A linear constraint over integer variables, `Σ cᵢ·xᵢ ≷ k`.
#[derive(Clone, Debug)]
pub(crate) struct IntLinear {
	exp: IntLinExp,
	cmp: Comparator,
	k: Coeff,
}

/// Encoder for [`IntLinear`] constraints.
///
/// The encoder is kept between constraints so that what it learns about a
/// variable while encoding one is available to the next: the encodings a
/// variable has been given, and later the products built for its coefficients.
#[derive(Clone, Debug, Default)]
pub(crate) struct IntLinEncoder {
	config: IntLinConfig,
	/// The bits of `c·(x − lb)` for products already built, so that a
	/// coefficient met again — in this constraint or a later one — costs
	/// nothing, and so that a synthesis shares the steps it has in common with
	/// one already done.
	///
	/// Only ever looked up, never iterated: the keys are addresses, and their
	/// order would differ between runs.
	products: FxHashMap<(VarKey, Coeff), Vec<BoolVal>>,
}

/// An integer variable, as the identity of one rather than a hold on it.
///
/// A `Weak` keeps the allocation alive after the variable itself is dropped, so
/// its address cannot be handed to a later variable while this key still exists
/// — which a raw pointer could not promise.
#[derive(Clone, Debug)]
struct VarKey(Weak<IntVar>);

/// Configuration for an [`IntLinEncoder`].
#[derive(Clone, Debug)]
pub(crate) struct IntLinConfig {
	/// Whether to narrow the domains of the variables of a constraint before
	/// encoding it.
	pub propagate: bool,
	/// The domain size from which a variable is held in binary rather than in
	/// order form. `None` keeps every variable in order form.
	pub cutoff: Option<Coeff>,
}

/// A term of a constraint, together with the encoding of its variable.
///
/// Materialising every encoding before the clauses are built keeps the walk
/// over the terms a pure function of what is already there.
#[derive(Clone, Copy, Debug)]
struct Encoded<'a> {
	c: Coeff,
	ord: &'a OrdEnc,
}

/// A sum of integer terms.
#[derive(Clone, Debug, Default)]
pub(crate) struct IntLinExp {
	terms: Vec<Term>,
}

/// An integer variable scaled by a coefficient.
#[derive(Clone, Debug)]
pub(crate) struct Term {
	c: Coeff,
	x: Rc<IntVar>,
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
	/// Encode `con`, adding the clauses to `db`.
	///
	/// Encoding a constraint fixes the literals of the variables it mentions,
	/// and so also fixes their domains. A constraint encoded later can still
	/// narrow a variable that no constraint has reached yet, but not one that
	/// is already encoded, which makes the result depend on the order the
	/// constraints are given in. Every such result is correct; they differ only
	/// in how much was pruned before the literals were committed.
	pub(crate) fn encode<Db: ClauseDatabase + ?Sized>(
		&mut self,
		db: &mut Db,
		con: &IntLinear,
	) -> Result {
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
				let dom = RangeList::from_iter([reach(Term::lb)..=reach(Term::ub)]);
				return cmp
					.split()
					.into_iter()
					.try_for_each(|cmp| total.encode_bound(db, cmp, k, &dom));
			}
		}

		// Otherwise walk the terms in order form. Any variable can produce an
		// order encoding, channelling to one it already has if need be, so this
		// is always available even where it is not the cheapest.
		let ords: Vec<OrdEnc> = terms
			.iter()
			.map(|t| t.x.ord(db))
			.collect::<Result<_, _>>()?;
		let encoded: Vec<Encoded> = terms
			.iter()
			.zip(&ords)
			.map(|(t, ord)| Encoded { c: t.c, ord })
			.collect();

		// An equality holds exactly when both of its inequalities do.
		for cmp in con.cmp.split() {
			for clause in Encoded::walk(&encoded, cmp, con.k) {
				db.add_clause(clause)?;
			}
		}
		Ok(())
	}

	/// The encoding of `Σ cᵢ·xᵢ`, or `None` if some coefficient cannot be
	/// decomposed into shifts and adders.
	fn binary_sum<Db: ClauseDatabase + ?Sized>(
		&mut self,
		db: &mut Db,
		terms: &[Term],
	) -> Result<Option<BinEnc>, Unsatisfiable> {
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
		Ok(Some(BinEnc::from_bits(
			total.unwrap_or_default(),
			terms.iter().map(Term::lb).sum(),
		)))
	}

	/// The bits of `c·(x − lb)`, built from shifts and adders.
	///
	/// A shift costs nothing, being leading zero bits on the vector, so what is
	/// left is to find the fewest additions that reach `c`. That is the
	/// single-constant multiplication problem, and [`ScmSolution::synthesize`]
	/// plans it.
	fn scaled_bits<Db: ClauseDatabase + ?Sized>(
		&mut self,
		db: &mut Db,
		x: &Rc<IntVar>,
		c: Coeff,
	) -> Result<Option<Vec<BoolVal>>, Unsatisfiable> {
		debug_assert!(c > 0, "a product is decomposed only for a positive factor");
		let key = (VarKey(Rc::downgrade(x)), c);
		if let Some(bits) = self.products.get(&key) {
			return Ok(Some(bits.clone()));
		}
		let Ok(c32) = u32::try_from(c) else {
			return Ok(None);
		};
		let input = x.bin(db)?.to_vec();
		let Some(width) = NonZero::new(input.len() as u32) else {
			// A variable of one value contributes nothing to the sum.
			return Ok(Some(Vec::new()));
		};

		// Every step of the plan names what it computes by the factor it
		// reaches, which is the same thing the cache is keyed on, so a step
		// shared with an earlier synthesis is picked up rather than rebuilt.
		let plan = ScmSolution::synthesize(c32, ScmObjective::MinAdders(width));
		let _ = self.products.insert((VarKey(Rc::downgrade(x)), 1), input);
		for op in plan.operations {
			let factor = Coeff::from(op.result().get());
			if self
				.products
				.contains_key(&(VarKey(Rc::downgrade(x)), factor))
			{
				continue;
			}
			let bits = match op {
				ScmOperation::ShiftLeft { source, shift } => {
					shifted(&self.product(x, source.get()), shift)
				}
				ScmOperation::ShiftAdd { left, right, shift } => {
					let left = shifted(&self.product(x, left.get()), shift);
					AdderEncoder::ripple_carry_adder(
						db,
						&left,
						&self.product(x, right.get()),
						None,
						None,
					)?
				}
				ScmOperation::ShiftSub { left, right, shift } => {
					let left = shifted(&self.product(x, left.get()), shift);
					self.difference(db, &left, &self.product(x, right.get()), factor, &width)?
				}
				ScmOperation::SubShift { left, right, shift } => {
					let right = shifted(&self.product(x, right.get()), shift);
					let left = self.product(x, left.get());
					self.difference(db, &left, &right, factor, &width)?
				}
			};
			let _ = self
				.products
				.insert((VarKey(Rc::downgrade(x)), factor), bits);
		}
		Ok(Some(self.product(x, c32)))
	}

	/// The bits of a difference `a − b`, which is known to be positive.
	///
	/// Subtraction is addition read the other way round: the bits are created
	/// and then constrained so that adding `b` back gives `a`.
	fn difference<Db: ClauseDatabase + ?Sized>(
		&mut self,
		db: &mut Db,
		a: &[BoolVal],
		b: &[BoolVal],
		factor: Coeff,
		width: &NonZero<u32>,
	) -> Result<Vec<BoolVal>, Unsatisfiable> {
		let span = factor * ((1 << width.get()) - 1);
		let bits: Vec<BoolVal> = (0..BinEnc::required_bits(span))
			.map(|_| BoolVal::Lit(db.new_lit()))
			.collect();
		let _ = AdderEncoder::ripple_carry_adder(db, b, &bits, None, Some(a))?;
		Ok(bits)
	}

	/// The bits of a product already built.
	fn product(&self, x: &Rc<IntVar>, factor: u32) -> Vec<BoolVal> {
		self.products[&(VarKey(Rc::downgrade(x)), Coeff::from(factor))].clone()
	}

	/// Create an integer variable over `dom`.
	pub(crate) fn new_int_var(
		&mut self,
		dom: RangeList<Coeff>,
		add_consistency: bool,
		lbl: String,
	) -> Rc<IntVar> {
		IntVar::new(dom, add_consistency, lbl)
	}

	/// Create an encoder with the given configuration.
	pub(crate) fn with_config(config: IntLinConfig) -> Self {
		Self {
			config,
			..Self::default()
		}
	}
}

impl IntLinear {
	/// Read `con` as `x + y = z`, the shape a ripple-carry adder encodes.
	fn as_addition(&self) -> Option<(&Term, &Term, &Term)> {
		if !matches!(self.cmp, Comparator::Equal) || self.k != 0 {
			return None;
		}
		let [a, b, c] = &self.exp.terms[..] else {
			return None;
		};
		let (x, y, z) = match (a.c, b.c, c.c) {
			(1, 1, -1) => (a, b, c),
			(1, -1, 1) => (a, c, b),
			(-1, 1, 1) => (b, c, a),
			_ => return None,
		};
		// Each encoding counts from its own lower bound, so an adder lines the sum
		// up with the result only when the bound of the result is the sum of the
		// other two. Anything else is left to the walk over the terms, which does
		// not care where an encoding starts.
		// ponytail: reconciling a mismatch would take a second adder for the
		// offset. Nothing builds one today, since the result of an addition is
		// given the bound its inputs imply.
		(z.x.lb() == x.x.lb() + y.x.lb()).then_some((x, y, z))
	}

	/// Create the constraint `Σ terms ≷ k`.
	pub(crate) fn new(terms: Vec<Term>, cmp: Comparator, k: Coeff) -> Self {
		Self {
			exp: IntLinExp { terms },
			cmp,
			k,
		}
	}

	/// Narrow the domains of the variables of `con` to the values that can
	/// still take part in a solution, up to a fixpoint.
	///
	/// A variable that is already encoded is left alone: its literals are
	/// committed and the values they stand for cannot be taken back.
	fn propagate(&self) -> Result {
		for cmp in self.cmp.split() {
			loop {
				let mut changed = false;
				for (i, term) in self.exp.terms.iter().enumerate() {
					// What the other terms contribute at their most favourable
					// leaves the rest of the budget for this one.
					let others: Coeff = self
						.exp
						.terms
						.iter()
						.enumerate()
						.filter(|(j, _)| *j != i)
						.map(|(_, t)| match cmp {
							Comparator::LessEq => t.lb(),
							_ => t.ub(),
						})
						.sum();
					let slack = self.k - others;
					if term.x.is_encoded() {
						continue;
					}
					// `c·x ≷ slack`, turned around when `c` is negative.
					let cmp = if term.c >= 0 { cmp } else { cmp.reverse() };
					changed |= match cmp {
						Comparator::LessEq => term.x.set_ub(div_floor(slack, term.c)),
						_ => term.x.set_lb(div_ceil(slack, term.c)),
					};
					if term.x.dom().is_empty() {
						return Err(Unsatisfiable);
					}
				}
				if !changed {
					break;
				}
			}
		}
		Ok(())
	}
}

impl Encoded<'_> {
	/// The clauses for `Σ terms ≷ k`, by taking the terms one at a time.
	///
	/// The head term is walked over the values it can take. Reaching a value
	/// costs the sum a known amount, so what is left for the remaining terms
	/// is a smaller constraint of the same shape, and the clauses for it need
	/// only hold when that value is in fact reached.
	fn walk(terms: &[Encoded], cmp: Comparator, k: Coeff) -> Vec<Vec<BoolVal>> {
		let Some((head, tail)) = terms.split_first() else {
			// Nothing left to give, so the empty sum either satisfies what remains
			// of the constraint or nothing can.
			let holds = match cmp {
				Comparator::LessEq => 0 <= k,
				Comparator::GreaterEq => 0 >= k,
				Comparator::Equal => unreachable!("an equality is split before it is encoded"),
			};
			return if holds { Vec::new() } else { vec![Vec::new()] };
		};
		if tail.is_empty() {
			return vec![vec![head.bound(cmp, k)]];
		}
		// Guard on the head reaching a value from whichever side pushes the sum
		// towards breaking the constraint.
		let geq = (head.c >= 0) == matches!(cmp, Comparator::LessEq);
		let mut clauses = Vec::new();
		let mut last: Option<Vec<Vec<BoolVal>>> = None;
		for (d, guard) in head.ord.steps(geq) {
			let sub = Self::walk(tail, cmp, k - head.c * d);
			// Advancing the walk only weakens the guard, so a step that asks of the
			// remaining terms exactly what the step before it asked is already
			// covered by that one. Consecutive steps land on the same demand often:
			// dividing by a coefficient rounds to the same bound, and the order
			// literals snap to the values the domain actually has.
			if last.as_ref() == Some(&sub) {
				continue;
			}
			clauses.extend(sub.iter().map(|clause| {
				std::iter::once(guard)
					.chain(clause.iter().copied())
					.collect()
			}));
			last = Some(sub);
		}
		clauses
	}

	/// The literal that holds when this term alone satisfies `term ≷ k`.
	fn bound(&self, cmp: Comparator, k: Coeff) -> BoolVal {
		// Dividing by a negative coefficient turns the comparison around.
		match if self.c >= 0 { cmp } else { cmp.reverse() } {
			Comparator::LessEq => self.ord.leq_val(div_floor(k, self.c)),
			Comparator::GreaterEq => self.ord.geq_val(div_ceil(k, self.c)),
			Comparator::Equal => unreachable!("an equality is split before it is encoded"),
		}
	}
}

impl Term {
	/// Encode `x + y = z` with a ripple-carry adder over the binary encodings.
	fn encode_addition<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		x: &Term,
		y: &Term,
		z: &Term,
	) -> Result {
		let (xs, ys, zs) = (x.x.bin(db)?, y.x.bin(db)?, z.x.bin(db)?);
		let _ = AdderEncoder::ripple_carry_adder(
			db,
			&xs.to_vec(),
			&ys.to_vec(),
			None,
			Some(&zs.to_vec()),
		)?;
		Ok(())
	}

	/// The term with its coefficient negated.
	fn negated(&self) -> Self {
		Self::new(-self.c, Rc::clone(&self.x))
	}

	/// The greatest value the term can take.
	pub(crate) fn ub(&self) -> Coeff {
		if self.c >= 0 {
			self.c * self.x.ub()
		} else {
			self.c * self.x.lb()
		}
	}

	/// The least value the term can take.
	fn lb(&self) -> Coeff {
		if self.c >= 0 {
			self.c * self.x.lb()
		} else {
			self.c * self.x.ub()
		}
	}

	/// Create the term `c·x`.
	pub(crate) fn new(c: Coeff, x: Rc<IntVar>) -> Self {
		Self { c, x }
	}
}

#[cfg(test)]
mod tests {
	use std::rc::Rc;

	use itertools::Itertools;
	use rangelist::RangeList;
	use traced_test::test;

	use super::{IntLinConfig, IntLinEncoder, IntLinear, IntVar, Term};
	use crate::{
		bool_linear::Comparator,
		solver::{cadical::Cadical, SolveResult, Solver},
		ClauseDatabaseTools, Cnf, Coeff, Valuation,
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
	) -> (Vec<Vec<Coeff>>, Vec<Rc<IntVar>>) {
		let mut cnf = Cnf::default();
		let mut enc = IntLinEncoder::with_config(IntLinConfig { propagate, cutoff });
		let xs = doms
			.iter()
			.enumerate()
			.map(|(i, dom)| enc.new_int_var(dom.clone(), true, format!("x{i}")))
			.collect_vec();
		let terms = coeffs
			.iter()
			.zip(&xs)
			.map(|(&c, x)| Term::new(c, Rc::clone(x)))
			.collect_vec();

		let con = IntLinear::new(terms, cmp, k);
		if enc.encode(&mut cnf, &con).is_err() {
			return (Vec::new(), xs);
		}
		// Rule out each assignment by the literals that decide the variables,
		// so that what is enumerated is integer solutions rather than models. A
		// constraint whose variables were all narrowed to a single value has no
		// literals at all, and the empty nogood correctly stops after one.
		let lits = xs.iter().flat_map(|x| x.lits()).collect_vec();
		let mut slv = Cadical::from(&cnf);
		let mut solutions = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			solutions.push(xs.iter().map(|x| x.value(&value)).collect_vec());
			let no_good = lits
				.iter()
				.map(|&l| if value.value(l) { !l } else { l })
				.collect_vec();
			if slv.add_clause(no_good).is_err() {
				break;
			}
		}
		solutions.sort();
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
		let contiguous = RangeList::from_iter([0..=3]);
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
		let dom = RangeList::from_elements([-2, 0, 3, 4]);
		for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
			for c in [-3, -1, 1, 2] {
				for k in -8..=8 {
					assert_eq!(
						solutions_of(&[c], std::slice::from_ref(&dom), cmp, k, false),
						brute_force(&[c], std::slice::from_ref(&dom), cmp, k),
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
		let contiguous = RangeList::from_iter([0..=3]);
		let holey = RangeList::from_elements([0, 1, 3]);
		let wide = RangeList::from_iter([2..=9]);
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
			let doms = vec![RangeList::from_iter([0..=span]); coeffs.len()];
			let mut cnf = Cnf::default();
			let mut enc = IntLinEncoder::default();
			let xs = doms
				.iter()
				.enumerate()
				.map(|(i, d)| enc.new_int_var(d.clone(), true, format!("x{i}")))
				.collect_vec();
			let terms = coeffs
				.iter()
				.zip(&xs)
				.map(|(&c, x)| Term::new(c, Rc::clone(x)))
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
		let dom = RangeList::from_iter([0..=7]);
		for c in [
			1, 2, 3, 5, 7, 9, 11, 15, 23, 45, 99, 101, 127, 255, 341, 569, 1023,
		] {
			for cmp in [Comparator::LessEq, Comparator::Equal, Comparator::GreaterEq] {
				// Around each value the product can take, and just off it.
				for k in (0..=7).flat_map(|v: Coeff| [c * v - 1, c * v, c * v + 1]) {
					let (solutions, xs) =
						solutions_with(&[c], std::slice::from_ref(&dom), cmp, k, false, Some(0));
					assert_eq!(
						solutions,
						brute_force(&[c], std::slice::from_ref(&dom), cmp, k),
						"{c}·x {cmp:?} {k}"
					);
					assert!(
						!xs.iter().any(|x| x.has_ord()),
						"{c}·x {cmp:?} {k} fell back to the walk"
					);
				}
			}
		}
	}

	#[test]
	fn a_sum_that_is_negative_throughout_reads_positive() {
		let doms = [
			RangeList::from_iter([0..=3]),
			RangeList::from_elements([1, 2, 5]),
		];
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
						!xs.iter().any(|x| x.has_ord()),
						"{coeffs:?} {cmp:?} {k} fell back to the walk"
					);
				}
			}
		}
	}

	#[test]
	fn products_combine_with_each_other() {
		let doms = [
			RangeList::from_iter([0..=3]),
			RangeList::from_elements([0, 1, 4]),
			RangeList::from_iter([2..=5]),
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
	fn a_product_is_built_once() {
		// The same coefficient over the same variable, in two constraints. The
		// second should cost nothing beyond its own bound.
		let dom = RangeList::from_iter([0..=15]);
		let mut cnf = Cnf::default();
		let mut enc = IntLinEncoder::with_config(IntLinConfig {
			propagate: false,
			cutoff: Some(0),
		});
		let x = enc.new_int_var(dom, true, "x".to_owned());

		let con = |k| IntLinear::new(vec![Term::new(45, Rc::clone(&x))], Comparator::LessEq, k);
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
			vec![RangeList::from_iter([0..=3]); 3],
			vec![RangeList::from_iter([0..=1]); 4],
			vec![
				RangeList::from_iter([2..=5]),
				RangeList::from_elements([0, 1, 4]),
				RangeList::from_iter([1..=3]),
			],
			vec![
				RangeList::from_iter([-3..=0]),
				RangeList::from_iter([1..=2]),
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
						!xs.iter().any(|x| x.has_ord()),
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
		let from = |lb: Coeff| RangeList::from_iter([lb..=(lb + 3)]);
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
			RangeList::from_iter([0..=1]),
			RangeList::from_iter([0..=1]),
			RangeList::from_iter([0..=15]),
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
		let dom = RangeList::from_iter([0..=3]);
		let (x, y) = (
			enc.new_int_var(dom.clone(), true, "x".to_owned()),
			enc.new_int_var(dom, true, "y".to_owned()),
		);
		let con = IntLinear::new(
			vec![Term::new(3, Rc::clone(&x)), Term::new(1, Rc::clone(&y))],
			Comparator::LessEq,
			5,
		);

		let mut cnf = Cnf::default();
		enc.encode(&mut cnf, &con).unwrap();
		assert_eq!(x.ub(), 1, "3x ≤ 5 leaves x at most one");
		assert_eq!(y.ub(), 3, "y is already tight");
	}
}
