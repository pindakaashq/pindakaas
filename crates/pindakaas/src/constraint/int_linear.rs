//! Linear constraints over integer variables, and the encoders that turn them
//! into clauses.
//!
//! A constraint is a sum of terms, each an integer variable scaled by a
//! coefficient, compared against a constant. Aggregating a pseudo-Boolean
//! constraint produces one of these, its groups of related terms having become
//! the integers they encode, so this is where every linear encoder starts.

use std::iter::once;

use itertools::Itertools;
use rangelist::RangeList;
use rustc_hash::FxHashMap;

pub use crate::encoder::int_lin::{IntLinConfig, IntLinEncoder};
use crate::{
	constraint::bool_linear::{Comparator, LimitComp, PosCoeff},
	decision::integer::IntVar,
	encoder::adder::AdderEncoder,
	helpers::{div_ceil, div_floor, new_named_lit},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Lit, Result, Unsatisfiable,
};

/// A linear constraint over integer variables as aggregation leaves it.
///
/// Every coefficient is positive, the sum is compared with `≤` or `=` rather
/// than `≥`, and the constant it is compared against is not negative. An
/// encoder that only ever sees aggregated constraints can rely on that instead
/// of checking for it, which is most of them: only the constraints a
/// decomposition makes for itself fall outside it, and those it encodes itself.
#[derive(Clone, Debug)]
pub struct NormalizedIntLinear {
	pub(crate) exp: IntLinExp,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

/// A linear constraint over integer variables, `Σ cᵢ·xᵢ ≷ k`.
#[derive(Clone, Debug)]
pub struct IntLinear {
	pub(crate) exp: IntLinExp,
	pub(crate) cmp: Comparator,
	pub(crate) k: Coeff,
}

/// A linear constraint over three integer terms, `x + y ≷ z`.
///
/// This is what a decomposition breaks a longer constraint into. The strategies
/// differ in the shape they give the intermediate sums — a chain, a balanced
/// tree, the layers of a decision diagram — but every step of every one of them
/// is the same thing: two terms, and where they come to together. Saying so in
/// the type keeps a decomposition from having to express it as a constraint of
/// any shape at all, which the encoder would then have to recognise again.
///
/// It is not a [`NormalizedIntLinear`]: `z` stands on the other side of the
/// comparison, and moving it across would mean a view of it counting the other
/// way rather than a constant.
#[derive(Clone, Debug)]
pub struct TernaryIntLinear {
	pub(crate) x: Term,
	pub(crate) y: Term,
	pub(crate) cmp: Comparator,
	pub(crate) z: Term,
}

impl TernaryIntLinear {
	/// The constraint `x + y ≷ z`.
	pub fn new(x: Term, y: Term, cmp: Comparator, z: Term) -> Self {
		Self { x, y, cmp, z }
	}

	/// The comparator of the constraint.
	pub fn cmp(&self) -> Comparator {
		self.cmp
	}

	/// The two terms that are added together.
	pub fn addends(&self) -> (&Term, &Term) {
		(&self.x, &self.y)
	}

	/// The term they are compared against.
	pub fn total(&self) -> &Term {
		&self.z
	}
}

impl From<&NormalizedIntLinear> for TernaryIntLinear {
	/// A constraint of two terms or fewer is already an addition: what its
	/// terms come to, against the constant it is compared with.
	///
	/// A term it does not have is zero, and the constant is a variable of one
	/// value — neither of which any literal has to stand for.
	fn from(con: &NormalizedIntLinear) -> Self {
		debug_assert!(
			con.terms().len() <= 2,
			"a longer constraint is more than one addition"
		);
		let zero = || Term::new(1, IntVar::new(0..=0));
		let mut terms = con.terms().iter().cloned();
		let (x, y) = (
			terms.next().unwrap_or_else(zero),
			terms.next().unwrap_or_else(zero),
		);
		let k = con.k();
		TernaryIntLinear::new(x, y, con.cmp().into(), Term::new(1, IntVar::new(k..=k)))
	}
}

impl From<&TernaryIntLinear> for IntLinear {
	/// A term over a variable of one value is what it is worth, so it belongs
	/// with the constant rather than among the terms.
	fn from(con: &TernaryIntLinear) -> Self {
		let (mut terms, mut k) = (Vec::new(), 0);
		for (term, adds) in [(&con.x, true), (&con.y, true), (&con.z, false)] {
			if term.x.card() == 1 {
				let worth = term.c * term.x.min();
				k += if adds { -worth } else { worth };
			} else {
				terms.push(if adds { term.clone() } else { term.negated() });
			}
		}
		Self::new(terms, con.cmp, k)
	}
}

/// A way of breaking a linear constraint into smaller ones.
///
/// What the encodings in the literature differ in is mostly the shape they give
/// the intermediate sums — a chain, a balanced tree, the layers of a decision
/// diagram — rather than how any one step is encoded. Producing constraints
/// rather than clauses keeps that difference in one place and leaves each step
/// to be encoded on whichever view its variables have.
pub(crate) trait Decompose {
	/// Break `con` into the additions that together mean the same.
	///
	/// The database is there for a strategy that wants a literal of a variable
	/// it has already made — a layer of a decision diagram sharing one with the
	/// layer after it, say. A strategy that shares nothing needs it for
	/// nothing.
	fn decompose<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		con: &NormalizedIntLinear,
	) -> Result<Vec<TernaryIntLinear>, Unsatisfiable>;
}

/// A sum of integer terms.
#[derive(Clone, Debug, Default)]
pub(crate) struct IntLinExp {
	pub(crate) terms: Vec<Term>,
}

/// An integer variable scaled by a coefficient.
///
/// A coefficient other than one is not expanded into repeated addition: the
/// encoder synthesises a chain of shifts and additions for it over the
/// variable's bits, and shares that chain with every other term of the same
/// coefficient over the same variable.
#[derive(Clone, Debug)]
pub struct Term {
	pub(crate) c: Coeff,
	pub(crate) x: IntVar,
}

impl NormalizedIntLinear {
	/// The comparator of the constraint, which is never `≥`.
	pub(crate) fn cmp(&self) -> LimitComp {
		self.cmp.clone()
	}

	/// The integer linear constraint a normalised pseudo-Boolean one stands
	/// for.
	///
	/// Aggregation has already found what structure the terms have; this reads
	/// each group as the integer it encodes, so that whichever encoder takes
	/// the constraint from here works on integers rather than on the literals
	/// they happen to be written in.
	pub(crate) fn from_terms(terms: Vec<Term>, cmp: LimitComp, k: PosCoeff) -> Self {
		debug_assert!(
			terms.iter().all(|t| t.c > 0),
			"aggregation leaves every coefficient positive"
		);
		Self {
			exp: IntLinExp { terms },
			cmp,
			k,
		}
	}

	/// What each term is worth, as the literals standing for it and what each
	/// of them adds.
	#[cfg(test)]
	pub(crate) fn grouped_weights<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<Vec<Vec<(Lit, Coeff)>>, Unsatisfiable> {
		IntLinear::from(self).grouped_weights(db)
	}

	/// The constant the sum is compared against, which is not negative.
	pub fn k(&self) -> Coeff {
		*self.k
	}

	/// The terms of the sum, each with a positive coefficient.
	pub fn terms(&self) -> &[Term] {
		&self.exp.terms
	}
}

impl From<&NormalizedIntLinear> for IntLinear {
	fn from(con: &NormalizedIntLinear) -> Self {
		Self {
			exp: con.exp.clone(),
			cmp: con.cmp.clone().into(),
			k: *con.k,
		}
	}
}

impl IntLinear {
	/// The comparator of the constraint.
	pub fn cmp(&self) -> Comparator {
		self.cmp
	}

	/// The constant the sum is compared against.
	pub fn k(&self) -> Coeff {
		self.k
	}

	/// The terms of the sum.
	pub fn terms(&self) -> &[Term] {
		&self.exp.terms
	}

	/// What each term is worth, as the literals standing for it and what each
	/// of them adds.
	///
	/// The same information as [`Self::as_weighted`], kept term by term rather
	/// than flattened, so that which literals share a variable is still
	/// visible.
	#[cfg(test)]
	pub(crate) fn grouped_weights<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<Vec<Vec<(Lit, Coeff)>>, Unsatisfiable> {
		self.terms()
			.iter()
			.map(|t| {
				let (lits, _) = t.x.as_weighted(db)?;
				Ok(lits
					.into_iter()
					.map(|(l, w)| (l, t.c * w))
					.filter(|&(_, w)| w != 0)
					.collect())
			})
			.collect()
	}

	/// The integer linear constraint a normalised pseudo-Boolean one stands
	/// for.
	///
	/// Aggregation has already found what structure the terms have; this reads
	/// each group as the integer it encodes, so that whichever encoder takes
	/// the constraint from here works on integers rather than on the literals
	/// they happen to be written in.
	/// Read `con` as `x + y = z`, the shape a ripple-carry adder encodes.
	pub(crate) fn as_addition(&self) -> Option<(&Term, &Term, &Term)> {
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
		// Each encoding counts from its own lower bound, so an adder lines the
		// sum up with the result only when the bound of the result is the sum
		// of the other two. Anything else is left to the walk over the terms,
		// which does not care where an encoding starts.
		(z.x.min() == x.x.min() + y.x.min()).then_some((x, y, z))
	}

	/// Create the constraint `Σ terms ≷ k`.
	pub fn new(terms: Vec<Term>, cmp: Comparator, k: Coeff) -> Self {
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
	pub(crate) fn propagate(&self) -> Result {
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
							Comparator::LessEq => t.min(),
							_ => t.max(),
						})
						.sum();
					let slack = self.k - others;
					if term.x.is_committed() {
						continue;
					}
					// `c·x ≷ slack`, turned around when `c` is negative.
					let cmp = if term.c >= 0 { cmp } else { cmp.reverse() };
					changed |= match cmp {
						Comparator::LessEq => term.x.set_max(div_floor(slack, term.c)),
						_ => term.x.set_min(div_ceil(slack, term.c)),
					};
					if term.x.domain().is_empty() {
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

impl Term {
	/// Encode `x + y = z` with a ripple-carry adder over the binary encodings.
	pub(crate) fn encode_addition<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		x: &Term,
		y: &Term,
		z: &Term,
	) -> Result {
		let (xs, ys, zs) = (
			x.x.binary_encoding(db)?,
			y.x.binary_encoding(db)?,
			z.x.binary_encoding(db)?,
		);
		let _ = AdderEncoder::ripple_carry_adder(
			db,
			&xs.to_vec(),
			&ys.to_vec(),
			None,
			Some(&zs.to_vec()),
		)?;
		Ok(())
	}

	/// The integer a group of at-most-one terms stands for.
	///
	/// One term at most is chosen, so the group takes the value of whichever it
	/// is and zero when none is. That is a direct encoding, and the terms
	/// already are one: a literal here says the group *is* its coefficient,
	/// which is what a direct literal says and not what an order literal says.
	///
	/// At most one of them holding is taken on trust — it is what makes the
	/// group a group — but the literal standing for the group being worth
	/// nothing is made here, along with the clauses tying it to the rest.
	///
	/// `exact` asks for the upper bound as well, which a group only needs when
	/// the constraint it belongs to is an equality.
	pub fn from_at_most_one<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		terms: &[(Lit, PosCoeff)],
		label: &str,
		exact: bool,
	) -> Result<Self, Unsatisfiable> {
		// At most one term is chosen, so the group takes the value of
		// whichever it is, and zero when none is. That is a direct
		// encoding, and the terms already are one: a literal here says
		// the group *is* its coefficient, which is what a direct
		// literal says and not what an order literal says.
		let mut by_coeff: FxHashMap<Coeff, Vec<Lit>> = FxHashMap::default();
		for &(lit, coeff) in terms {
			by_coeff.entry(*coeff).or_default().push(lit);
		}
		// The group is worth nothing when no term is chosen, and one of
		// the coefficients otherwise.
		let domain = RangeList::from_elements(once(0).chain(by_coeff.keys().copied()));

		let by_coeff = by_coeff
			.into_iter()
			.sorted_by_key(|(c, _)| *c)
			.collect_vec();
		// The group is worth nothing when no term is chosen, which is a
		// value like any other. A group of one term says that already:
		// it is worth nothing exactly when that term is not chosen. Any
		// other group needs a literal of its own, and clauses tying it
		// to the rest.
		let single = matches!(by_coeff.as_slice(), [(_, terms)] if terms.len() == 1);
		let none = match by_coeff.as_slice() {
			[(_, terms)] if terms.len() == 1 => !terms[0],
			_ => new_named_lit!(db, format!("{label}=0")),
		};
		let mut lits = vec![none];
		for (_coeff, terms) in by_coeff {
			let d = match terms.as_slice() {
				// One term reaching a value is the literal for it.
				&[lit] => lit,
				// Several are not one literal, so they need one, which
				// each of them reaches.
				_ => {
					let d = new_named_lit!(db, format!("{label}={_coeff}"));
					for &lit in &terms {
						db.add_clause([!lit, d])?;
					}
					d
				}
			};
			// The group is worth this only if one of these terms is
			// chosen. Without it the group may say it is worth more
			// than it is, which a `≤` can live with and costs the
			// solver nothing, since nothing forces it to. A value one
			// term reaches says it already, that term being the literal
			// for it.
			if exact && terms.len() > 1 {
				db.add_clause([!d].into_iter().chain(terms))?;
			}
			// Nothing is chosen only if this value is not taken.
			if !single {
				db.add_clause([!d, !none])?;
			}
			lits.push(d);
		}
		// Some value is taken.
		if !single {
			db.add_clause(lits.iter().copied())?;
		}
		// The group's own clauses above already give exactly one value,
		// so the variable is told the literals rather than asked to
		// constrain them.
		let x = IntVar::new(domain)
			.enforce_consistency(false)
			.with_label(label);
		x.with_direct_encoding(db, &lits, None)?;
		Ok(Self::new(1, x))
	}

	/// The integer a group of terms that each imply the one before stands for.
	///
	/// The implications are taken on trust: they are what makes the group a
	/// chain, and the running sums it counts through are read straight off its
	/// literals. See [`IntVar::constrain`] where they need saying.
	pub fn from_implication_chain<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		terms: &[(Lit, PosCoeff)],
		label: &str,
	) -> Result<Self, Unsatisfiable> {
		// Each term implies the one before it, so the group counts up
		// through the running sums and a term's literal is already the
		// order literal for its sum.
		let mut acc = 0;
		let (totals, lits): (Vec<_>, Vec<_>) = terms
			.iter()
			.map(|&(lit, coeff)| {
				acc += *coeff;
				(acc, lit)
			})
			.unzip();
		// Coefficients are positive, so the running sums climb and the
		// domain has one value per term, plus the zero none reaches.
		let domain = RangeList::from_elements(once(0).chain(totals));
		Ok(Self::new(
			1,
			IntVar::from_order_encoding(db, domain, &lits)?.with_label(label),
		))
	}

	/// The integer a group of terms declared to be its bits stands for.
	///
	/// The bits staying within `lb..=ub` is taken on trust, as is the caller's
	/// word that these literals are the bits of one integer at all. See
	/// [`IntVar::constrain`] to make the bounds a restriction rather than a
	/// claim.
	pub fn from_binary_digits<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		terms: &[(Lit, PosCoeff)],
		lb: PosCoeff,
		ub: PosCoeff,
		label: &str,
	) -> Result<Self, Unsatisfiable> {
		// The caller has declared these literals to be the bits of an
		// integer, so they are taken as exactly that rather than being
		// split into a variable each. Their coefficients are a multiple
		// of the powers of two, and the aggregator has already scaled
		// the bounds to match, so what the bits hold is the value over
		// that multiple and the multiple stays on the term.
		let multiple = *terms[0].1;
		let bits: Vec<BoolVal> = terms.iter().map(|&(lit, _)| BoolVal::Lit(lit)).collect();
		let domain = RangeList::from(div_ceil(*lb, multiple)..=div_floor(*ub, multiple));
		if domain.is_empty() {
			db.contradiction()?;
		}
		Ok(Self::new(
			multiple,
			// The bits count from zero, whatever the bounds say.
			IntVar::from_binary_encoding(db, domain, &bits, 0)?.with_label(label),
		))
	}

	/// The values the term can take.
	pub(crate) fn values(&self) -> Vec<Coeff> {
		let mut vs: Vec<Coeff> = self
			.x
			.domain()
			.iter()
			.flatten()
			.map(|v| self.c * v)
			.collect();
		// A negative coefficient turns the domain around.
		vs.sort_unstable();
		vs
	}

	/// The term with its coefficient negated.
	pub(crate) fn negated(&self) -> Self {
		Self::new(-self.c, self.x.clone())
	}

	/// The greatest value the term can take.
	pub(crate) fn max(&self) -> Coeff {
		if self.c >= 0 {
			self.c * self.x.max()
		} else {
			self.c * self.x.min()
		}
	}

	/// The least value the term can take.
	pub(crate) fn min(&self) -> Coeff {
		if self.c >= 0 {
			self.c * self.x.min()
		} else {
			self.c * self.x.max()
		}
	}

	/// Create the term `c·x`.
	pub fn new(c: Coeff, x: IntVar) -> Self {
		Self { c, x }
	}
}
