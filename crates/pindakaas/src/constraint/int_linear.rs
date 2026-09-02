//! Linear constraints over integer variables, and the encoders that turn them
//! into clauses.
//!
//! A constraint is a sum of terms, each an integer variable scaled by a
//! coefficient, compared against a constant. Aggregating a pseudo-Boolean
//! constraint produces one of these, its groups of related terms having become
//! the integers they encode, so this is where every linear encoder starts.

pub use crate::encoder::{
	bdd::BddEncoder,
	swc::SwcEncoder,
	totalizer::TotalizerEncoder,
};
#[cfg(test)]
use crate::Lit;
use crate::{
	constraint::{
		bool_linear::{Comparator, LimitComp, PosCoeff},
		int_ternary::IntTernary,
	},
	decision::integer::IntVar,
	encoder::adder::AdderEncoder,
	helpers::{div_ceil, div_floor},
	ClauseDatabase, Coeff, Result, Unsatisfiable,
};

/// A linear constraint over integer variables as aggregation leaves it.
///
/// Every coefficient is positive, the sum is compared with `≤` or `=` rather
/// than `≥`, and the constant it is compared against is not negative. An
/// encoder that only ever sees aggregated constraints can rely on that instead
/// of checking for it, which is most of them: only the constraints a
/// decomposition makes for itself fall outside it, and those it encodes itself.
///
/// The usual way to reach one is to aggregate, which puts a constraint into
/// this form whatever shape it was written in:
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{bool_linear::{Comparator, Linear}, linear::{BoolLinAggregator, LinVariant}},
/// #     decision::integer::IntVar, encoder::bdd::BddEncoder,
/// #     Cnf, Encoder, ClauseDatabaseTools,
/// # };
/// let mut f = Cnf::default();
/// let x = IntVar::new(0..=5);
/// let con = Linear::new(x.clone() * -2 + 7, Comparator::GreaterEq, 1);
///
/// let LinVariant::Linear(con) = BoolLinAggregator::default().aggregate(&mut f, &con)? else {
///     panic!("a constraint over an integer aggregates to a linear one");
/// };
/// // Whatever it was written as, the types now say it is `≤` over positive
/// // coefficients: `-2x + 7 ≥ 1` has become `2x ≤ 6`, counted in steps of two.
/// assert_eq!(con.k(), 3);
/// BddEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Clone, Debug)]
pub struct NormalizedIntLinear {
	pub(crate) terms: Vec<(PosCoeff, IntVar)>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

/// A linear constraint over integer variables, `Σ cᵢ·xᵢ ≷ k`.
#[derive(Clone, Debug)]
pub struct IntLinear {
	pub(crate) terms: Vec<Term>,
	pub(crate) cmp: Comparator,
	pub(crate) k: Coeff,
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
	) -> Result<Vec<IntTernary>, Unsatisfiable>;
}

/// An integer variable scaled by a coefficient.
///
/// A coefficient other than one is not expanded into repeated addition: the
/// encoder synthesises a chain of shifts and additions for it over the
/// variable's bits, and shares that chain with every other term of the same
/// coefficient over the same variable.
pub(crate) type Term = (Coeff, IntVar);

impl NormalizedIntLinear {
	/// The constraint as a single addition, if it is short enough to be one.
	///
	/// A term it does not have is zero, and the constant it is compared with is
	/// a variable of one value — neither of which any literal has to stand for.
	pub(crate) fn as_ternary(&self) -> Option<IntTernary> {
		if self.terms().len() > 2 {
			return None;
		}
		let zero = || (1, IntVar::new(0..=0));
		let mut terms = self.terms().iter().map(|(c, x)| (**c, x.clone()));
		let (x, y) = (
			terms.next().unwrap_or_else(zero),
			terms.next().unwrap_or_else(zero),
		);
		let k = self.k();
		Some(IntTernary::new(
			x,
			y,
			self.cmp().into(),
			(1, IntVar::new(k..=k)),
		))
	}

	/// The comparator of the constraint, which is never `≥`.
	pub fn cmp(&self) -> LimitComp {
		self.cmp.clone()
	}

	/// The integer linear constraint a normalised pseudo-Boolean one stands
	/// for.
	///
	/// Aggregation has already found what structure the terms have; this reads
	/// each group as the integer it encodes, so that whichever encoder takes
	/// the constraint from here works on integers rather than on the literals
	/// they happen to be written in.
	///
	/// Every guarantee the type makes is carried by the arguments: a
	/// [`LimitComp`] cannot be `≥`, and a [`PosCoeff`] cannot be negative.
	pub fn new(
		terms: impl IntoIterator<Item = (PosCoeff, IntVar)>,
		cmp: LimitComp,
		k: PosCoeff,
	) -> Self {
		Self {
			terms: terms.into_iter().collect(),
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
	pub fn terms(&self) -> &[(PosCoeff, IntVar)] {
		&self.terms
	}
}

impl From<&NormalizedIntLinear> for IntLinear {
	fn from(con: &NormalizedIntLinear) -> Self {
		Self {
			terms: con.terms.iter().map(|(c, x)| (**c, x.clone())).collect(),
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
		&self.terms
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
				let (lits, _) = t.1.as_weighted(db)?;
				Ok(lits
					.into_iter()
					.map(|(l, w)| (l, t.0 * w))
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
		let [a, b, c] = &self.terms[..] else {
			return None;
		};
		let (x, y, z) = match (a.0, b.0, c.0) {
			(1, 1, -1) => (a, b, c),
			(1, -1, 1) => (a, c, b),
			(-1, 1, 1) => (b, c, a),
			_ => return None,
		};
		// Each encoding counts from its own lower bound, so an adder lines the
		// sum up with the result only when the bound of the result is the sum
		// of the other two. Anything else is left to the walk over the terms,
		// which does not care where an encoding starts.
		(z.1.min() == x.1.min() + y.1.min()).then_some((x, y, z))
	}

	/// Create the constraint `Σ terms ≷ k`.
	pub fn new(terms: Vec<Term>, cmp: Comparator, k: Coeff) -> Self {
		Self { terms, cmp, k }
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
				for (i, term) in self.terms.iter().enumerate() {
					// What the other terms contribute at their most favourable
					// leaves the rest of the budget for this one.
					let others: Coeff = self
						.terms
						.iter()
						.enumerate()
						.filter(|(j, _)| *j != i)
						.map(|(_, t)| match cmp {
							Comparator::LessEq => term_min(t),
							_ => term_max(t),
						})
						.sum();
					let slack = self.k - others;
					if term.1.is_committed() {
						continue;
					}
					// `c·x ≷ slack`, turned around when `c` is negative.
					let cmp = if term.0 >= 0 { cmp } else { cmp.reverse() };
					changed |= match cmp {
						Comparator::LessEq => term.1.set_max(div_floor(slack, term.0)),
						_ => term.1.set_min(div_ceil(slack, term.0)),
					};
					if term.1.domain().is_empty() {
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

/// Encode `x + y = z` with a ripple-carry adder over the binary encodings.
pub(crate) fn encode_addition<Db: ClauseDatabase + ?Sized>(
	db: &mut Db,
	x: &Term,
	y: &Term,
	z: &Term,
) -> Result {
	let (xs, ys, zs) = (
		x.1.binary_encoding(db)?,
		y.1.binary_encoding(db)?,
		z.1.binary_encoding(db)?,
	);
	let _ =
		AdderEncoder::ripple_carry_adder(db, &xs.to_vec(), &ys.to_vec(), None, Some(&zs.to_vec()))?;
	Ok(())
}

/// The values the term can take.
pub(crate) fn term_values(t: &Term) -> Vec<Coeff> {
	let mut vs: Vec<Coeff> = t.1.domain().iter().flatten().map(|v| t.0 * v).collect();
	// A negative coefficient turns the domain around.
	vs.sort_unstable();
	vs
}

/// The term with its coefficient negated.
pub(crate) fn term_negated(t: &Term) -> Term {
	(-t.0, t.1.clone())
}

/// The greatest value the term can take.
pub(crate) fn term_max(t: &Term) -> Coeff {
	if t.0 >= 0 {
		t.0 * t.1.max()
	} else {
		t.0 * t.1.min()
	}
}

/// The least value the term can take.
pub(crate) fn term_min(t: &Term) -> Coeff {
	if t.0 >= 0 {
		t.0 * t.1.min()
	} else {
		t.0 * t.1.max()
	}
}
