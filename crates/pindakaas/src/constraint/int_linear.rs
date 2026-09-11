//! Linear constraints over integer variables, and the encoders that turn them
//! into clauses.
//!
//! A constraint is a sum of terms, each an integer variable scaled by a
//! coefficient, compared against a constant. Aggregating a pseudo-Boolean
//! constraint produces one of these, its groups of related terms having become
//! the integers they encode, so this is where every linear encoder starts.

use std::cmp::min;

use itertools::Itertools;
use rangelist::RangeList;

pub use crate::encoder::{
	decision_diagram::DecisionDiagramEncoder, mixed_radix::MixedRadixEncoder,
	sequential_counter::SequentialCounterEncoder, totalizer::TotalizerEncoder,
	watchdog::WatchdogEncoder,
};
#[cfg(test)]
use crate::Lit;
use crate::{
	constraint::{
		int_ternary::IntTernary,
		linear::{Comparator, LimitComp, PosCoeff},
	},
	decision::integer::IntVar,
	encoder::adder::AdderEncoder,
	helpers::{div_ceil, div_floor, new_named_lit},
	BoolVal, ClauseDatabase, Coeff, Result, Unsatisfiable,
};

/// A linear constraint over integer variables as aggregation leaves it.
///
/// Coefficients are positive, the comparator is `≤` or `=`, and the bound is
/// nonnegative.
///
/// # Examples
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{linear::{Comparator, Linear}, linear::{LinAggregator, LinVariant}},
/// #     decision::integer::IntVar, encoder::decision_diagram::DecisionDiagramEncoder,
/// #     Cnf, Encoder, ClauseDatabaseTools,
/// # };
/// let mut f = Cnf::default();
/// let x = IntVar::new(0..=5);
/// let con = Linear::new(x.clone() * -2 + 7, Comparator::GreaterEq, 1);
///
/// let LinVariant::Linear(con) = LinAggregator::default().aggregate(&mut f, &con)? else {
///     panic!("a constraint over an integer aggregates to a linear one");
/// };
/// // Whatever it was written as, the types now say it is `≤` over positive
/// // coefficients: `-2x + 7 ≥ 1` has become `2x ≤ 6`, counted in steps of two.
/// assert_eq!(con.k(), 3);
/// DecisionDiagramEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Clone, Debug)]
pub struct NormalizedIntLinear {
	pub(crate) terms: Vec<(PosCoeff, IntVar)>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

/// A linear constraint over integer variables, `Σ cᵢ·xᵢ ≷ k`, with the signs
/// and comparator it was written with.
///
/// The working form behind aggregation and the encoders: an [`IntTernary`] is
/// read as one to be walked, and a [`NormalizedIntLinear`] is one whose
/// coefficients have been made positive. Callers state constraints as a
/// [`Linear`](super::linear::Linear) and aggregate.
#[derive(Clone, Debug)]
pub(crate) struct IntLinear {
	pub(crate) terms: Vec<Term>,
	pub(crate) cmp: Comparator,
	pub(crate) k: Coeff,
}

/// A decomposition into ternary constraints, leaving Boolean views to the
/// encoder.
pub(crate) trait Decompose {
	/// Additions equivalent to `con`.
	///
	/// The database allows a decomposition to share literals between
	/// intermediates.
	fn decompose<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		con: &NormalizedIntLinear,
	) -> Result<Vec<IntTernary>, Unsatisfiable>;
}

/// An integer variable scaled by a coefficient.
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

	/// Returns the constraint's comparator, which is never `≥`.
	pub fn cmp(&self) -> LimitComp {
		self.cmp.clone()
	}

	/// Construct a normalised integer linear constraint.
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

	/// Returns the non-negative constant the sum is compared against.
	pub fn k(&self) -> Coeff {
		*self.k
	}

	/// Returns the sum's terms, each with a positive coefficient.
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
		self.terms
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

	/// The constraint as `x + y = z`, when compatible with a ripple-carry
	/// adder.
	pub(crate) fn as_addition(&self) -> Option<(&Term, &Term, &Term)> {
		if self.k != 0 {
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
		// The adder requires the result offset to equal the sum of input
		// offsets.
		(z.1.min() == x.1.min() + y.1.min()).then_some((x, y, z))
	}

	/// Create the constraint `Σ terms ≷ k`.
	pub(crate) fn new(terms: Vec<Term>, cmp: Comparator, k: Coeff) -> Self {
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
	cmp: Comparator,
	z: &Term,
) -> Result {
	let (xs, ys, zs) = (
		x.1.binary_encoding(db)?.to_vec(),
		y.1.binary_encoding(db)?.to_vec(),
		z.1.binary_encoding(db)?.to_vec(),
	);
	if cmp == Comparator::Equal {
		let _ = AdderEncoder::ripple_carry_adder(db, &xs, &ys, None, Some(&zs))?;
		return Ok(());
	}
	// `x + y ≤ z` is `x + y + s = z` for a free slack, and the adder driving
	// the bits above `z` to zero is what rules out an overflow.
	let sum = AdderEncoder::ripple_carry_adder(db, &xs, &ys, None, None)?;
	let slack: Vec<BoolVal> = (0..zs.len().max(sum.len()))
		.map(|_| BoolVal::Lit(new_named_lit!(db, "s")))
		.collect();
	let (lhs, total) = match cmp {
		Comparator::LessEq => (&sum, &zs),
		_ => (&zs, &sum),
	};
	let _ = AdderEncoder::ripple_carry_adder(db, lhs, &slack, None, Some(total))?;
	Ok(())
}

/// The values `x + y` can take, with anything past `ub` dropped.
///
/// The sum of two intervals is an interval, so where neither term's
/// coefficient stretches a contiguous domain into gaps there is nothing to
/// enumerate. That is the common case — every intermediate of a decomposition
/// has a coefficient of one — and enumerating it costs `O(|dom x|·|dom y|)`
/// values and a sort, before the bound drops most of them again.
pub(crate) fn sum_values(x: &Term, y: &Term, ub: Coeff) -> RangeList<Coeff> {
	if let (Some((x0, x1)), Some((y0, y1))) = (term_interval(x), term_interval(y)) {
		let (lo, hi) = (x0 + y0, min(x1 + y1, ub));
		return if lo > hi {
			RangeList::default()
		} else {
			RangeList::from(lo..=hi)
		};
	}
	term_values(x)
		.into_iter()
		.cartesian_product(term_values(y))
		.map(|(a, b)| a + b)
		.filter(|&d| d <= ub)
		.map(|d| d..=d)
		.collect()
}

/// The term's values as the one range they run over, where they do.
///
/// A coefficient other than ±1 leaves gaps between them, and a domain with a
/// hole in it has them already.
fn term_interval(t: &Term) -> Option<(Coeff, Coeff)> {
	if t.0.abs() != 1 {
		return None;
	}
	let domain = t.1.domain();
	let mut ranges = domain.iter();
	let range = ranges.next()?;
	if ranges.next().is_some() {
		return None;
	}
	let (a, b) = (t.0 * *range.start(), t.0 * *range.end());
	Some((min(a, b), a.max(b)))
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
