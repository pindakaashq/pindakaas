//! Linear constraints over integer variables, and the encoders that turn them
//! into clauses.
//!
//! A constraint is a sum of terms, each an integer variable scaled by a
//! coefficient, compared against a constant. Aggregating a pseudo-Boolean
//! constraint produces one of these, its groups of related terms having become
//! the integers they encode, so this is where every linear encoder starts.

/// The `with_consistency`, `with_cutoff`, and `with_propagation` setters of an
/// encoder holding a [`DecomposeConfig`] in its `config` field.
macro_rules! decompose_setters {
	() => {
		/// Enable independent domain constraints for newly created intermediate
		/// views.
		///
		/// Disabled by default. Enables standalone binary and direct consistency
		/// clauses. The consistency constraint of an order encoding is kept
		/// either way, except for the sums of the sorting networks that
		/// [`WatchdogEncoder::with_sorting_networks`] counts with.
		///
		/// [`WatchdogEncoder::with_sorting_networks`]: crate::encoder::watchdog::WatchdogEncoder::with_sorting_networks
		pub fn with_consistency(&mut self, b: bool) -> &mut Self {
			self.config.consistency = b;
			self
		}

		/// Set the domain size at which an unencoded variable prefers binary.
		///
		/// `None` (the default) prefers order; existing binary or order views
		/// take precedence. The threshold is inclusive. Binary arithmetic can
		/// weaken unit propagation; see the [encoding overview](crate::encoder).
		pub fn with_cutoff(&mut self, c: Option<Coeff>) -> &mut Self {
			self.config.cutoff = c;
			self
		}

		/// Narrow the domains to the bounds the constraint implies before
		/// decomposing it; enabled by default.
		///
		/// Narrowing is what keeps the intermediate sums of a decomposition
		/// small, and turning it off can cost several times the clauses.
		pub fn with_propagation(&mut self, b: bool) -> &mut Self {
			self.config.propagation = b;
			self
		}
	};
}

use std::cmp::min;

pub(crate) use decompose_setters;
use itertools::Itertools;
use rangelist::RangeList;

pub use crate::encoder::{
	decision_diagram::DecisionDiagramEncoder, mixed_radix::MixedRadixEncoder,
	sequential_counter::SequentialCounterEncoder, sorting_network::SortingNetworkEncoder,
	totalizer::TotalizerEncoder, watchdog::WatchdogEncoder,
};
use crate::{
	constraint::{
		int_ternary::{IntTernary, IntTernaryConfig, IntTernaryEncoder},
		linear::{Comparator, LimitComp, PosCoeff},
	},
	decision::integer::{IntVar, ShiftedVar},
	encoder::adder::AdderEncoder,
	helpers::{div_ceil, div_floor, new_named_lit},
	BoolVal, ClauseDatabase, Coeff, Lit, Result, Unsatisfiable,
};

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

/// The settings every decomposing encoder shares: how its intermediates are
/// made, and how the ternary pieces it breaks a constraint into are encoded.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct DecomposeConfig {
	pub(crate) consistency: bool,
	pub(crate) propagation: bool,
	pub(crate) cutoff: Option<Coeff>,
}

/// A linear constraint over integer variables, `Σ cᵢ·xᵢ ≷ k`, with the signs
/// and comparator it was written with.
///
/// The working form behind aggregation and the encoders: an [`IntTernary`] is
/// read as one to be walked, and a [`NormalizedIntLinear`] is one whose
/// coefficients have been made positive. Callers state constraints as a
/// [`Linear`](crate::constraint::linear::Linear) and aggregate. Its terms are
/// over variables, never over views.
#[derive(Clone, Debug)]
pub(crate) struct IntLinear {
	pub(crate) terms: Vec<Term>,
	pub(crate) cmp: Comparator,
	pub(crate) k: Coeff,
}

/// A linear constraint over integer variables as aggregation leaves it.
///
/// Coefficients are positive, every term counts from zero, the comparator is
/// `≤` or `=`, and the bound is nonnegative. An encoder may therefore read a
/// term as what it adds to the sum, never as what it takes away.
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
	/// Each term as `c·(x + shift)`.
	terms: Vec<(Coeff, ShiftedVar)>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
}

/// An integer variable scaled by a coefficient.
pub(crate) type Term = (Coeff, IntVar);

/// Encode `x + y = z` with a ripple-carry adder over the binary encodings.
pub(crate) fn encode_addition<Db: ClauseDatabase + ?Sized>(
	db: &mut Db,
	x: &Term,
	y: &Term,
	cmp: Comparator,
	z: &Term,
) -> Result {
	let bits = |db: &mut Db, t: &Term| -> Result<Vec<BoolVal>> {
		let (bits, weight, _) = t.1.binary_bits(db)?;
		debug_assert_eq!(
			weight, 1,
			"an addition is read over the variables themselves, see `IntLinear`"
		);
		Ok(bits)
	};
	let (xs, ys, zs) = (bits(db, x)?, bits(db, y)?, bits(db, z)?);
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

/// Each literal as a term worth its coefficient when it holds and nothing
/// when it does not, which is a direct encoding of the two values already.
pub(crate) fn lit_terms<Db: ClauseDatabase + ?Sized>(
	db: &mut Db,
	lits: impl IntoIterator<Item = (Lit, PosCoeff)>,
) -> Result<Vec<(PosCoeff, IntVar)>, Unsatisfiable> {
	lits.into_iter()
		.enumerate()
		.map(|(i, (lit, coef))| {
			let domain = RangeList::from_elements([0, *coef]);
			IntVar::from_direct_encoding(db, domain, &[!lit, lit])
				.map(|x| (PosCoeff::new(1), x.with_label(format_args!("x{i}"))))
		})
		.collect()
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
	// The bounds tell whether a domain is one range without copying it.
	let (lo, hi) = (t.1.min(), t.1.max());
	if t.0.abs() != 1 || t.1.card() as Coeff != hi - lo + 1 {
		return None;
	}
	let (a, b) = (t.0 * lo, t.0 * hi);
	Some((min(a, b), a.max(b)))
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

/// The values the term can take.
pub(crate) fn term_values(t: &Term) -> Vec<Coeff> {
	let mut vs: Vec<Coeff> = t.1.domain().iter().flatten().map(|v| t.0 * v).collect();
	// A negative coefficient turns the domain around.
	vs.sort_unstable();
	vs
}

impl DecomposeConfig {
	/// The encoder of the pieces a constraint is decomposed into.
	pub(crate) fn encoder(&self) -> IntTernaryEncoder {
		IntTernaryEncoder::with_config(IntTernaryConfig {
			propagate: self.propagation,
			cutoff: self.cutoff,
		})
	}

	/// A variable over `domain` for an intermediate of the decomposition.
	pub(crate) fn intermediate(&self, domain: impl Into<RangeList<Coeff>>) -> IntVar {
		IntVar::new(domain).enforce_consistency(self.consistency)
	}
}

impl Default for DecomposeConfig {
	fn default() -> Self {
		Self {
			consistency: false,
			propagation: true,
			cutoff: None,
		}
	}
}

impl IntLinear {
	/// The constraint as `x + y ≷ z + k`, when compatible with a ripple-carry
	/// adder.
	pub(crate) fn as_addition(&self) -> Option<(&Term, &Term, &Term)> {
		let [a, b, c] = &self.terms[..] else {
			return None;
		};
		let (x, y, z) = match (a.0, b.0, c.0) {
			(1, 1, -1) => (a, b, c),
			(1, -1, 1) => (a, c, b),
			(-1, 1, 1) => (b, c, a),
			_ => return None,
		};
		// Given bits can count from below the domain, so this compares what
		// each binary encoding counts from.
		let least = |t: &Term| t.1.binary_least();
		(least(x) + least(y) == least(z) + self.k).then_some((x, y, z))
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

	/// Create the constraint `Σ terms ≷ k` over the variables the views are on.
	pub(crate) fn new(
		terms: impl IntoIterator<Item = Term>,
		cmp: Comparator,
		mut k: Coeff,
	) -> Self {
		let terms = terms
			.into_iter()
			.map(|(c, x)| {
				let (c, x, offset) = x.base_term(c);
				k -= offset;
				(c, x)
			})
			.collect();
		Self { terms, cmp, k }
	}

	/// Narrow the domains of the variables of `con` to the values that can
	/// still take part in a solution, up to a fixpoint.
	///
	/// A variable that is already encoded fixes the literals of the values it
	/// loses, see [`IntVar::narrow`].
	pub(crate) fn propagate<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
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
					// `c·x ≷ slack`, turned around when `c` is negative.
					let cmp = if term.0 >= 0 { cmp } else { cmp.reverse() };
					changed |= match cmp {
						Comparator::LessEq => term.1.set_max(db, div_floor(slack, term.0))?,
						_ => term.1.set_min(db, div_ceil(slack, term.0))?,
					};
				}
				if !changed {
					break;
				}
			}
		}
		Ok(())
	}
}

impl From<&NormalizedIntLinear> for IntLinear {
	fn from(con: &NormalizedIntLinear) -> Self {
		Self::new(con.signed_terms(), con.cmp.into(), *con.k)
	}
}

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
		let mut terms = self.signed_terms();
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
		self.cmp
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

	/// Construct a normalised integer linear constraint. A term with
	/// coefficient zero is left out.
	///
	/// # Panics
	///
	/// A term whose least value is not zero, or whose coefficient times the
	/// scale of its view overflows a coefficient.
	pub fn new(
		terms: impl IntoIterator<Item = (PosCoeff, IntVar)>,
		cmp: LimitComp,
		k: PosCoeff,
	) -> Self {
		let terms = terms
			.into_iter()
			.filter(|(c, _)| **c != 0)
			.map(|(c, x)| {
				assert_eq!(
					x.min(),
					0,
					"a normalised constraint counts every term from zero, and {x} does not"
				);
				let (scale, x) = x.into_scaled_shift();
				let c = c
					.checked_mul(scale)
					.expect("a term's coefficient overflows a coefficient");
				(c, x)
			})
			.collect();
		Self { terms, cmp, k }
	}

	/// The terms as the plain [`Term`]s a decomposition works with.
	pub(crate) fn signed_terms(&self) -> impl ExactSizeIterator<Item = Term> + '_ {
		self.terms().map(|(c, x)| (*c, x))
	}

	/// Returns the sum's terms, each a positive coefficient over a view whose
	/// least value is zero.
	pub fn terms(&self) -> impl ExactSizeIterator<Item = (PosCoeff, IntVar)> + '_ {
		self.terms
			.iter()
			.map(|(c, x)| (PosCoeff::new(c.abs()), x.signed(c.signum())))
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::{
		constraint::{
			int_linear::NormalizedIntLinear,
			linear::{LimitComp, PosCoeff},
		},
		decision::integer::IntVar,
		helpers::tests::models,
		Cnf,
	};

	/// A term comes back as a positive coefficient over a view that counts from
	/// zero, worth the same at every value.
	#[test]
	fn a_term_is_given_back_as_it_was_given() {
		for (c, scale, offset) in [(1, 1, 0), (3, 2, 0), (2, -1, 3), (1, -2, 6), (5, 1, 0)] {
			let mut cnf = Cnf::default();
			let x = IntVar::new(0..=3);
			x.require_order_encoding(&mut cnf).unwrap();
			let view = x.clone() * scale + offset;
			let con = NormalizedIntLinear::new(
				[(PosCoeff::new(c), view.clone())],
				LimitComp::LessEq,
				PosCoeff::new(100),
			);
			let [(back_c, ref back)] = con.terms().collect::<Vec<_>>()[..] else {
				panic!("one term in, one term out");
			};
			assert_eq!(back.min(), 0, "{c}·({view}) still counts from zero");
			let seen = models(&cnf, |v| {
				(x.value(v), c * view.value(v), *back_c * back.value(v))
			});
			assert_eq!(seen.len(), 4, "{c}·({view}) over each value of x");
			for (v, given, back) in seen {
				assert_eq!(given, back, "{c}·({view}) at x = {v}");
			}
		}
	}

	/// Every encoder reads a term as what it adds to the sum, so a term that
	/// could take it away is a constraint aggregation should have shifted.
	#[test]
	#[should_panic(expected = "counts every term from zero")]
	fn a_term_reaching_below_zero_is_rejected() {
		let _ = NormalizedIntLinear::new(
			vec![(PosCoeff::new(1), IntVar::new(-1..=3))],
			LimitComp::LessEq,
			PosCoeff::new(3),
		);
	}

	/// A term has to start at zero, which aggregation ensures.
	#[test]
	#[should_panic(expected = "counts every term from zero")]
	fn a_term_starting_above_zero_is_rejected() {
		let _ = NormalizedIntLinear::new(
			vec![(PosCoeff::new(1), IntVar::new(1..=3))],
			LimitComp::LessEq,
			PosCoeff::new(3),
		);
	}

	/// A term worth nothing is left out, rather than read as a view scaled by
	/// zero.
	#[test]
	fn a_term_worth_nothing_is_left_out() {
		let con = NormalizedIntLinear::new(
			[
				(PosCoeff::new(0), IntVar::new(0..=3)),
				(PosCoeff::new(2), IntVar::new(0..=1)),
			],
			LimitComp::LessEq,
			PosCoeff::new(1),
		);
		assert_eq!(con.terms().len(), 1);
	}
}
