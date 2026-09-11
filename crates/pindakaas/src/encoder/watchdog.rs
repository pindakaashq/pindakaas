//! Encoding a linear constraint as a watchdog over the bits of its
//! coefficients.
//!
//! Each term contributes a bit per binary digit of what it is worth. Counting
//! the terms that set a given digit, and carrying half of each count into the
//! digit above, leaves one number whose top digit says whether the bound was
//! passed — the watchdog. The global form uses `O(n·log n·log qₘₐₓ)` variables
//! and `O(n²·log n·log qₘₐₓ)` clauses [^1].
//!
//! A carry drops the low bit of the count below it, so one watchdog over the
//! whole constraint is consistency-checking rather than domain consistent
//! [^1][^2]. Domain consistency is bought back a watchdog at a time: one per
//! value a term can take, over the terms that are left once it does, each
//! ending in a clause rather than an assertion. See
//! [`WatchdogEncoder::with_local`].
//!
//! A term is an integer variable, so a group of mutually exclusive literals
//! reaches this as one variable over the values they stand for — where the
//! caller built one, since aggregation does not look for at-most-one
//! constraints of its own accord. Bucketing that variable's values rather than
//! the literals under it is the generalized watchdog of Bofill et al. [^2], so
//! GGPW and GLPW are what the general case already does.
//!
//! [^1]: O. Bailleux, Y. Boufkhad, O. Roussel, "New Encodings of Pseudo-Boolean
//! Constraints into CNF", SAT 2009, LNCS 5584, 181–194.
//!
//! [^2]: M. Bofill, J. Coll, P. Nightingale, J. Suy, F. Ulrich-Oltean, M.
//! Villaret, "SAT encodings for pseudo-Boolean constraints together with
//! at-most-one constraints", Artificial Intelligence 302 (2022) 103604.

use std::cmp::min;

use itertools::Itertools;

use crate::{
	constraint::{
		bool_linear::NormalizedBoolLinear,
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		count::Count,
		int_linear::{term_max, term_values, Decompose, NormalizedIntLinear, Term},
		int_ternary::{IntTernary, IntTernaryConfig, IntTernaryEncoder},
		linear::{Comparator, LimitComp},
	},
	decision::integer::{Consistency, IntVar},
	helpers::new_named_lit,
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Result, Unsatisfiable,
};

/// A polynomial watchdog (GPW globally, LPW locally).
///
/// The default global form is consistency-checking; [`Self::with_local`]
/// enables domain consistency with a watchdog per term value. Binary
/// cutoffs can weaken this guarantee; see [`Self::with_cutoff`].
///
/// # Examples
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{linear::{Comparator, Linear},
/// #                  int_linear::WatchdogEncoder,
/// #                  linear::{LinAggregator, LinVariant}},
/// #     decision::integer::IntVar, Cnf, Encoder,
/// # };
/// # let mut f = Cnf::default();
/// # let (x, y) = (IntVar::new(0..=5), IntVar::new(0..=5));
/// let con = Linear::new(x * 2 + y * 3, Comparator::LessEq, 10);
/// let LinVariant::Linear(con) = LinAggregator::default().aggregate(&mut f, &con)? else {
///     panic!("a sum of integer terms is a linear constraint");
/// };
/// WatchdogEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WatchdogEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<Coeff>,
	local: bool,
}

/// The variable `⌊x / 2⌋`, which reaches `w` exactly when `x` reaches `2·w`.
///
/// Its literals are `x`'s, every other one, so halving costs nothing.
fn halved<Db: ClauseDatabase + ?Sized>(db: &mut Db, x: &IntVar) -> Result<IntVar, Unsatisfiable> {
	let walk = (0..=(x.max() / 2))
		.map(|w| Ok((w, x.lit_at_least(db, 2 * w)?)))
		.collect::<Result<Vec<_>, Unsatisfiable>>()?;
	IntVar::from_order_walk(db, walk).map(|h| h.with_label(format!("{}/2", x.label())))
}

impl WatchdogEncoder {
	/// A variable over `0..=1` saying whether `2ʳ` is part of what the term is
	/// worth.
	///
	/// One value of the term setting that digit is a literal already; several
	/// need one of their own, implied by each of them. Only the implication is
	/// stated: the count it feeds may stand above the digit but never below
	/// it, which is the side the bound is read from.
	fn digit_of<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		term: &Term,
		r: u32,
		_label: &str,
	) -> Result<Option<IntVar>, Unsatisfiable> {
		let set = term_values(term)
			.into_iter()
			.filter(|&v| v > 0 && (v >> r) & 1 == 1)
			.collect_vec();
		let Some((&first, rest)) = set.split_first() else {
			return Ok(None);
		};
		// The values are of the term, so dividing out the coefficient gives
		// back the value of the variable that reaches them.
		let takes = |db: &mut Db, v: Coeff| term.1.lit_equals(db, v / term.0);
		let digit = if rest.is_empty() {
			takes(db, first)?
		} else {
			let digit = BoolVal::Lit(new_named_lit!(db, format!("{_label}≥2^{r}")));
			for &v in &set {
				let takes = takes(db, v)?;
				db.add_clause([!takes, digit])?;
			}
			digit
		};
		Ok(Some(IntVar::from_order_walk(
			db,
			[(0, BoolVal::Const(true)), (1, digit)],
		)?))
	}

	/// The encoder of the pieces this one decomposes a constraint into.
	fn encoder(&self) -> IntTernaryEncoder {
		IntTernaryEncoder::with_config(IntTernaryConfig {
			propagate: self.add_propagation != Consistency::None,
			cutoff: self.cutoff,
		})
	}

	/// Count `leaves` into one variable, held to `cap`.
	///
	/// A balanced tree of additions, each node standing for at least what its
	/// children come to. A node that cannot stay under `cap` is a sum that
	/// already breaks the bound, so the count is truncated there rather than
	/// carried further.
	fn totalize(
		&self,
		leaves: Vec<IntVar>,
		cap: Coeff,
		_label: &str,
		cons: &mut Vec<IntTernary>,
	) -> Result<IntVar, Unsatisfiable> {
		let mut layer = leaves;
		if layer.is_empty() {
			layer.push(IntVar::new(0..=0));
		}
		// A single leaf is already the count, unless the cap has to bite.
		while layer.len() > 1 || layer[0].max() > cap {
			let mut next = Vec::with_capacity(layer.len().div_ceil(2));
			for (i, pair) in layer.chunks(2).enumerate() {
				let (x, y) = match pair {
					[x] => (x.clone(), IntVar::new(0..=0)),
					[x, y] => (x.clone(), y.clone()),
					_ => unreachable!("leaves are taken two at a time"),
				};
				let (lb, ub) = (x.min() + y.min(), min(x.max() + y.max(), cap));
				if lb > ub {
					return Err(Unsatisfiable);
				}
				let z = IntVar::new(lb..=ub)
					.enforce_consistency(self.add_consistency)
					.with_label(format!("{_label}_{i}"));
				cons.push(IntTernary::new(
					(1, x),
					(1, y),
					Comparator::LessEq,
					(1, z.clone()),
				));
				next.push(z);
			}
			layer = next;
		}
		Ok(layer.pop().expect("a layer holds at least one variable"))
	}

	/// The pieces that together say `Σ terms ≤ k`, or that say so whenever
	/// `guard` fails to hold.
	///
	/// `k + 1` is first raised to a multiple of `2ᵖ` by a padding constant, so
	/// that passing the bound is exactly the top count reaching `m`: the
	/// digits below it are worth less than `2ᵖ` between them and cannot make up
	/// the difference either way. Without a guard the counts are held to what
	/// the bound leaves them, since a count past that is a sum that has already
	/// broken it; under one they are left alone and only the top count is
	/// spoken about, in a clause the guard can satisfy instead.
	fn watchdog<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		terms: &[Term],
		k: Coeff,
		guard: Option<BoolVal>,
		cons: &mut Vec<IntTernary>,
	) -> Result<(), Unsatisfiable> {
		if k < 0 {
			// Nothing can be added to reach a negative bound, so only the
			// guard can save the constraint.
			return match guard {
				Some(g) => db.add_clause([g]),
				None => Err(Unsatisfiable),
			};
		}
		let terms = terms.iter().filter(|t| term_max(t) > 0).collect_vec();
		let sum: Coeff = terms.iter().map(|t| term_max(t)).sum();
		if sum <= k {
			// The bound cannot be passed however the terms fall.
			return Ok(());
		}
		let qmax = terms
			.iter()
			.map(|t| term_max(t))
			.max()
			.expect("a sum that can pass its bound has a term");
		let p = qmax.ilog2();
		// The smallest padding that makes the bound a multiple of the digit
		// the watchdog is read on.
		let pad = ((1 << p) - ((k + 1) % (1 << p))) % (1 << p);
		let total = k + 1 + pad;

		let mut carried: Option<IntVar> = None;
		for r in 0..=p {
			// A digit reaching this threshold already exceeds the bound; under
			// a guard only the last such threshold needs a clause.
			let cap = if guard.is_some() {
				Coeff::MAX
			} else {
				(total >> r) - 1
			};
			let mut leaves = Vec::with_capacity(terms.len() + 1);
			if (pad >> r) & 1 == 1 {
				leaves.push(IntVar::new(1..=1));
			}
			for (i, term) in terms.iter().enumerate() {
				if let Some(digit) = Self::digit_of(db, term, r, &format!("d{i}"))? {
					leaves.push(digit);
				}
			}
			let count = self.totalize(leaves, cap, &format!("b{r}"), cons)?;
			carried = Some(match carried {
				None => count,
				Some(below) => {
					// Half of the count below, which is a view on its literals
					// rather than a variable of its own.
					let half = halved(db, &below)?;
					let (lb, ub) = (count.min() + half.min(), min(count.max() + half.max(), cap));
					if lb > ub {
						return Err(Unsatisfiable);
					}
					let sum = IntVar::new(lb..=ub)
						.enforce_consistency(self.add_consistency)
						.with_label(format!("s{r}"));
					cons.push(IntTernary::new(
						(1, count),
						(1, half),
						Comparator::LessEq,
						(1, sum.clone()),
					));
					sum
				}
			});
		}
		if let Some(g) = guard {
			// The top count reaching `m` is the bound being passed, which the
			// guard is the only other way out of.
			let top = carried.expect("a watchdog has at least one digit");
			let m = total >> p;
			let within = top.lit_at_most(db, m - 1)?;
			db.add_clause([g, within])?;
		}
		Ok(())
	}

	/// The pieces that together say `Σ terms ≤ k`, one watchdog or many.
	fn watchdogs<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		terms: &[Term],
		k: Coeff,
		cons: &mut Vec<IntTernary>,
	) -> Result<(), Unsatisfiable> {
		if !self.local {
			return self.watchdog(db, terms, k, None, cons);
		}
		for (i, term) in terms.iter().enumerate() {
			let rest = terms
				.iter()
				.enumerate()
				.filter(|&(j, _)| j != i)
				.map(|(_, t)| t.clone())
				.collect_vec();
			for v in term_values(term) {
				if v <= 0 {
					continue;
				}
				let guard = !term.1.lit_equals(db, v / term.0)?;
				self.watchdog(db, &rest, k - v, Some(guard), cons)?;
			}
		}
		Ok(())
	}

	/// Independent domain constraints for newly created intermediate views.
	///
	/// Disabled by default. Enables standalone binary and direct consistency
	/// clauses; order-encoding implication chains remain mandatory.
	pub fn with_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}

	/// The domain size at which an unencoded variable prefers binary.
	///
	/// `None` (the default) prefers order; existing binary or order views take
	/// precedence. The threshold is inclusive. Binary arithmetic can weaken
	/// unit propagation; see the [encoding overview](crate::encoder).
	pub fn with_cutoff(&mut self, c: Option<Coeff>) -> &mut Self {
		self.cutoff = c;
		self
	}

	/// Local watchdogs for domain consistency; global is the default.
	///
	/// One watchdog per term value rules it out when the remaining terms exceed
	/// the residual bound. The global form uses one watchdog for the
	/// constraint. The propagation guarantee assumes order arithmetic; binary
	/// cutoffs can weaken it.
	pub fn with_local(&mut self, b: bool) -> &mut Self {
		self.local = b;
		self
	}

	/// Selects domain consistency applied before decomposition; bounds is the
	/// default.
	pub fn with_propagation(&mut self, c: Consistency) -> &mut Self {
		self.add_propagation = c;
		self
	}
}

impl Decompose for WatchdogEncoder {
	/// Bucket the terms by the digits of what they are worth, and carry.
	///
	/// An equality is two watchdogs: one over the terms as they stand, and one
	/// over each of them counted from the far end, which is the same
	/// constraint the other way round.
	fn decompose<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		con: &NormalizedIntLinear,
	) -> Result<Vec<IntTernary>, Unsatisfiable> {
		let terms = con
			.terms()
			.iter()
			.map(|(c, x)| (**c, x.clone()))
			.collect_vec();
		let mut cons = Vec::new();
		self.watchdogs(db, &terms, con.k(), &mut cons)?;
		if con.cmp() == LimitComp::Equal {
			// `Σ c·x ≥ k` is `Σ c·x' ≤ Σ c·(min + max) − k` over the mirrored
			// terms, which is a view on their literals.
			let mut k = -con.k();
			let mut mirrored = Vec::with_capacity(terms.len());
			for (c, x) in &terms {
				k += c * (x.min() + x.max());
				mirrored.push((*c, IntVar::mirrored(db, x)?));
			}
			if k < 0 {
				return Err(Unsatisfiable);
			}
			self.watchdogs(db, &mirrored, k, &mut cons)?;
		}
		Ok(cons)
	}
}

impl Default for WatchdogEncoder {
	fn default() -> Self {
		Self {
			add_consistency: false,
			add_propagation: Consistency::Bounds,
			cutoff: None,
			local: false,
		}
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for WatchdogEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for WatchdogEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Count> for WatchdogEncoder {
	fn encode(&self, db: &mut Db, con: &Count) -> Result {
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db> Encoder<Db, NormalizedBoolLinear> for WatchdogEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	fn encode(&self, db: &mut Db, con: &NormalizedBoolLinear) -> Result {
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for WatchdogEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "watchdog_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		self.encoder().encode_decomposed(db, con, self)
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::{
		helpers::tests::{linear_test_suite, prelude::*},
		solver::{cadical::Cadical, SolveResult, Solver},
		Valuation,
	};

	/// Two values of one term setting the same digit need a literal standing
	/// for the digit, implied by each of them. Only the implication is stated,
	/// so the count read against the bound can stand above the digit but never
	/// below it.
	#[test]
	fn a_digit_two_values_reach_is_implied_by_both() {
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();
		// Three and five both set the low digit, and only the three leaves
		// room for the four.
		let con = NormalizedIntLinear::new(
			vec![
				(
					PosCoeff::new(1),
					at_most_one_var(
						&mut cnf,
						&[(a, PosCoeff::new(3)), (b, PosCoeff::new(5))],
						"x0",
						false,
					)
					.unwrap(),
				),
				(
					PosCoeff::new(1),
					at_most_one_var(&mut cnf, &[(c, PosCoeff::new(4))], "x1", false).unwrap(),
				),
			],
			LimitComp::LessEq,
			PosCoeff::new(7),
		);
		WatchdogEncoder::default().encode(&mut cnf, &con).unwrap();

		let mut seen = Vec::new();
		let mut slv = Cadical::from(&cnf);
		let watched = cnf.get_variables();
		while let SolveResult::Satisfied(value) = slv.solve() {
			seen.push((value.value(a), value.value(b), value.value(c)));
			let no_good = watched
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
		seen.sort();
		seen.dedup();
		// Three fits beside the four and five does not, which is only visible
		// if the two of them are told apart at the digit they share.
		assert_eq!(
			seen,
			vec![
				(false, false, false),
				(false, false, true),
				(false, true, false),
				(true, false, false),
				(true, false, true),
			]
		);
	}

	/// A sum that cannot reach its bound is not worth a watchdog, and the
	/// local form asks for one per value, so the saving is per value too.
	#[test]
	fn a_sum_that_cannot_pass_its_bound_costs_nothing() {
		for local in [false, true] {
			let mut cnf = Cnf::default();
			let (a, b, c) = cnf.new_lits();
			// Three, five and four come to twelve at most, which the bound
			// already allows.
			let con = NormalizedIntLinear::new(
				construct_terms(&mut cnf, &[(a, 3), (b, 5), (c, 4)]),
				LimitComp::LessEq,
				PosCoeff::new(12),
			);
			let vars = cnf.num_vars();
			let mut enc = WatchdogEncoder::default();
			let _ = enc.with_local(local);
			enc.encode(&mut cnf, &con).unwrap();
			assert_eq!(cnf.num_clauses(), 0, "local: {local}");
			assert_eq!(cnf.num_vars(), vars, "local: {local}");
		}
	}

	/// The point of the watchdog is that a coefficient costs its bit width
	/// rather than its magnitude, so guard against a change that would make it
	/// pointless.
	#[test]
	fn smaller_than_the_totalizer() {
		const N: usize = 20;
		let coeffs = (0..N as Coeff).map(|i| 1 + i * 65_537).collect_vec();
		let k = coeffs.iter().sum::<Coeff>() / 2;
		let con =
			|vars: &[Lit]| Linear::new(LinExp::from_slices(&coeffs, vars), Comparator::LessEq, k);

		let mut gt = Cnf::default();
		let vars = gt.new_var_range(N).iter_lits().collect_vec();
		LinearEncoder::<StaticLinEncoder<TotalizerEncoder, TotalizerEncoder>>::default()
			.encode(&mut gt, &con(&vars))
			.unwrap();

		let mut gpw = Cnf::default();
		let vars = gpw.new_var_range(N).iter_lits().collect_vec();
		LinearEncoder::<StaticLinEncoder<WatchdogEncoder, WatchdogEncoder>>::default()
			.encode(&mut gpw, &con(&vars))
			.unwrap();

		assert!(
			gpw.num_vars() < gt.num_vars(),
			"expected fewer variables than the totalizer, got {} instead of {}",
			gpw.num_vars(),
			gt.num_vars()
		);
		assert!(
			gpw.num_clauses() < gt.num_clauses(),
			"expected fewer clauses than the totalizer, got {} instead of {}",
			gpw.num_clauses(),
			gt.num_clauses()
		);
	}

	card1_test_suite! {
		watchdog_encoder_card1, WatchdogEncoder::default()
	}
	linear_test_suite!(watchdog_encoder, WatchdogEncoder::default());

	linear_test_suite!(
		watchdog_encoder_local,
		WatchdogEncoder::default().with_local(true)
	);
	linear_test_suite!(
		watchdog_encoder_no_prop,
		WatchdogEncoder::default().with_propagation(crate::decision::integer::Consistency::None)
	);
	linear_test_suite!(
		watchdog_encoder_prop_doms,
		WatchdogEncoder::default().with_propagation(crate::decision::integer::Consistency::Domain)
	);
	linear_test_suite!(
		watchdog_encoder_consistency,
		WatchdogEncoder::default().with_consistency(true)
	);
	linear_test_suite!(
		watchdog_encoder_binary,
		WatchdogEncoder::default().with_cutoff(Some(0))
	);
}
