//! Counting literals, or adding up weighted terms, through a network of
//! comparators.
//!
//! Each merge is either stated outright or halved and recursed on — see
//! [`SortingNetworkStrategy`] — and the leaves become ternary integer
//! constraints. Each sub-sorter is built only as wide as the bound above it can
//! use, which is what makes this the cardinality network of Asín et al. [^1]
//! rather than a full sorter; the merges between them are not truncated.
//!
//! A weighted term enters as the integer it is: a literal worth `w` is a
//! variable over `{0, w}`, which the merges add up like any other. What a merge
//! comes to is kept as every value up to the bound, so the network grows with
//! the bound rather than with the number of terms.
//!
//! Domain consistent on unit weights [^1].
//!
//! [^1]: R. Asín, R. Nieuwenhuis, A. Oliveras, E. Rodríguez-Carbonell,
//! "Cardinality Networks: a theoretical and empirical study", Constraints
//! 16(2) (2011) 195–221.

use std::{cmp::min, fmt::Display, hash, mem, ops::RangeInclusive, sync::Mutex};

use rustc_hash::FxHashMap;

use crate::{
	constraint::{
		bool_linear::NormalizedBoolLinear,
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		count::Count,
		int_linear::NormalizedIntLinear,
		int_ternary::{IntTernary, IntTernaryEncoder},
		linear::LimitComp,
	},
	decision::integer::IntVar,
	ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Result, Unsatisfiable,
};

#[derive(Debug)]
/// A cardinality network sized by the bound rather than the input.
///
/// # Warning
/// The encoder structure contains a cache for computing node costs that is used
/// when using a mixed strategy. This cache is not considered when comparing two
/// encoders for equality, when hashing, or when cloning. This could, for
/// example, mean that a cloned encoder might lead to a degradation in
/// performance.
///
/// # Examples
///
/// ```rust
/// use pindakaas::{
///     constraint::{count::Count, linear::LimitComp}, decision::integer::IntVar,
///     encoder::sorting_network::SortingNetworkEncoder, ClauseDatabase, Cnf, Encoder,
/// };
/// let mut cnf = Cnf::default();
/// let lits = cnf.new_var_range(8).map(Into::into).collect();
/// let constraint = Count::new(lits, LimitComp::Equal, IntVar::new(0..=8));
/// SortingNetworkEncoder::default().encode(&mut cnf, &constraint)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
pub struct SortingNetworkEncoder {
	add_consistency: bool,
	strategy: SortingNetworkStrategy,
	strategy_cost_cache: Mutex<StrategyCache>,
}

/// How [`SortingNetworkEncoder`] merges two sorted halves.
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum SortingNetworkStrategy {
	/// State the result of the merge outright, a clause per pair of values.
	Direct,
	/// Halve the inputs, merge each half, and comparator the results together.
	Recursive,
	/// Whichever of the two is cheaper for the merge at hand, by a cost model
	/// that counts clauses and literals and weighs literals by the given
	/// factor.
	Mixed(u32),
}

type StrategyCache = FxHashMap<(u128, u128, u128), (SortingNetworkStrategy, (u128, u128))>;

impl SortingNetworkEncoder {
	/// A variable over what `x` and `y` can come to together, up to `ub`, or
	/// `None` when they cannot stay within it.
	fn capped_sum(&self, x: &IntVar, y: &IntVar, ub: Coeff) -> Option<IntVar> {
		let (lb, ub) = (x.min() + y.min(), min(x.max() + y.max(), ub));
		(lb <= ub).then(|| self.sum([x, y], lb..=ub, format_args!("{}+{}", x.label(), y.label())))
	}

	/// One step of a merge: what `x` and `y` reach between them, `z` reaches.
	fn comp<Db>(
		&self,
		db: &mut Db,
		x: &IntVar,
		y: &IntVar,
		cmp: &LimitComp,
		z: &IntVar,
		c: Coeff,
	) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		let (x, y) = (x.at_least(db, c)?, y.at_least(db, c + 1)?);
		let (z1, z2) = (z.at_least(db, c + c)?, z.at_least(db, c + c + 1)?);

		db.add_clause([!x, z1])?;
		db.add_clause([!y, z1])?;
		db.add_clause([!x, !y, z2])?;
		if cmp == &LimitComp::Equal {
			db.add_clause([x, !z2])?;
			db.add_clause([y, !z2])?;
			db.add_clause([x, y, !z1])?;
		}
		Ok(())
	}

	/// Constrain `z` to be what `x` and `y` come to together.
	///
	/// A variable with a single value has nothing to merge, and merging it
	/// anyway would not converge, since halving leaves it unchanged. So
	/// once any of the three is fixed, the constraint is stated outright. The
	/// two inputs are checked alike even though the corpus only exercises the
	/// first: the alternative to a redundant check here is a hang.
	pub(crate) fn merge<Db>(
		&self,
		db: &mut Db,
		x: &IntVar,
		y: &IntVar,
		cmp: &LimitComp,
		z: &IntVar,
	) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		if x.card() == 1 || y.card() == 1 || z.card() == 1 {
			self.ternary(db, x, y, cmp, z)
		} else {
			self.merged(db, x, y, cmp, z)
		}
	}

	/// Merge `x` and `y` into `z` a bit at a time, or state the addition
	/// outright where that is cheaper.
	fn merged<Db>(&self, db: &mut Db, x: &IntVar, y: &IntVar, cmp: &LimitComp, z: &IntVar) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		let (a, b, c) = (x.max(), y.max(), z.max());
		let strat = if let SortingNetworkStrategy::Mixed(lambda) = &self.strategy {
			let mut cache = self.strategy_cost_cache.lock().unwrap();
			SortingNetworkStrategy::mixed_cost(&mut cache, a as u128, b as u128, c as u128, *lambda)
				.0
		} else {
			self.strategy.clone()
		};

		match strat {
			SortingNetworkStrategy::Direct => self.ternary(db, x, y, cmp, z),
			SortingNetworkStrategy::Recursive => {
				if a == 0 && b == 0 {
					Ok(())
				} else if a == 1 && b == 1 && c <= 2 {
					self.smerge(db, x, y, cmp, z)
				} else {
					let (x_floor, y_floor) = (IntVar::halved(db, x)?, IntVar::halved(db, y)?);
					let (x_up, y_up) = (x.clone() + 1, y.clone() + 1);
					let (x_ceil, y_ceil) = (IntVar::halved(db, &x_up)?, IntVar::halved(db, &y_up)?);

					// The halves add up to `z ≤ c` and differ by two at most:
					// the floor half is at most `c/2`, the ceiling `c/2 + 1`.
					let (Some(z_floor), Some(z_ceil)) = (
						self.capped_sum(&x_floor, &y_floor, c / 2),
						self.capped_sum(&x_ceil, &y_ceil, c / 2 + 1),
					) else {
						return db.contradiction();
					};
					self.merge(db, &x_floor, &y_floor, cmp, &z_floor)?;
					self.merge(db, &x_ceil, &y_ceil, cmp, &z_ceil)?;

					(0..=c / 2).try_for_each(|i| self.comp(db, &z_floor, &z_ceil, cmp, z, i))
				}
			}
			SortingNetworkStrategy::Mixed(_) => {
				unreachable!("a strategy is settled before it is used")
			}
		}
	}

	/// The base case, `x{0,1} + y{0,1} ≷ z{0,1,2}`.
	fn smerge<Db>(&self, db: &mut Db, x: &IntVar, y: &IntVar, cmp: &LimitComp, z: &IntVar) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		// `y` stands in for the half that rounds up, so both sides move along
		// by one to meet it.
		let (y, z) = (y.clone() + 1, z.clone() + 1);
		self.comp(db, x, &y, cmp, &z, 1)
	}

	/// Sort `xs` into a variable for what they come to together, up to `max`.
	fn sort<Db>(
		&self,
		db: &mut Db,
		xs: &[IntVar],
		cmp: &LimitComp,
		max: Coeff,
		label: String,
	) -> Result<Option<IntVar>, Unsatisfiable>
	where
		Db: ClauseDatabase + ?Sized,
	{
		Ok(match xs {
			[] => None,
			[x] => Some(x.clone()),
			xs => {
				let y = self.sum(xs, 0..=max, label);
				self.sorted(db, xs, cmp, &y)?;
				Some(y)
			}
		})
	}

	/// Constrain `y` to be what `xs` come to together.
	pub(crate) fn sorted<Db>(
		&self,
		db: &mut Db,
		xs: &[IntVar],
		cmp: &LimitComp,
		y: &IntVar,
	) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		let zero = || IntVar::new(0..=0).with_label("0");
		match xs {
			[] => self.ternary(db, &zero(), &zero(), cmp, y),
			[x] => self.ternary(db, x, &zero(), cmp, y),
			[x1, x2] if x1.max() == 1 && x2.max() == 1 && y.max() <= 2 => {
				self.smerge(db, x1, x2, cmp, y)
			}
			xs => {
				let n = xs.len() / 2;
				let y1 = self.sort(
					db,
					&xs[..n],
					cmp,
					min(xs[..n].iter().map(IntVar::max).sum(), y.max()),
					String::from("y1"),
				)?;
				let y2 = self.sort(
					db,
					&xs[n..],
					cmp,
					min(xs[n..].iter().map(IntVar::max).sum(), y.max()),
					String::from("y2"),
				)?;
				match (y1, y2) {
					(Some(y1), Some(y2)) => self.merged(db, &y1, &y2, cmp, y),
					_ => Ok(()),
				}
			}
		}
	}

	/// A variable over `domain` for what `addends` come to together.
	///
	/// Without consistency, the order consistency constraint is left out when
	/// no addend skips a value or is read on direct literals that say less
	/// than its order literals, since the merges then state every value the
	/// sum reaches.
	pub(crate) fn sum<'a>(
		&self,
		addends: impl IntoIterator<Item = &'a IntVar>,
		domain: RangeInclusive<Coeff>,
		label: impl Display,
	) -> IntVar {
		// The network creates no direct encodings, so an addend read on its
		// order literals now still is when merged.
		let states_every_value = |x: &IntVar| {
			x.card() as Coeff == x.max() - x.min() + 1 && (x.card() <= 2 || !x.is_read_directly())
		};
		let sum = IntVar::new(domain)
			.enforce_consistency(self.add_consistency)
			.with_label(label);
		if self.add_consistency || !addends.into_iter().all(states_every_value) {
			sum
		} else {
			sum.without_order_consistency()
		}
	}

	/// Encode `x + y ≷ z` as the linear constraint it is.
	fn ternary<Db>(
		&self,
		db: &mut Db,
		x: &IntVar,
		y: &IntVar,
		cmp: &LimitComp,
		z: &IntVar,
	) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		IntTernaryEncoder::default().encode(
			db,
			&IntTernary::new(
				(1, x.clone()),
				(1, y.clone()),
				(*cmp).into(),
				(1, z.clone()),
			),
		)
	}

	/// Configures whether intermediate variables are constrained independently
	/// of the merges; disabled by default.
	///
	/// Disabled, a sum has no order consistency constraint unless an addend
	/// skips a value, or is read on its direct literals and has more than two
	/// values. Enabled, the network is larger, but on a pigeonhole instance
	/// CaDiCaL needed a half to a fifth of the conflicts.
	pub fn with_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}

	/// Selects the merge strategy; the default is
	/// [`SortingNetworkStrategy::Mixed`] with weight 10.
	pub fn with_strategy(&mut self, strategy: SortingNetworkStrategy) -> &mut Self {
		self.strategy = strategy;
		self
	}
}

impl Clone for SortingNetworkEncoder {
	fn clone(&self) -> Self {
		Self {
			add_consistency: self.add_consistency,
			strategy: self.strategy.clone(),
			strategy_cost_cache: Mutex::default(),
		}
	}
}

impl Default for SortingNetworkEncoder {
	fn default() -> Self {
		Self {
			strategy: SortingNetworkStrategy::Mixed(10),
			add_consistency: false,
			strategy_cost_cache: Mutex::default(),
		}
	}
}

impl<Db> Encoder<Db, Cardinality> for SortingNetworkEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "sorting_network_encoder", skip_all, fields(constraint = card.trace_print()))
	)]
	fn encode(&self, db: &mut Db, card: &Cardinality) -> Result {
		let k: Coeff = card.rhs();
		let y = IntVar::new(k..=k).with_label("k");
		self.encode(db, &Count::new(card.lits.clone(), card.cmp, y))
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for SortingNetworkEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Count> for SortingNetworkEncoder {
	fn encode(&self, db: &mut Db, count: &Count) -> Result {
		let xs = count
			.lits
			.iter()
			.enumerate()
			.map(|(i, &x)| {
				IntVar::from_order_encoding(0..=1, &[x]).with_label(format_args!("x_{}", i + 1))
			})
			.collect::<Vec<_>>();
		// The network only states the counts the literals reach, so a bound
		// below zero is ruled out here.
		let reached = count.y.at_least(db, 0)?;
		db.add_clause([reached])?;
		self.sorted(db, &xs, &count.cmp, &count.y)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, NormalizedBoolLinear> for SortingNetworkEncoder {
	fn encode(&self, db: &mut Db, con: &NormalizedBoolLinear) -> Result {
		let con = con.as_int_linear();
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, NormalizedIntLinear> for SortingNetworkEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "sorting_network_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		let xs = con.terms().map(|(c, x)| x * *c).collect::<Vec<_>>();
		let y = IntVar::new(*con.k..=*con.k).with_label("k");
		self.sorted(db, &xs, &con.cmp, &y)
	}
}

impl Eq for SortingNetworkEncoder {}

impl PartialEq for SortingNetworkEncoder {
	fn eq(&self, other: &Self) -> bool {
		// Deconstruct the two structs to ensure no additional fields are
		// ignored if they are ever added
		let &Self {
			add_consistency: a1,
			strategy: b1,
			strategy_cost_cache: _, // Ignore the cache for equality comparison
		} = &self;
		let &Self {
			add_consistency: a2,
			strategy: b2,
			strategy_cost_cache: _,
		} = &other;
		a1 == a2 && b1 == b2
	}
}

impl hash::Hash for SortingNetworkEncoder {
	fn hash<H: hash::Hasher>(&self, state: &mut H) {
		// Deconstruct the struct to ensure no additional fields are ignored if
		// they are ever added
		let &Self {
			add_consistency,
			strategy,
			strategy_cost_cache: _, // Ignore the cache for hashing
		} = &self;
		add_consistency.hash(state);
		strategy.hash(state);
	}
}

impl SortingNetworkStrategy {
	/// Calculate the cost of the direct strategy for the given upper bounds of
	/// the integer variables.
	fn direct_cost(a: u128, b: u128, c: u128) -> (u128, u128) {
		if a <= c && b <= c && a + b > c {
			(
				c,
				(a + b) * c - ((c * (c - 1)) / 2) - ((a * (a - 1)) / 2) - ((b * (b - 1)) / 2),
			)
		} else {
			(a + b, a * b + a + b)
		}
	}
	/// Calculate the cost of both the direct and recursive strategies for the
	/// given upper bounds of the integer variables, and return the best
	/// strategy and its cost using the given lambda to bias the comparison.
	fn mixed_cost(
		cache: &mut StrategyCache,
		mut a: u128,
		mut b: u128,
		c: u128,
		lambda: u32,
	) -> (SortingNetworkStrategy, (u128, u128)) {
		if a > b {
			mem::swap(&mut a, &mut b);
		}
		let key = (a, b, c);
		if let Some(cached) = cache.get(&key) {
			return cached.clone();
		}

		// TODO safely use floating point for lambda
		let lambda_fn = |(v, c): (u128, u128), lambda: u32| -> u128 { (v * lambda as u128) + c };

		let dir_cost = Self::direct_cost(a, b, c);
		// `merge` states a merge into a cap of zero outright, and halving it
		// again would leave the recursive cost a cap below zero.
		let ret = if c == 0 && (a > 0 || b > 1) {
			(SortingNetworkStrategy::Direct, dir_cost)
		} else {
			let rec_cost = Self::recursive_cost(cache, a, b, c, lambda);
			if lambda_fn(dir_cost, lambda) < lambda_fn(rec_cost, lambda) {
				(SortingNetworkStrategy::Direct, dir_cost)
			} else {
				(SortingNetworkStrategy::Recursive, rec_cost)
			}
		};

		let _ = cache.insert(key, ret.clone());
		ret
	}

	/// Calculate the cost of the recursive strategy for the given upper bounds
	/// of the integer variables.
	fn recursive_cost(
		cache: &mut StrategyCache,
		a: u128,
		b: u128,
		c: u128,
		lambda: u32,
	) -> (u128, u128) {
		match (a, b, c) {
			(0, 0, _) => (0, 0),
			(1, 0, _) => unreachable!(),
			(0, 1, _) => (0, 0),
			(1, 1, 1) => (1, 2),
			(1, 1, 2) => (2, 3),
			(a, b, c) => {
				let ((_, (v1, c1)), (_, (v2, c2)), (v3, c3)) = (
					Self::mixed_cost(cache, a.div_ceil(2), b.div_ceil(2), c / 2 + 1, lambda),
					Self::mixed_cost(cache, a / 2, b / 2, c / 2, lambda),
					(
						c - 1,
						if c % 2 == 1 {
							(3 * c - 3) / 2
						} else {
							((3 * c - 2) / 2) + 2
						},
					),
				);
				(v1 + v2 + v3, c1 + c2 + c3)
			}
		}
	}
}

#[cfg(test)]
mod tests {
	macro_rules! sorted_card_test_suite {
		($encoder:expr,$cmp:expr) => {
			use traced_test::test;

			use crate::helpers::tests::prelude::*;

			#[test]
			fn card_2_1() {
				test_card!($encoder, 2, $cmp, 1);
			}

			#[test]
			fn card_2_2() {
				test_card!($encoder, 2, $cmp, 2);
			}

			#[test]
			fn card_3_1() {
				test_card!($encoder, 3, $cmp, 1);
			}

			#[test]
			fn card_3_2() {
				test_card!($encoder, 3, $cmp, 2);
			}

			#[test]
			fn card_3_3() {
				test_card!($encoder, 3, $cmp, 3);
			}

			#[test]
			fn card_4_2() {
				test_card!($encoder, 4, $cmp, 2);
			}

			#[test]
			fn card_4_3() {
				test_card!($encoder, 4, $cmp, 3);
			}

			#[test]
			fn card_4_4() {
				test_card!($encoder, 4, $cmp, 4);
			}

			#[test]
			fn card_5_3() {
				test_card!($encoder, 5, $cmp, 3);
			}

			#[test]
			fn card_6_1() {
				test_card!($encoder, 6, $cmp, 1);
			}

			#[test]
			fn card_5_2() {
				test_card!($encoder, 5, $cmp, 1);
			}
		};
	}

	macro_rules! test_card {
		($encoder:expr,$n:expr,$cmp:expr,$k:expr) => {
			let mut cnf = Cnf::default();
			let vars = cnf.new_var_range($n).iter_lits().collect_vec();
			$encoder
				.encode(
					&mut cnf,
					&Cardinality {
						lits: vars.clone(),
						cmp: $cmp,
						k: PosCoeff::new($k),
					},
				)
				.unwrap();

			let expect = expect_file![format!(
				"cardinality/sorting_network/test_card_{}_{}_{}.sol",
				$n,
				$k,
				match $cmp {
					LimitComp::LessEq => "le",
					LimitComp::Equal => "eq",
				}
			)];
			assert_solutions(&cnf, vars, &expect);
		};
	}

	use std::num::NonZeroI32;

	use itertools::{iproduct, Itertools};
	use rangelist::RangeList;
	use traced_test::test;

	use crate::{
		constraint::{
			count::{Count, SortingNetworkEncoder, SortingNetworkStrategy},
			int_linear::{lit_terms, NormalizedIntLinear},
			linear::{LimitComp, PosCoeff},
		},
		decision::integer::IntVar,
		encoder::sorting_network::StrategyCache,
		helpers::tests::{
			assert_count_admits, assert_solutions, brute_force, encoded_var, expect_file,
			linear_test_suite, models, models_over,
		},
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Coeff, Encoder, Lit, Unsatisfiable, Var,
		VarRange,
	};

	/// A direct guard says that its addend takes a value, not that it reaches
	/// every value below it, so a sum it adds to keeps its order consistency.
	#[test]
	fn a_direct_addend_bounds_a_sum_without_consistency() {
		// Three values are the fewest for which a direct literal says less
		// than an order literal does.
		let values: [&[Coeff]; 2] = [&[0, 1, 2], &[0, 1, 2, 3]];
		for (strategy, cmp, w, (d1, d2), values) in itertools::iproduct!(
			[
				SortingNetworkStrategy::Direct,
				SortingNetworkStrategy::Recursive,
				SortingNetworkStrategy::Mixed(10),
			],
			[LimitComp::LessEq, LimitComp::Equal],
			// A direct value loses only the sum's literals between it and the
			// other addend, which a weight of `K` asks for with three values.
			[3, 8, 9],
			[(true, false), (false, true), (true, true)],
			values
		) {
			const K: Coeff = 9;
			let mut cnf = Cnf::default();
			let mut lits = Vec::new();
			let x1 = encoded_var(&mut cnf, values, d1, &mut lits);
			let x2 = encoded_var(&mut cnf, values, d2, &mut lits);
			let b = cnf.new_lit();
			lits.push(b);
			// The weighted literal comes first, as the aggregator leaves it.
			let mut terms = lit_terms([(b, PosCoeff::new(w))]);
			terms.extend([x1.clone(), x2.clone()].map(|x| (PosCoeff::new(1), x)));
			let encoded = get_sorted_encoder(strategy.clone()).encode(
				&mut cnf,
				&NormalizedIntLinear::new(terms, cmp, PosCoeff::new(K)),
			);

			let mut seen = models_over(&cnf, &lits, |value| {
				vec![
					x1.value(value),
					x2.value(value),
					Coeff::from(value.value(b)),
				]
			});
			seen.sort_unstable();
			let domain = RangeList::from_sorted_elements(values.to_vec());
			let doms = [domain.clone(), domain, RangeList::from(0..=1)];
			let allowed = brute_force(&[1, 1, w], &doms, cmp.into(), K);
			assert_eq!(
				seen, allowed,
				"{strategy:?} {cmp:?} {w} {values:?} direct {d1} {d2}"
			);
			assert!(encoded.is_ok() || allowed.is_empty());
		}
	}

	#[test]
	fn a_direct_count_at_most_admits_what_the_constraint_does() {
		assert_counts_admit(SortingNetworkStrategy::Direct, LimitComp::LessEq);
	}

	#[test]
	fn a_direct_count_equal_admits_what_the_constraint_does() {
		assert_counts_admit(SortingNetworkStrategy::Direct, LimitComp::Equal);
	}

	/// A literal read on its direct encoding says what its order encoding
	/// does, so the sums it adds to cost no more than for an order literal.
	#[test]
	fn a_direct_literal_costs_what_an_order_literal_does() {
		for (coefs, k) in [(&[2, 1, 1][..], 2), (&[3, 1, 1, 1, 1], 4)] {
			let [direct, order] = [true, false].map(|direct| {
				let mut cnf = Cnf::default();
				let lits = cnf.new_var_range(coefs.len()).iter_lits().collect_vec();
				let terms = if direct {
					let weighted = lits.iter().zip(coefs).map(|(&l, &c)| (l, PosCoeff::new(c)));
					lit_terms(weighted)
				} else {
					let to_term = |(&l, &c)| {
						let x = IntVar::from_order_encoding(0..=1, &[l]);
						(PosCoeff::new(c), x)
					};
					lits.iter().zip(coefs).map(to_term).collect_vec()
				};
				let con = NormalizedIntLinear::new(terms, LimitComp::LessEq, PosCoeff::new(k));
				SortingNetworkEncoder::default()
					.encode(&mut cnf, &con)
					.unwrap();
				(cnf.num_vars(), cnf.num_clauses())
			});
			assert_eq!(direct, order, "{coefs:?} {k}");
		}
	}

	/// A merge into a cap of zero is stated outright, which is the cheaper
	/// way, so the mixed strategy picks it too.
	#[test]
	fn a_merge_into_a_cap_of_zero_costs_what_the_direct_one_does() {
		let [direct, mixed] = [
			SortingNetworkStrategy::Direct,
			SortingNetworkStrategy::Mixed(10),
		]
		.map(|strategy| {
			let mut cnf = Cnf::default();
			let terms = [0..=3, 0..=3].map(|d| (PosCoeff::new(1), IntVar::new(d)));
			let con = NormalizedIntLinear::new(terms.to_vec(), LimitComp::LessEq, PosCoeff::new(0));
			get_sorted_encoder(strategy).encode(&mut cnf, &con).unwrap();
			(cnf.num_vars(), cnf.num_clauses())
		});
		assert_eq!(mixed, direct);
	}

	/// The watchdog merges counts that start above zero, such as a padding
	/// digit plus a term, so every strategy must handle a nonzero minimum.
	#[test]
	fn a_merge_of_counts_that_start_above_zero_bounds_their_sum() {
		for strategy in [
			SortingNetworkStrategy::Direct,
			SortingNetworkStrategy::Recursive,
			SortingNetworkStrategy::Mixed(10),
		] {
			for ((x_min, x_max), (y_min, y_max), cap) in [
				((1, 3), (0, 4), 5),
				((1, 8), (0, 8), 9),
				((2, 6), (1, 5), 8),
				((1, 4), (1, 4), 8),
			] {
				let mut cnf = Cnf::default();
				let x = IntVar::new(x_min..=x_max);
				let y = IntVar::new(y_min..=y_max);
				let z = IntVar::new(x_min + y_min..=cap);
				get_sorted_encoder(strategy.clone())
					.merge(&mut cnf, &x, &y, &LimitComp::LessEq, &z)
					.unwrap();
				let lits = order_literals(&mut cnf, [&x, &y, &z]);

				let mut seen = models_over(&cnf, &lits, |value| {
					[&x, &y, &z].map(|v| v.value(value)).to_vec()
				});
				seen.sort_unstable();
				// `z` stands for at least `x + y`, within its domain.
				let allowed = [&x, &y, &z]
					.iter()
					.map(|v| v.min()..=v.max())
					.multi_cartesian_product()
					.filter(|v| v[0] + v[1] <= v[2])
					.sorted()
					.collect_vec();
				assert_eq!(
					seen, allowed,
					"{strategy:?} x {x_min}..={x_max} y {y_min}..={y_max} cap {cap}"
				);
			}
		}
	}

	/// The cost model prices a merge whose inputs reach past its cap, which
	/// halving can bring down to a cap of zero.
	#[test]
	fn a_merge_past_its_cap_has_a_cost() {
		let mut cache = StrategyCache::default();
		for (a, b, c) in itertools::iproduct!(0..=12, 0..=12, 0..=12) {
			let _ = SortingNetworkStrategy::mixed_cost(&mut cache, a, b, c, 10);
		}
	}

	#[test]
	fn a_merge_past_the_bound_is_a_contradiction() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (IntVar::new(3..=5), IntVar::new(3..=5), IntVar::new(0..=4));
		assert_eq!(
			get_sorted_encoder(SortingNetworkStrategy::Recursive).merged(
				&mut cnf,
				&x,
				&y,
				&LimitComp::LessEq,
				&z
			),
			Err(Unsatisfiable)
		);
		assert!(models(&cnf, |_| ()).is_empty());
	}

	#[test]
	fn a_mixed_count_at_most_admits_what_the_constraint_does() {
		assert_counts_admit(SortingNetworkStrategy::Mixed(10), LimitComp::LessEq);
	}

	#[test]
	fn a_mixed_count_equal_admits_what_the_constraint_does() {
		assert_counts_admit(SortingNetworkStrategy::Mixed(10), LimitComp::Equal);
	}

	#[test]
	fn a_recursive_count_at_most_admits_what_the_constraint_does() {
		assert_counts_admit(SortingNetworkStrategy::Recursive, LimitComp::LessEq);
	}

	#[test]
	fn a_recursive_count_equal_admits_what_the_constraint_does() {
		assert_counts_admit(SortingNetworkStrategy::Recursive, LimitComp::Equal);
	}

	#[test]
	fn an_at_most_merge_half_holds_only_values_within_the_bound() {
		assert_merge_halves_within_the_bound(LimitComp::LessEq);
	}

	#[test]
	fn an_equal_merge_half_holds_only_values_within_the_bound() {
		assert_merge_halves_within_the_bound(LimitComp::Equal);
	}

	/// Assert that a count of up to seven literals admits exactly what its
	/// bound does, at every bound from below nothing to past the literals.
	fn assert_counts_admit(strategy: SortingNetworkStrategy, cmp: LimitComp) {
		for n in 0..=7 {
			let mut domains = (0..=n + 1).map(|k| RangeList::from(k..=k)).collect_vec();
			domains.extend([
				RangeList::from(0..=n),
				RangeList::from(2..=n + 2),
				RangeList::from(-1..=1),
				RangeList::from(-2..=-1),
			]);
			for domain in domains {
				let encoder = get_sorted_encoder(strategy.clone());
				assert_count_admits(n as usize, domain, cmp, |cnf, con| encoder.encode(cnf, con));
			}
		}
	}

	/// Assert that a recursive merge into `z ≤ c` gives each half no value
	/// that already puts `z` past `c`.
	///
	/// A half with such a value has a literal no model can set, which the
	/// comparators then rule out one unit clause at a time.
	fn assert_merge_halves_within_the_bound(cmp: LimitComp) {
		for (a, b) in iproduct!(1..=9, 1..=9) {
			for c in 1..a + b {
				let mut cnf = Cnf::default();
				let x = IntVar::new(0..=a);
				let y = IntVar::new(0..=b);
				let z = IntVar::new(0..=c);
				for v in [&x, &y, &z] {
					v.require_order_encoding(&mut cnf).unwrap();
				}
				let (vars, clauses) = (cnf.num_vars(), cnf.num_clauses());
				get_sorted_encoder(SortingNetworkStrategy::Recursive)
					.merged(&mut cnf, &x, &y, &cmp, &z)
					.unwrap();
				// A unit on an input is the bound itself, as `x` past `c` is.
				let dead = cnf
					.iter()
					.skip(clauses)
					.filter(|clause| {
						clause.len() == 1 && i32::from(clause[0].var()) as usize > vars
					})
					.count();
				assert_eq!(dead, 0, "merging 0..={a} and 0..={b} into 0..={c}");
			}
		}
	}

	fn get_sorted_encoder(strategy: SortingNetworkStrategy) -> SortingNetworkEncoder {
		SortingNetworkEncoder {
			strategy,
			..SortingNetworkEncoder::default()
		}
	}

	/// Without consistency, a sum leaves out its order consistency constraint
	/// only when no addend skips a value, so order-encoded integers with and
	/// without holes in their domains, starting at zero and above it, must
	/// all add up to exactly the bound either way.
	#[test]
	fn integers_with_and_without_holes_add_up_to_the_bound() {
		let domains: [&[Coeff]; 4] = [&[0, 1, 2, 3], &[1, 2, 3], &[0, 2, 3], &[0, 1, 3, 4]];
		for (strategy, consistency) in [
			SortingNetworkStrategy::Direct,
			SortingNetworkStrategy::Recursive,
			SortingNetworkStrategy::Mixed(10),
		]
		.into_iter()
		.cartesian_product([true, false])
		{
			for (cmp, k) in [LimitComp::LessEq, LimitComp::Equal]
				.into_iter()
				.cartesian_product(4..=8)
			{
				for doms in domains.iter().combinations_with_replacement(3) {
					let mut cnf = Cnf::default();
					let terms = doms
						.iter()
						.map(|d| {
							let x = IntVar::new(RangeList::from_sorted_elements(d.to_vec()));
							x.require_order_encoding(&mut cnf).unwrap();
							(PosCoeff::new(1), x)
						})
						.collect_vec();
					let lits = order_literals(&mut cnf, terms.iter().map(|(_, x)| x));
					// A normalised term counts from zero, and its least value
					// moves into the bound.
					let least: Coeff = terms.iter().map(|(_, x)| x.min()).sum();
					if k < least {
						continue;
					}
					let counted = terms.iter().map(|(c, x)| (*c, x.clone() - x.min()));
					let con = NormalizedIntLinear::new(counted, cmp, PosCoeff::new(k - least));
					let mut enc = get_sorted_encoder(strategy.clone());
					let _ = enc.with_consistency(consistency);
					if enc.encode(&mut cnf, &con).is_err() {
						continue;
					}

					let mut seen = models_over(&cnf, &lits, |value| {
						terms.iter().map(|(_, x)| x.value(value)).collect_vec()
					});
					seen.sort_unstable();
					let ranges = doms
						.iter()
						.map(|d| RangeList::from_sorted_elements(d.to_vec()))
						.collect_vec();
					let allowed = brute_force(&[1; 3], &ranges, cmp.into(), k);
					assert_eq!(
						seen, allowed,
						"{strategy:?} consistency {consistency} {cmp:?} {k} over {doms:?}"
					);
				}
			}
		}
	}

	#[test]
	fn merged_2_eq() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=1).with_label("x");
		x.require_order_encoding(&mut cnf).unwrap();
		let y = IntVar::new(0..=1).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let z = IntVar::new(0..=2).with_label("z");
		z.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();
		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.merge(&mut cnf, &x, &y, &LimitComp::Equal, &z)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_2_merged_eq.sol"]);
	}

	/// The order literals of `vars`, to read models on: one for each way the
	/// network's own literals fall would be too many.
	fn order_literals<'a>(cnf: &mut Cnf, vars: impl IntoIterator<Item = &'a IntVar>) -> Vec<Lit> {
		vars.into_iter()
			.flat_map(|x| {
				let values = x.domain().iter().flatten().skip(1).collect_vec();
				values
					.into_iter()
					.filter_map(|v| match x.at_least(cnf, v).unwrap() {
						BoolVal::Lit(l) => Some(l),
						BoolVal::Const(_) => None,
					})
					.collect_vec()
			})
			.collect()
	}

	#[test]
	fn sorted_1_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let y = IntVar::new(0..=1).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(&mut cnf, &Count::new(vec![a], LimitComp::Equal, y.clone()))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_1_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_2_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let y = IntVar::new(0..=2).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Count::new(vec![a, b], LimitComp::Equal, y.clone()),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_2_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_3_2_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let c = cnf.new_lit();
		let y = IntVar::new(0..=2).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Count::new(vec![a, b, c], LimitComp::Equal, y.clone()),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_3_2_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_3_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let c = cnf.new_lit();
		let y = IntVar::new(0..=3).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Count::new(vec![a, b, c], LimitComp::Equal, y.clone()),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_3_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_4_2_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(4).iter_lits().collect_vec();
		let y = IntVar::new(0..=2).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Count::new(lits.clone(), LimitComp::Equal, y.clone()),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_4_2_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_4_3_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(4).iter_lits().collect_vec();
		let y = IntVar::new(0..=3).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Count::new(lits.clone(), LimitComp::Equal, y.clone()),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_4_3_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_4_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(4).iter_lits().collect_vec();
		let y = IntVar::new(0..=4).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Count::new(lits.clone(), LimitComp::Equal, y.clone()),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_4_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_5_1_eq_negated() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(5).iter_lits().map(|l| !l).collect_vec();
		let y = IntVar::new(0..=1).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Count::new(lits.clone(), LimitComp::Equal, y.clone()),
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["sorted/test_5_1_sorted_eq_negated.sol"],
		);
	}

	#[test]
	fn sorted_5_3_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(5).iter_lits().collect_vec();
		let y = IntVar::new(0..=3).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Count::new(lits.clone(), LimitComp::Equal, y.clone()),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_5_3_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_5_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(5).iter_lits().collect_vec();
		let y = IntVar::new(0..=5).with_label("y");
		// Materialise before the variable range is captured below.
		y.require_order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Count::new(lits.clone(), LimitComp::Equal, y.clone()),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_5_sorted_eq.sol"]);
	}

	#[test]
	fn weighted_integers_add_up_to_the_bound() {
		const K: Coeff = 9;
		for strategy in [
			SortingNetworkStrategy::Direct,
			SortingNetworkStrategy::Recursive,
			SortingNetworkStrategy::Mixed(10),
		] {
			for cmp in [LimitComp::LessEq, LimitComp::Equal] {
				let mut cnf = Cnf::default();
				// The terms are read from their own literals, since a model
				// for each way the network's literals can fall is too many.
				let mut lits = Vec::new();
				let terms = [(2, 3), (3, 2), (5, 1), (1, 4)].map(|(c, ub)| {
					let order = cnf.new_var_range(ub as usize).iter_lits().collect_vec();
					for (&below, &above) in order.iter().tuple_windows() {
						cnf.add_clause([!above, below]).unwrap();
					}
					lits.extend(&order);
					let x = IntVar::from_order_encoding(0..=ub, &order);
					(PosCoeff::new(c), x)
				});
				get_sorted_encoder(strategy.clone())
					.encode(
						&mut cnf,
						&NormalizedIntLinear::new(terms.clone(), cmp, PosCoeff::new(K)),
					)
					.unwrap();

				let mut seen = models_over(&cnf, &lits, |value| {
					terms.iter().map(|(_, x)| x.value(value)).collect_vec()
				});
				seen.sort_unstable();

				let allowed = terms
					.iter()
					.map(|(_, x)| x.min()..=x.max())
					.multi_cartesian_product()
					.filter(|values| {
						let sum: Coeff = values.iter().zip(&terms).map(|(v, (c, _))| v * **c).sum();
						match cmp {
							LimitComp::LessEq => sum <= K,
							LimitComp::Equal => sum == K,
						}
					})
					.sorted()
					.collect_vec();
				assert_eq!(seen, allowed, "{strategy:?} {cmp:?}");
			}
		}
	}

	linear_test_suite!(sorting_network_linear, SortingNetworkEncoder::default());
	linear_test_suite!(
		sorting_network_linear_direct,
		SortingNetworkEncoder::default().with_strategy(SortingNetworkStrategy::Direct)
	);
	linear_test_suite!(
		sorting_network_linear_recursive,
		SortingNetworkEncoder::default().with_strategy(SortingNetworkStrategy::Recursive)
	);
	linear_test_suite!(
		sorting_network_linear_consistency,
		SortingNetworkEncoder::default().with_consistency(true)
	);

	mod eq_consistency {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let _ = e.with_consistency(true);
				e
			},
			LimitComp::Equal
		);
	}

	mod eq_direct {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let _ = e.with_strategy(SortingNetworkStrategy::Direct);
				e
			},
			LimitComp::Equal
		);
	}

	mod eq_recursive {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let _ = e.with_strategy(SortingNetworkStrategy::Recursive);
				e
			},
			LimitComp::Equal
		);
	}

	mod le_consistency {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let _ = e.with_consistency(true);
				e
			},
			LimitComp::LessEq
		);
	}

	mod le_direct {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let _ = e.with_strategy(SortingNetworkStrategy::Direct);
				e
			},
			LimitComp::LessEq
		);
	}

	mod le_mixed {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let _ = e.with_strategy(SortingNetworkStrategy::Mixed(2));
				e
			},
			LimitComp::LessEq
		);
	}

	mod le_recursive {
		sorted_card_test_suite!(
			{
				let mut e = SortingNetworkEncoder::default();
				let _ = e.with_strategy(SortingNetworkStrategy::Recursive);
				e
			},
			LimitComp::LessEq
		);
	}
}
