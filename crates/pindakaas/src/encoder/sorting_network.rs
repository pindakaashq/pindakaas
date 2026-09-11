//! Counting literals through a network of comparators.
//!
//! Each merge is either stated outright or halved and recursed on — see
//! [`SortingNetworkStrategy`] — and the leaves become ternary integer
//! constraints. Each sub-sorter is built only as wide as the bound above it can
//! use, which is what makes this the cardinality network of Asín et al. [^1]
//! rather than a full sorter; the merges between them are not truncated.
//!
//! Domain consistent [^1].
//!
//! [^1]: R. Asín, R. Nieuwenhuis, A. Oliveras, E. Rodríguez-Carbonell,
//! "Cardinality Networks: a theoretical and empirical study", Constraints
//! 16(2) (2011) 195–221.

use std::{cmp::min, hash, mem, sync::Mutex};

use rustc_hash::FxHashMap;

use crate::{
	constraint::{
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		count::Count,
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

/// The variable `⌊x / 2⌋`, which reaches `w` exactly when `x` reaches `2·w`.
///
/// Its literals are `x`'s, every other one, so halving costs nothing.
fn halved<Db: ClauseDatabase + ?Sized>(db: &mut Db, x: &IntVar) -> Result<IntVar, Unsatisfiable> {
	let max = x.max() / 2;
	let walk = (0..=max)
		.map(|w| Ok((w, x.lit_at_least(db, 2 * w)?)))
		.collect::<Result<Vec<_>, Unsatisfiable>>()?;
	Ok(IntVar::from_order_walk(db, walk)?.with_label(format!("{}/2", x.label())))
}

/// The variable `x + k`, which reaches `v` exactly when `x` reaches `v - k`.
///
/// Its literals are `x`'s, the domain having only moved along.
fn shifted<Db: ClauseDatabase + ?Sized>(
	db: &mut Db,
	x: &IntVar,
	k: Coeff,
) -> Result<IntVar, Unsatisfiable> {
	let walk = x
		.domain()
		.iter()
		.flatten()
		.map(|v| Ok((v + k, x.lit_at_least(db, v)?)))
		.collect::<Result<Vec<_>, Unsatisfiable>>()?;
	Ok(IntVar::from_order_walk(db, walk)?.with_label(format!("{}+{k}", x.label())))
}

impl SortingNetworkEncoder {
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
		let (x, y) = (x.lit_at_least(db, c)?, y.lit_at_least(db, c + 1)?);
		let (z1, z2) = (z.lit_at_least(db, c + c)?, z.lit_at_least(db, c + c + 1)?);

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

	/// Configures whether intermediate variables are constrained independently
	/// of the merge.
	pub fn enable_intermediate_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}

	/// Constrain `z` to be what `x` and `y` come to together.
	///
	/// A variable with a single value has nothing to merge, and merging it
	/// anyway would not converge, since halving leaves it unchanged. So
	/// once any of the three is fixed, the constraint is stated outright. The
	/// two inputs are checked alike even though the corpus only exercises the
	/// first: the alternative to a redundant check here is a hang.
	fn merge<Db>(
		&self,
		db: &mut Db,
		x: &IntVar,
		y: &IntVar,
		cmp: &LimitComp,
		z: &IntVar,
		lvl: usize,
	) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		if x.card() == 1 || y.card() == 1 || z.card() == 1 {
			self.ternary(db, x, y, cmp, z)
		} else {
			self.merged(db, x, y, cmp, z, lvl)
		}
	}

	/// Merge `x` and `y` into `z` a bit at a time, or state the addition
	/// outright where that is cheaper.
	fn merged<Db>(
		&self,
		db: &mut Db,
		x: &IntVar,
		y: &IntVar,
		cmp: &LimitComp,
		z: &IntVar,
		lvl: usize,
	) -> Result
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
					let (x_floor, y_floor) = (halved(db, x)?, halved(db, y)?);
					let (x_up, y_up) = (shifted(db, x, 1)?, shifted(db, y, 1)?);
					let (x_ceil, y_ceil) = (halved(db, &x_up)?, halved(db, &y_up)?);

					let z_floor = self.sum_var(db, &x_floor, &y_floor, c)?;
					self.merge(db, &x_floor, &y_floor, cmp, &z_floor, lvl + 1)?;

					let z_ceil = self.sum_var(db, &x_ceil, &y_ceil, c)?;
					self.merge(db, &x_ceil, &y_ceil, cmp, &z_ceil, lvl + 1)?;

					(0..=c).try_for_each(|c| self.comp(db, &z_floor, &z_ceil, cmp, z, c))
				}
			}
			SortingNetworkStrategy::Mixed(_) => {
				unreachable!("a strategy is settled before it is used")
			}
		}
	}

	/// A variable over `0..=max`, or the constant zero where there is nothing
	/// to count.
	fn next_int_var(&self, max: Coeff, label: String) -> IntVar {
		IntVar::new(0..=max)
			.enforce_consistency(self.add_consistency)
			.with_label(label)
	}

	/// The base case, `x{0,1} + y{0,1} ≷ z{0,1,2}`.
	fn smerge<Db>(&self, db: &mut Db, x: &IntVar, y: &IntVar, cmp: &LimitComp, z: &IntVar) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		// `y` stands in for the half that rounds up, so both sides move along
		// by one to meet it.
		let (y, z) = (shifted(db, y, 1)?, shifted(db, z, 1)?);
		self.comp(db, x, &y, cmp, &z, 1)
	}

	/// Sort `xs` into a variable counting how many of them hold, up to `max`.
	fn sort<Db>(
		&self,
		db: &mut Db,
		xs: &[IntVar],
		cmp: &LimitComp,
		max: Coeff,
		label: String,
		lvl: usize,
	) -> Result<Option<IntVar>, Unsatisfiable>
	where
		Db: ClauseDatabase + ?Sized,
	{
		Ok(match xs {
			[] => None,
			[x] => Some(x.clone()),
			xs => {
				let y = self.next_int_var(max, label);
				self.sorted(db, xs, cmp, &y, lvl)?;
				Some(y)
			}
		})
	}

	/// Constrain `y` to count how many of `xs` hold.
	fn sorted<Db>(
		&self,
		db: &mut Db,
		xs: &[IntVar],
		cmp: &LimitComp,
		y: &IntVar,
		lvl: usize,
	) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		debug_assert!(xs.iter().all(|x| x.max() == 1));
		match xs {
			[] => Ok(()),
			[x] => {
				let zero = IntVar::new(0..=0).with_label("0");
				self.ternary(db, x, &zero, cmp, y)
			}
			[x1, x2] if y.max() <= 2 => self.smerge(db, x1, x2, cmp, y),
			xs => {
				let n = xs.len() / 2;
				let y1 = self.sort(
					db,
					&xs[..n],
					cmp,
					min(n as Coeff, y.max()),
					String::from("y1"),
					lvl,
				)?;
				let y2 = self.sort(
					db,
					&xs[n..],
					cmp,
					min((xs.len() - n) as Coeff, y.max()),
					String::from("y2"),
					lvl,
				)?;
				match (y1, y2) {
					(Some(y1), Some(y2)) => self.merged(db, &y1, &y2, cmp, y, lvl + 1),
					_ => Ok(()),
				}
			}
		}
	}

	/// A variable over what `x` and `y` can come to together, up to `ub`.
	///
	/// The halves a merge is split into are capped at the bound above them,
	/// but halving rounds up on one side, so what the two ceilings come to can
	/// be one past the bound — whenever both inputs and the bound are the same
	/// odd number. Nothing below reads that value, so dropping it costs
	/// nothing and saves a few percent of the merge.
	fn sum_var<Db>(
		&self,
		_db: &mut Db,
		x: &IntVar,
		y: &IntVar,
		ub: Coeff,
	) -> Result<IntVar, Unsatisfiable>
	where
		Db: ClauseDatabase + ?Sized,
	{
		Ok(
			IntVar::new((x.min() + y.min())..=min(x.max() + y.max(), ub))
				.enforce_consistency(self.add_consistency)
				.with_label(format!("{}+{}", x.label(), y.label())),
		)
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
				cmp.clone().into(),
				(1, z.clone()),
			),
		)
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
		self.encode(db, &Count::new(card.lits.clone(), card.cmp.clone(), y))
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
				IntVar::from_order_encoding(db, 0..=1, &[x])
					.map(|v| v.with_label(format!("x_{}", i + 1)))
			})
			.collect::<Result<Vec<_>, _>>()?;

		self.sorted(db, &xs, &count.cmp, &count.y, 0)
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
		if cache.contains_key(&key) {
			return cache[&key].clone();
		}

		// TODO safely use floating point for lambda
		let lambda_fn = |(v, c): (u128, u128), lambda: u32| -> u128 { (v * lambda as u128) + c };

		let dir_cost = Self::direct_cost(a, b, c);
		let rec_cost = Self::recursive_cost(cache, a, b, c, lambda);
		let ret = if lambda_fn(dir_cost, lambda) < lambda_fn(rec_cost, lambda) {
			(SortingNetworkStrategy::Direct, dir_cost)
		} else {
			(SortingNetworkStrategy::Recursive, rec_cost)
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
		let div_ceil = |a: u128, b: u128| (a - 1 + b) / b;

		match (a, b, c) {
			(0, 0, _) => (0, 0),
			(1, 0, _) => unreachable!(),
			(0, 1, _) => (0, 0),
			(1, 1, 1) => (1, 2),
			(1, 1, 2) => (2, 3),
			(a, b, c) => {
				let ((_, (v1, c1)), (_, (v2, c2)), (v3, c3)) = (
					Self::mixed_cost(cache, div_ceil(a, 2), div_ceil(b, 2), c / 2 + 1, lambda),
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

	use itertools::Itertools;
	use traced_test::test;

	use crate::{
		constraint::{
			cardinality::Cardinality,
			count::{Count, SortingNetworkEncoder, SortingNetworkStrategy},
			linear::{LimitComp, PosCoeff},
		},
		decision::integer::IntVar,
		helpers::tests::{assert_solutions, expect_file},
		solver::{cadical::Cadical, SolveResult, Solver},
		ClauseDatabase, ClauseDatabaseTools, Cnf, Coeff, Encoder, Valuation, Var, VarRange,
	};

	/// The smallest case where a merge intermediate reaches one past the
	/// bound, and so the only one that tells the cap in [`sum_var`] from its
	/// absence: both halves and the bound have to be the same odd number,
	/// which needs seven literals at a bound of three.
	///
	/// The cap can only lose assignments, never admit extra ones, so the
	/// assertion is that every assignment the constraint allows is still a
	/// model — checking the models satisfy the constraint would not see it.
	#[test]
	fn a_merge_intermediate_is_capped_without_losing_assignments() {
		const N: usize = 7;
		const K: Coeff = 3;
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(N).iter_lits().collect_vec();
		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.encode(
				&mut cnf,
				&Cardinality {
					lits: lits.clone(),
					cmp: LimitComp::LessEq,
					k: PosCoeff::new(K),
				},
			)
			.unwrap();

		let vars = cnf.get_variables();
		let mut slv = Cadical::from(&cnf);
		let mut seen = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			seen.push(lits.iter().map(|&l| value.value(l)).collect_vec());
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
		seen.sort_unstable();
		seen.dedup();

		let allowed = (0..(1 << N))
			.map(|m: u32| (0..N).map(|i| m >> i & 1 == 1).collect_vec())
			.filter(|a| a.iter().filter(|holds| **holds).count() as Coeff <= K)
			.sorted()
			.collect_vec();
		assert_eq!(seen, allowed);
	}

	fn get_sorted_encoder(strategy: SortingNetworkStrategy) -> SortingNetworkEncoder {
		SortingNetworkEncoder {
			strategy,
			..SortingNetworkEncoder::default()
		}
	}

	#[test]
	fn merged_2_eq() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=1).with_label("x");
		let _ = x.order_encoding(&mut cnf).unwrap();
		let y = IntVar::new(0..=1).with_label("y");
		// Materialise before the variable range is captured below.
		let _ = y.order_encoding(&mut cnf).unwrap();
		let z = IntVar::new(0..=2).with_label("z");
		let _ = z.order_encoding(&mut cnf).unwrap();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();
		get_sorted_encoder(SortingNetworkStrategy::Recursive)
			.merge(&mut cnf, &x, &y, &LimitComp::Equal, &z, 0)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_2_merged_eq.sol"]);
	}

	#[test]
	fn sorted_1_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let y = IntVar::new(0..=1).with_label("y");
		// Materialise before the variable range is captured below.
		let _ = y.order_encoding(&mut cnf).unwrap();
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
		let _ = y.order_encoding(&mut cnf).unwrap();
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
		let _ = y.order_encoding(&mut cnf).unwrap();
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
		let _ = y.order_encoding(&mut cnf).unwrap();
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
		let _ = y.order_encoding(&mut cnf).unwrap();
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
		let _ = y.order_encoding(&mut cnf).unwrap();
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
		let _ = y.order_encoding(&mut cnf).unwrap();
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
		let _ = y.order_encoding(&mut cnf).unwrap();
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
		let _ = y.order_encoding(&mut cnf).unwrap();
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
		let _ = y.order_encoding(&mut cnf).unwrap();
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
