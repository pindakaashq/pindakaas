//! The odd-even merge network that encodes a [`Count`] constraint.
//!
//! Each merge is either stated outright or halved and recursed on — see
//! [`SortedStrategy`] — and the leaves become ternary integer constraints.

use std::{cmp::min, hash, mem, sync::Mutex};

use rustc_hash::FxHashMap;

use crate::{
	constraint::{
		linear::LimitComp,
		int_ternary::{IntTernary, IntTernaryEncoder},
		count::Count,
	},
	decision::integer::IntVar,
	ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Result, Unsatisfiable,
};

type SortedCache = FxHashMap<(u128, u128, u128), (SortedStrategy, (u128, u128))>;

#[derive(Debug)]
/// Encoder for a [`Count`] constraint, as an odd-even merge network.
///
/// # Warning
/// The encoder structure contains a cache for computing node costs that is
/// used when using a mixed strategy. This cache is not considered when
/// comparing two encoders for equality, when hashing, or when cloning. This
/// could, for example, mean that a cloned encoder might lead to a degradation
/// in performance.
pub struct SortedEncoder {
	add_consistency: bool,
	strategy: SortedStrategy,
	overwrite_direct_cmp: Option<LimitComp>,
	overwrite_recursive_cmp: Option<LimitComp>,
	strategy_cost_cache: Mutex<SortedCache>,
}

/// How [`SortedEncoder`] merges two sorted halves.
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum SortedStrategy {
	/// State the result of the merge outright, a clause per pair of values.
	Direct,
	/// Halve the inputs, merge each half, and comparator the results together.
	Recursive,
	/// Whichever of the two is cheaper for the merge at hand, by a cost model
	/// that counts clauses and literals and weighs literals by the given
	/// factor.
	Mixed(u32),
}

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

impl SortedEncoder {
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
		let cmp = self.overwrite_recursive_cmp.as_ref().unwrap_or(cmp);
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

	/// Set whether to add consistency constraints to the intermediate integer
	/// variables.
	pub fn enable_intermediate_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}

	/// Constrain `z` to be what `x` and `y` come to together.
	///
	/// A variable with a single value has nothing to merge, and merging it
	/// anyway would not converge, since halving it leaves it just as large. So
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
		let strat = if let SortedStrategy::Mixed(lambda) = &self.strategy {
			let mut cache = self.strategy_cost_cache.lock().unwrap();
			SortedStrategy::mixed_cost(&mut cache, a as u128, b as u128, c as u128, *lambda).0
		} else {
			self.strategy.clone()
		};

		match strat {
			SortedStrategy::Direct => {
				let cmp = self.overwrite_direct_cmp.as_ref().unwrap_or(cmp);
				self.ternary(db, x, y, cmp, z)
			}
			SortedStrategy::Recursive => {
				if a == 0 && b == 0 {
					Ok(())
				} else if a == 1 && b == 1 && c <= 2 {
					self.smerge(db, x, y, cmp, z)
				} else {
					// Split each side into the halves that round down and up,
					// merge those separately, and let the comparators put the
					// two results back together.
					let (x_floor, y_floor) = (halved(db, x)?, halved(db, y)?);
					let (x_up, y_up) = (shifted(db, x, 1)?, shifted(db, y, 1)?);
					let (x_ceil, y_ceil) = (halved(db, &x_up)?, halved(db, &y_up)?);

					let z_floor = self.sum_var(db, &x_floor, &y_floor)?;
					self.merge(db, &x_floor, &y_floor, cmp, &z_floor, lvl + 1)?;

					let z_ceil = self.sum_var(db, &x_ceil, &y_ceil)?;
					self.merge(db, &x_ceil, &y_ceil, cmp, &z_ceil, lvl + 1)?;

					(0..=c).try_for_each(|c| self.comp(db, &z_floor, &z_ceil, cmp, z, c))
				}
			}
			SortedStrategy::Mixed(_) => unreachable!("a strategy is settled before it is used"),
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

	/// A variable over what `x` and `y` can come to together.
	fn sum_var<Db>(&self, _db: &mut Db, x: &IntVar, y: &IntVar) -> Result<IntVar, Unsatisfiable>
	where
		Db: ClauseDatabase + ?Sized,
	{
		Ok(IntVar::new((x.min() + y.min())..=(x.max() + y.max()))
			.enforce_consistency(self.add_consistency)
			.with_label(format!("{}+{}", x.label(), y.label())))
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

	pub(crate) fn with_overwrite_direct_cmp(&mut self, cmp: Option<LimitComp>) -> &mut Self {
		self.overwrite_direct_cmp = cmp;
		self
	}

	pub(crate) fn with_overwrite_recursive_cmp(&mut self, cmp: Option<LimitComp>) -> &mut Self {
		self.overwrite_recursive_cmp = cmp;
		self
	}

	/// Set whether the encoder should use the direct or recursive strategy, or
	/// a mix of both.
	pub fn with_strategy(&mut self, strategy: SortedStrategy) -> &mut Self {
		self.strategy = strategy;
		self
	}
}

impl Clone for SortedEncoder {
	fn clone(&self) -> Self {
		Self {
			add_consistency: self.add_consistency,
			strategy: self.strategy.clone(),
			overwrite_direct_cmp: self.overwrite_direct_cmp.clone(),
			overwrite_recursive_cmp: self.overwrite_recursive_cmp.clone(),
			strategy_cost_cache: Mutex::default(),
		}
	}
}

impl Default for SortedEncoder {
	fn default() -> Self {
		Self {
			strategy: SortedStrategy::Mixed(10),
			add_consistency: false,
			overwrite_direct_cmp: Some(LimitComp::LessEq),
			overwrite_recursive_cmp: Some(LimitComp::Equal),
			strategy_cost_cache: Mutex::default(),
		}
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Count> for SortedEncoder {
	fn encode(&self, db: &mut Db, count: &Count) -> Result {
		// Each literal is an integer worth one when it holds.
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

impl Eq for SortedEncoder {}

impl PartialEq for SortedEncoder {
	fn eq(&self, other: &Self) -> bool {
		// Deconstruct the two structs to ensure no additional fields are
		// ignored if they are ever added
		let &Self {
			add_consistency: a1,
			strategy: b1,
			overwrite_direct_cmp: c1,
			overwrite_recursive_cmp: d1,
			strategy_cost_cache: _, // Ignore the cache for equality comparison
		} = &self;
		let &Self {
			add_consistency: a2,
			strategy: b2,
			overwrite_direct_cmp: c2,
			overwrite_recursive_cmp: d2,
			strategy_cost_cache: _,
		} = &other;
		a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2
	}
}

impl hash::Hash for SortedEncoder {
	fn hash<H: hash::Hasher>(&self, state: &mut H) {
		// Deconstruct the struct to ensure no additional fields are ignored if
		// they are ever added
		let &Self {
			add_consistency,
			strategy,
			overwrite_direct_cmp,
			overwrite_recursive_cmp,
			strategy_cost_cache: _, // Ignore the cache for hashing
		} = &self;
		add_consistency.hash(state);
		strategy.hash(state);
		overwrite_direct_cmp.hash(state);
		overwrite_recursive_cmp.hash(state);
	}
}

impl SortedStrategy {
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
		cache: &mut SortedCache,
		mut a: u128,
		mut b: u128,
		c: u128,
		lambda: u32,
	) -> (SortedStrategy, (u128, u128)) {
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
			(SortedStrategy::Direct, dir_cost)
		} else {
			(SortedStrategy::Recursive, rec_cost)
		};

		let _ = cache.insert(key, ret.clone());
		ret
	}

	/// Calculate the cost of the recursive strategy for the given upper bounds
	/// of the integer variables.
	fn recursive_cost(
		cache: &mut SortedCache,
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
	use std::num::NonZeroI32;

	use itertools::Itertools;
	use traced_test::test;

	use crate::{
		constraint::{
			linear::LimitComp,
			count::{Count, SortedEncoder, SortedStrategy},
		},
		decision::integer::IntVar,
		helpers::tests::{assert_solutions, expect_file},
		ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder, Var, VarRange,
	};

	fn get_sorted_encoder(strategy: SortedStrategy) -> SortedEncoder {
		SortedEncoder {
			strategy,
			overwrite_direct_cmp: None,
			overwrite_recursive_cmp: None,
			..SortedEncoder::default()
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
		get_sorted_encoder(SortedStrategy::Recursive)
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

		get_sorted_encoder(SortedStrategy::Recursive)
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

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Count::new(vec![a, b], LimitComp::Equal, y.clone()))
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

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Count::new(vec![a, b, c], LimitComp::Equal, y.clone()))
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

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Count::new(vec![a, b, c], LimitComp::Equal, y.clone()))
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

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Count::new(lits.clone(), LimitComp::Equal, y.clone()))
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

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Count::new(lits.clone(), LimitComp::Equal, y.clone()))
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

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Count::new(lits.clone(), LimitComp::Equal, y.clone()))
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

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Count::new(lits.clone(), LimitComp::Equal, y.clone()))
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

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Count::new(lits.clone(), LimitComp::Equal, y.clone()))
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

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Count::new(lits.clone(), LimitComp::Equal, y.clone()))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_5_sorted_eq.sol"]);
	}
}
