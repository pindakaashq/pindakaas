use std::{cmp::min, hash, iter::once, mem, sync::Mutex};

use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
	bool_linear::{BoolLinExp, LimitComp},
	integer::{IntVarEnc, IntVarOrd, TernLeConstraint, TernLeEncoder},
	propositional_logic::{Formula, TseitinEncoder},
	AsDynClauseDatabase, Checker, ClauseDatabase, Coeff, Encoder, Lit, Result, Unsatisfiable,
	Valuation,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SortN {
	#[allow(dead_code, reason = "TODO: Ask HB to see whether this is still useful")]
	One,
	DivTwo,
}

#[derive(Debug, Clone)]
pub struct Sorted<'a> {
	pub(crate) xs: &'a [Lit],
	pub(crate) cmp: LimitComp,
	pub(crate) y: &'a IntVarEnc,
}

type SortedCache = FxHashMap<(u128, u128, u128), (SortedStrategy, (u128, u128))>;

#[derive(Debug)]
/// Encoder for [`Sorted`] employing a Merge Sort strategy.
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
	sort_n: SortN,
	strategy_cost_cache: Mutex<SortedCache>,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum SortedStrategy {
	Direct,
	Recursive,
	Mixed(u32),
}

impl<'a> Sorted<'a> {
	pub(crate) fn new(xs: &'a [Lit], cmp: LimitComp, y: &'a IntVarEnc) -> Self {
		Self { xs, cmp, y }
	}
}

impl Checker for Sorted<'_> {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<()> {
		let lhs = BoolLinExp::from_terms(self.xs.iter().map(|x| (*x, 1)).collect_vec().as_slice())
			.value(sol)?;
		let rhs = BoolLinExp::from(self.y).value(sol)?;

		if match self.cmp {
			LimitComp::LessEq => lhs <= rhs,
			LimitComp::Equal => lhs == rhs,
		} {
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}
}

impl SortedEncoder {
	fn comp<Db>(
		&self,
		db: &mut Db,
		x: &IntVarEnc,
		y: &IntVarEnc,
		cmp: &LimitComp,
		z: &IntVarEnc,
		c: Coeff,
	) -> Result
	where
		Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	{
		let cmp = self.overwrite_recursive_cmp.as_ref().unwrap_or(cmp);
		let c1 = c;
		let c2 = c + 1;
		let x = x.geq(c1); // c
		let y = y.geq(c2); // c+1
		let z1 = z.geq(c1 + c1); // 2c
		let z2 = z.geq(c1 + c2); // 2c+1

		TseitinEncoder.encode(db, &Formula::Or(vec![!x.clone(), z1.clone()]))?;
		TseitinEncoder.encode(db, &Formula::Or(vec![!y.clone(), z1.clone()]))?;
		TseitinEncoder.encode(db, &Formula::Or(vec![!x.clone(), !y.clone(), z2.clone()]))?;
		if cmp == &LimitComp::Equal {
			TseitinEncoder.encode(db, &Formula::Or(vec![x.clone(), !z2.clone()]))?;
			TseitinEncoder.encode(db, &Formula::Or(vec![y.clone(), !z2]))?;
			TseitinEncoder.encode(db, &Formula::Or(vec![x, y, !z1]))?;
		}
		Ok(())
	}

	/// Set whether to add consistency constraints to the intermediate integer
	/// variables.
	pub fn enable_intermediate_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}

	fn merged<Db>(
		&self,
		db: &mut Db,
		x1: &IntVarEnc,
		x2: &IntVarEnc,
		cmp: &LimitComp,
		y: &IntVarEnc,
		_lvl: usize,
	) -> Result
	where
		Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	{
		let (a, b, c) = (x1.ub(), x2.ub(), y.ub());
		let strat = if let SortedStrategy::Mixed(lambda) = &self.strategy {
			let mut cache = self.strategy_cost_cache.lock().unwrap();
			SortedStrategy::mixed_cost(&mut cache, a as u128, b as u128, c as u128, *lambda).0
		} else {
			self.strategy.clone()
		};

		match strat {
			SortedStrategy::Direct => {
				let cmp = self.overwrite_direct_cmp.as_ref().unwrap_or(cmp).clone();
				TernLeEncoder::default().encode(
					db,
					&TernLeConstraint {
						x: x1,
						y: x2,
						cmp,
						z: y, // TODO no consistency implemented for this bound yet
					},
				)
			}
			SortedStrategy::Recursive => {
				if a == 0 && b == 0 {
					Ok(())
				} else if a == 1 && b == 1 && c <= 2 {
					self.smerge(db, x1, x2, cmp, y)
				} else {
					let x1_floor = x1.div(2);
					let x1_ceil = x1
						.add(
							db,
							&TernLeEncoder::default(),
							&IntVarEnc::Const(1),
							None,
							None,
						)?
						.div(2);

					let x2_floor = x2.div(2);
					let x2_ceil = x2
						.add(
							db,
							&TernLeEncoder::default(),
							&IntVarEnc::Const(1),
							None,
							None,
						)?
						.div(2);

					let z_floor =
						x1_floor.add(db, &TernLeEncoder::default(), &x2_floor, None, None)?;
					self.encode(
						db,
						&TernLeConstraint::new(&x1_floor, &x2_floor, cmp.clone(), &z_floor),
					)?;

					let z_ceil =
						x1_ceil.add(db, &TernLeEncoder::default(), &x2_ceil, None, None)?;
					self.encode(
						db,
						&TernLeConstraint::new(&x1_ceil, &x2_ceil, cmp.clone(), &z_ceil),
					)?;

					for c in 0..=c {
						self.comp(db, &z_floor, &z_ceil, cmp, y, c)?;
					}

					Ok(())
				}
			}
			_ => unreachable!(),
		}
	}

	fn next_int_var<Db>(&self, db: &mut Db, ub: Coeff, lbl: String) -> IntVarEnc
	where
		Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	{
		// TODO We always have the view x>=1 <-> y>=1, which is now realized using equiv
		if ub == 0 {
			IntVarEnc::Const(0)
		} else {
			let y = IntVarOrd::from_bounds(db, 0, ub, lbl);
			if self.add_consistency {
				y.consistent(db).unwrap();
			}
			y.into()
		}
	}

	/// The sorted/merged base case of x1{0,1}+x2{0,1}<=y{0,1,2}
	fn smerge<Db>(
		&self,
		db: &mut Db,
		x1: &IntVarEnc,
		x2: &IntVarEnc,
		cmp: &LimitComp,
		y: &IntVarEnc,
	) -> Result
	where
		Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	{
		// we let x2 take the place of z_ceil, so we need to add 1 to both sides
		let x2 = x2.add(
			db,
			&TernLeEncoder::default(),
			&IntVarEnc::Const(1),
			None,
			None,
		)?;
		let y = y.add(
			db,
			&TernLeEncoder::default(),
			&IntVarEnc::Const(1),
			None,
			None,
		)?;
		self.comp(db, x1, &x2, cmp, &y, 1)
	}

	fn sort<Db>(
		&self,
		db: &mut Db,
		xs: &[IntVarEnc],
		cmp: &LimitComp,
		ub: Coeff,
		lbl: String,
		_lvl: usize,
	) -> Option<IntVarEnc>
	where
		Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	{
		match xs {
			[] => None,
			[x] => Some(x.clone()),
			xs => {
				let y = self.next_int_var(db, ub, lbl);
				self.sorted(db, xs, cmp, &y, _lvl).unwrap();
				Some(y)
			}
		}
	}

	fn sorted<Db>(
		&self,
		db: &mut Db,
		xs: &[IntVarEnc],
		cmp: &LimitComp,
		y: &IntVarEnc,
		_lvl: usize,
	) -> Result
	where
		Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	{
		let (n, m) = (xs.len(), y.ub());
		let direct = false;

		// TODO: Add tracing
		// eprintln!(
		// 	"{:_lvl$}sorted([{}] {} {}, {})",
		// 	"",
		// 	xs.iter().join(", "),
		// 	cmp,
		// 	y,
		// 	direct,
		// 	_lvl = _lvl
		// );

		debug_assert!(xs.iter().all(|x| x.ub() == 1));
		if direct {
			return (1..=m + 1).try_for_each(|k| {
				xs.iter()
					.map(|x| x.geq(1))
					.combinations(k as usize)
					.try_for_each(|lits| {
						let lits = lits
							.into_iter()
							.map(|lit| !lit)
							.chain(once(y.geq(k)))
							.collect();
						TseitinEncoder.encode(db, &Formula::Or(lits))
					})
			});
		}
		match xs {
			[] => Ok(()),
			[x] => TernLeEncoder::default().encode(
				db,
				&TernLeConstraint {
					x,
					y: &IntVarEnc::Const(0),
					cmp: cmp.clone(),
					z: y,
				},
			),
			[x1, x2] if m <= 2 => self.smerge(db, x1, x2, cmp, y),
			xs => {
				let n = match self.sort_n {
					SortN::One => 1,
					SortN::DivTwo => n / 2,
				};
				let y1 = self.sort(
					db,
					&xs[..n],
					cmp,
					min((0..n).fold(0, |a, _| a + 1), y.ub()),
					String::from("y1"),
					_lvl,
				);
				let y2 = self.sort(
					db,
					&xs[n..],
					cmp,
					min((n..xs.len()).fold(0, |a, _| a + 1), y.ub()),
					String::from("y2"),
					_lvl,
				);

				if let Some(y1) = y1 {
					if let Some(y2) = y2 {
						self.merged(db, &y1, &y2, cmp, y, _lvl + 1)
					} else {
						Ok(())
					}
				} else {
					Ok(())
				}
			}
		}
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
			sort_n: self.sort_n.clone(),
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
			sort_n: SortN::DivTwo,
			strategy_cost_cache: Mutex::default(),
		}
	}
}

impl<Db: ClauseDatabase + AsDynClauseDatabase + ?Sized> Encoder<Db, Sorted<'_>> for SortedEncoder {
	fn encode(&self, db: &mut Db, sorted: &Sorted) -> Result {
		let xs = sorted
			.xs
			.iter()
			.map(|x| Some(*x))
			.enumerate()
			.map(|(i, x)| {
				IntVarOrd::from_views(db, (0..=1).into(), vec![x], format!("x_{}", i + 1)).into()
			})
			.collect_vec();

		if self.add_consistency {
			sorted.y.consistent(db).unwrap();
		}

		self.sorted(db, &xs, &sorted.cmp, sorted.y, 0)
	}
}

impl<Db> Encoder<Db, TernLeConstraint<'_>> for SortedEncoder
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
{
	fn encode(&self, db: &mut Db, tern: &TernLeConstraint) -> Result {
		let TernLeConstraint { x, y, cmp, z } = tern;
		if tern.is_fixed()? {
			Ok(())
		} else if matches!(x, IntVarEnc::Ord(_))
			&& matches!(y, IntVarEnc::Ord(_))
			&& matches!(z, IntVarEnc::Ord(_))
		{
			self.merged(db, x, y, cmp, z, 0)
		} else {
			TernLeEncoder::default().encode(db, tern)
		}
	}
}

impl Eq for SortedEncoder {}

impl PartialEq for SortedEncoder {
	fn eq(&self, other: &Self) -> bool {
		// Deconstruct the two structs to ensure no additional fields are ignored if
		// they are ever added
		let &Self {
			add_consistency: a1,
			strategy: b1,
			overwrite_direct_cmp: c1,
			overwrite_recursive_cmp: d1,
			sort_n: e1,
			strategy_cost_cache: _, // Ignore the cache for equality comparison
		} = &self;
		let &Self {
			add_consistency: a2,
			strategy: b2,
			overwrite_direct_cmp: c2,
			overwrite_recursive_cmp: d2,
			sort_n: e2,
			strategy_cost_cache: _,
		} = &other;
		a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2 && e1 == e2
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
			sort_n,
			strategy_cost_cache: _, // Ignore the cache for hashing
		} = &self;
		add_consistency.hash(state);
		strategy.hash(state);
		overwrite_direct_cmp.hash(state);
		overwrite_recursive_cmp.hash(state);
		sort_n.hash(state);
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
		bool_linear::LimitComp,
		helpers::tests::{assert_solutions, expect_file},
		integer::{IntVarEnc, IntVarOrd, TernLeConstraint},
		sorted::{Sorted, SortedEncoder, SortedStrategy},
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
		let x: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 1, String::from("x")).into();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 1, String::from("y")).into();
		let z: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 2, String::from("z")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();
		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(
				&mut cnf,
				&TernLeConstraint::new(&x, &y, LimitComp::Equal, &z),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_2_merged_eq.sol"]);
	}

	#[test]
	fn sorted_2_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 2, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&[a, b], LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_2_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_3_2_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let c = cnf.new_lit();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 2, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&[a, b, c], LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_3_2_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_3_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let c = cnf.new_lit();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 3, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&[a, b, c], LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_3_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_4_2_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(4).iter_lits().collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 2, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_4_2_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_4_3_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(4).iter_lits().collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 3, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_4_3_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_4_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(4).iter_lits().collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 4, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_4_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_5_1_eq_negated() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(5).iter_lits().map(|l| !l).collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 1, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
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
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 3, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_5_3_sorted_eq.sol"]);
	}

	#[test]
	fn sorted_5_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(5).iter_lits().collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 5, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_5_sorted_eq.sol"]);
	}
}
