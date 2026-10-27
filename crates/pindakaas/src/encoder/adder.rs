//! Encoding a linear constraint as the circuit that adds its terms up.
//!
//! The literals are bucketed by which bit of their coefficient they set, and
//! each bucket compressed three at a time by full adders. Also holds the sum
//! and carry circuits themselves, which the integer encoders build on.
//!
//! The adder network of Warners [^1], as Eén and Sörensson give it [^2].
//! Smallest of the encodings here and the weakest: a carry says nothing until
//! its inputs are settled, so unit propagation cannot tell that a partial
//! assignment has already broken the bound.
//!
//! [^1]: J. P. Warners, "A linear-time transformation of linear inequalities
//! into conjunctive normal form", Information Processing Letters 68(2) (1998)
//! 63–69.
//!
//! [^2]: N. Eén, N. Sörensson, "Translating Pseudo-Boolean Constraints into
//! SAT", Journal on Satisfiability, Boolean Modeling and Computation 2 (2006)
//! 1–26.

use std::{
	cmp::{max, min},
	num::NonZero,
};

use itertools::Itertools;

use crate::{
	constraint::{
		bool_linear::NormalizedBoolLinear,
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		count::Count,
		int_linear::NormalizedIntLinear,
		linear::{LimitComp, PosCoeff},
		propositional_logic::{Formula, TseitinEncoder},
	},
	decision::integer::{lex_leq_const, BinaryEncoding, IntVar},
	helpers::{
		as_binary, bit, new_named_lit,
		scm::{ScmObjective, ScmOperation, ScmSolution},
		shifted,
	},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Lit, Result, Unsatisfiable,
};

/// Above this many literals, enumerating the assignments of the wrong parity
/// costs more clauses than a Tseitin transformation costs auxiliary variables.
const DIRECT_PARITY_LITS: usize = 4;

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// An adder network for a linear constraint.
///
/// # Examples
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{linear::{Comparator, Linear}, linear::AdderEncoder,
/// #                  linear::{LinAggregator, LinVariant}},
/// #     decision::integer::IntVar, Cnf, Encoder,
/// # };
/// # let mut f = Cnf::default();
/// # let (x, y) = (IntVar::new(0..=5), IntVar::new(0..=5));
/// let con = Linear::new(x * 2 + y * 3, Comparator::LessEq, 10);
/// let LinVariant::Linear(con) = LinAggregator::default().aggregate(&mut f, &con)? else {
///     panic!("a sum of integer terms is a linear constraint");
/// };
/// AdderEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
pub struct AdderEncoder {}

impl AdderEncoder {
	/// Encode the adder carry circuit, i.e. whether at least two of `xs` are
	/// true.
	///
	/// The carry is constrained to equal `out` when given, and otherwise
	/// created, or returned directly when the fixed bits already determine it.
	#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "carry_circuit", skip_all, fields(constraint = Self::trace_print_carry(xs, &out))))]
	pub(crate) fn carry_circuit<Db>(
		db: &mut Db,
		xs: &[BoolVal],
		out: Option<BoolVal>,
		_label: String,
	) -> Result<BoolVal>
	where
		Db: ClauseDatabase + ?Sized,
	{
		let (lits, trues) = Self::filter_fixed_sum(xs);
		// With fewer than two free literals the fixed bits settle the carry.
		let determined = match lits[..] {
			[] => Some(BoolVal::Const(trues >= 2)),
			[x] => Some(match trues {
				0 => BoolVal::Const(false),
				1 => x,
				_ => BoolVal::Const(true),
			}),
			_ => None,
		};
		if let Some(c) = determined {
			return match out {
				None => Ok(c),
				Some(out) => {
					db.add_clause([!c, out])?;
					db.add_clause([c, !out])?;
					Ok(out)
				}
			};
		}

		let carry = out.unwrap_or_else(|| BoolVal::Lit(new_named_lit!(db, _label)));
		match lits[..] {
			[x, y] if trues == 0 => {
				db.add_clause([!x, !y, carry])?;
				db.add_clause([x, !carry])?;
				db.add_clause([y, !carry])?;
			}
			[x, y] => {
				debug_assert_eq!(trues, 1);
				db.add_clause([x, y, !carry])?;
				db.add_clause([!x, carry])?;
				db.add_clause([!y, carry])?;
			}
			[x, y, z] => {
				debug_assert_eq!(trues, 0);
				db.add_clause([x, y, !carry])?;
				db.add_clause([x, z, !carry])?;
				db.add_clause([y, z, !carry])?;
				db.add_clause([!x, !y, carry])?;
				db.add_clause([!x, !z, carry])?;
				db.add_clause([!y, !z, carry])?;
			}
			_ => unreachable!("a full adder has at most three inputs"),
		}
		Ok(carry)
	}

	/// The bits of a difference `a − b`, which is known to be positive.
	///
	/// Subtraction is addition read the other way round: the bits are created
	/// and then constrained so that adding `b` back gives `a`.
	fn difference<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		a: &[BoolVal],
		b: &[BoolVal],
		factor: Coeff,
		width: &NonZero<u32>,
	) -> Result<Vec<BoolVal>, Unsatisfiable> {
		let span = factor * ((1 << width.get()) - 1);
		let bits: Vec<BoolVal> = (0..BinaryEncoding::required_bits(span))
			.map(|_| BoolVal::Lit(db.new_lit()))
			.collect();
		let _ = AdderEncoder::ripple_carry_adder(db, b, &bits, None, Some(a))?;
		Ok(bits)
	}

	/// Split `xs` into its literals and the number of its bits fixed to one.
	fn filter_fixed_sum(xs: &[BoolVal]) -> (Vec<BoolVal>, usize) {
		let mut trues = 0;
		let lits = xs
			.iter()
			.filter(|x| match x {
				BoolVal::Lit(_) => true,
				BoolVal::Const(b) => {
					trues += usize::from(*b);
					false
				}
			})
			.copied()
			.collect();
		(lits, trues)
	}

	/// The bits of `c·x` for a positive `c`, or `None` where carrying `c` in
	/// the columns costs less.
	fn product_bits<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		x: &IntVar,
		c: Coeff,
	) -> Result<Option<Vec<BoolVal>>, Unsatisfiable> {
		// Reading it in binary is free where that view exists, and costs a
		// channel where it does not.
		if !x.has_binary_encoding() && (x.has_order_encoding() || x.has_direct_encoding()) {
			return Ok(None);
		}
		if let Some(bits) = x.product(c) {
			return Ok(Some(bits));
		}
		let Ok(c32) = u32::try_from(c) else {
			return Ok(None);
		};
		let Some(width) = NonZero::new(BinaryEncoding::required_bits(x.max() - x.min()) as u32)
		else {
			return Ok(None);
		};
		// Heuristic: below four set bits the partial products barely overlap,
		// so the columns carry them for almost nothing.
		if c32.count_ones() < 4 {
			return Ok(None);
		}
		// Heuristic: one clause per column, against the adders SCM would need;
		// form the product only where it comes out ahead.
		let columns = (c32.count_ones() * width.get()).saturating_sub(c32.ilog2() + 1);
		let plan = ScmSolution::synthesize(c32, ScmObjective::MinAdders(width));
		if plan.cost >= columns {
			return Ok(None);
		}
		Ok(Some(Self::scaled_bits(db, x, c, plan)?))
	}

	/// Ripple-carry adder over the binary encodings `xs` and `ys`.
	///
	/// When `zs` is given the sum is *constrained* to equal it; otherwise the
	/// sum bits are created and returned, truncated to `bits` (defaulting to
	/// the width needed to hold any sum, so that no overflow is possible).
	#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "ripple_carry_adder", skip_all, fields(constraint = format!("{xs:?} + {ys:?} = {zs:?}"))))]
	pub(crate) fn ripple_carry_adder<Db>(
		db: &mut Db,
		xs: &[BoolVal],
		ys: &[BoolVal],
		bits: Option<usize>,
		zs: Option<&[BoolVal]>,
	) -> Result<Vec<BoolVal>>
	where
		Db: ClauseDatabase + ?Sized,
	{
		// A given sum may be wider than the inputs reach; its top bits still
		// have to be driven to zero.
		let max_bits = max(max(xs.len(), ys.len()) + 1, zs.map_or(0, <[_]>::len));
		let bits = bits.unwrap_or(max_bits);
		let mut c = BoolVal::Const(false);
		(0..max_bits)
			.map(|i| {
				let (x, y) = (bit(xs, i), bit(ys, i));
				let z = match zs {
					Some(zs) => Some(bit(zs, i)),
					// Past the requested width the bit has to be zero.
					None if i < bits => None,
					None => Some(BoolVal::Const(false)),
				};
				let z = Self::sum_circuit(db, &[x, y, c], z, format!("z_{i}"))?;
				c = Self::carry_circuit(db, &[x, y, c], None, format!("c_{}", i + 1))?;
				Ok(z)
			})
			.collect()
	}

	/// The bits of `c·(x − lb)`, built from shifts and adders.
	///
	/// A shift costs nothing, being leading zero bits on the vector, so what is
	/// left is to find the fewest additions that reach `c`. That is the
	/// single-constant multiplication problem, and [`ScmSolution::synthesize`]
	/// plans it.
	fn scaled_bits<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		x: &IntVar,
		c: Coeff,
		plan: ScmSolution,
	) -> Result<Vec<BoolVal>, Unsatisfiable> {
		debug_assert!(c > 0, "a product is decomposed only for a positive factor");
		let c32 = u32::try_from(c).expect("the plan was synthesised for this coefficient");
		let prev_product = |x: &IntVar, factor: u32| -> Vec<BoolVal> {
			x.product(Coeff::from(factor))
				.expect("the plan builds every product before it is used")
		};

		let (input, _, _) = x.binary_bits(db)?;
		let width = NonZero::new(input.len() as u32)
			.expect("a variable of one value is not scaled by a plan");

		// A step is named by the factor it reaches, which is what products are
		// kept under, so one shared with an earlier synthesis is picked up.
		for op in plan.operations {
			let factor = Coeff::from(op.result().get());
			if x.product(factor).is_some() {
				continue;
			}
			let bits = match op {
				ScmOperation::ShiftLeft { source, shift } => {
					shifted(&prev_product(x, source.get()), shift)
				}
				ScmOperation::ShiftAdd { left, right, shift } => {
					let left = shifted(&prev_product(x, left.get()), shift);
					AdderEncoder::ripple_carry_adder(
						db,
						&left,
						&prev_product(x, right.get()),
						None,
						None,
					)?
				}
				ScmOperation::ShiftSub { left, right, shift } => {
					let left = shifted(&prev_product(x, left.get()), shift);
					Self::difference(db, &left, &prev_product(x, right.get()), factor, &width)?
				}
				ScmOperation::SubShift { left, right, shift } => {
					let right = shifted(&prev_product(x, right.get()), shift);
					let left = prev_product(x, left.get());
					Self::difference(db, &left, &right, factor, &width)?
				}
			};
			x.set_product(factor, bits);
		}
		Ok(prev_product(x, c32))
	}

	/// Encode the adder sum circuit, i.e. `out ≡ xs[0] ⊕ .. ⊕ xs[n]`.
	///
	/// The sum is constrained to equal `out` when given, and otherwise created.
	#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "sum_circuit", skip_all, fields(constraint = Self::trace_print_sum(xs, &out))))]
	pub(crate) fn sum_circuit<Db>(
		db: &mut Db,
		xs: &[BoolVal],
		out: Option<BoolVal>,
		_label: String,
	) -> Result<BoolVal>
	where
		Db: ClauseDatabase + ?Sized,
	{
		let out = out.unwrap_or_else(|| BoolVal::Lit(new_named_lit!(db, _label)));
		// `out = ⊕xs` is exactly `⊕xs ⊕ out = 0`, and each bit fixed to one
		// flips the parity the remaining literals have to add up to.
		let (lits, trues) = Self::filter_fixed_sum(&[xs, &[out]].concat());
		let target = (trues % 2) as u32;
		if lits.is_empty() {
			return if target == 0 {
				Ok(out)
			} else {
				Err(Unsatisfiable)
			};
		}
		if lits.len() > DIRECT_PARITY_LITS {
			let xor = Formula::Xor(lits.into_iter().map(Formula::Atom).collect_vec());
			TseitinEncoder.encode(
				db,
				&if target == 1 {
					xor
				} else {
					Formula::Not(Box::new(xor))
				},
			)?;
			return Ok(out);
		}
		// Heuristic: `2ⁿ⁻¹` parity clauses and no auxiliary variables, which
		// beats Tseitin at the widths an adder uses.
		for assign in 0..(1_u32 << lits.len()) {
			if assign.count_ones() % 2 != target {
				db.add_clause(lits.iter().enumerate().map(|(i, &x)| {
					if assign & (1 << i) == 0 {
						x
					} else {
						!x
					}
				}))?;
			}
		}
		Ok(out)
	}

	#[cfg(any(feature = "tracing", test))]
	fn trace_print_carry(input: &[BoolVal], output: &Option<BoolVal>) -> String {
		let inner = itertools::join(input.iter().map(|l| format!("{l}")), " + ");
		match output {
			None => format!("_ ≡ ({inner} > 1)"),
			Some(BoolVal::Lit(r)) => {
				format!("{} ≡ ({} > 1)", crate::trace::trace_print_lit(r), inner)
			}
			Some(BoolVal::Const(true)) => format!("{inner} > 1"),
			Some(BoolVal::Const(false)) => format!("{inner} ≤ 1"),
		}
	}

	#[cfg(any(feature = "tracing", test))]
	fn trace_print_sum(input: &[BoolVal], output: &Option<BoolVal>) -> String {
		let inner = itertools::join(input.iter().map(|l| format!("{l}")), " ⊻ ");
		match output {
			None => format!("_ ≡ {inner}"),
			Some(BoolVal::Lit(r)) => format!("{} ≡ {}", crate::trace::trace_print_lit(r), inner),
			Some(BoolVal::Const(true)) => inner,
			Some(BoolVal::Const(false)) => format!("¬({inner})"),
		}
	}

	/// The constraint's terms as the literals standing for them and what each
	/// one adds, together with what the sum is worth before any of them holds.
	///
	/// A term over a variable held in binary with a dense coefficient becomes
	/// the bits of the product, which cost less to build than to carry; every
	/// other term becomes its variable's literals, scaled.
	fn weighted_literals<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		con: &NormalizedIntLinear,
	) -> Result<(Vec<(Lit, Coeff)>, Coeff), Unsatisfiable> {
		let mut weighted = Vec::new();
		let mut constant = 0;
		for (c, x) in con.terms() {
			let (c, x, offset) = x.base_term(*c);
			constant += offset;
			let (lits, worth, scale) = match Self::product_bits(db, &x, c.abs())? {
				Some(bits) => {
					let least = x.binary_least();
					let (lits, worth) =
						BinaryEncoding::from_bits(bits, c.abs() * least).as_weighted();
					(lits, worth, c.signum())
				}
				None => {
					let (lits, worth) = x.as_weighted(db)?;
					(lits, worth, c)
				}
			};
			constant += scale * worth;
			for (lit, weight) in lits {
				match scale * weight {
					0 => {}
					weight if weight > 0 => weighted.push((lit, weight)),
					weight => {
						weighted.push((!lit, -weight));
						constant += weight;
					}
				}
			}
		}
		Ok((weighted, constant))
	}
}

impl AdderEncoder {
	/// Carry the first of `inputs` that [`Self::carry_into`] can place into
	/// column `c`, reporting whether one was.
	fn carry_either<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		bucket: &mut [Vec<Lit>],
		c: usize,
		inputs: &[BoolVal],
	) -> Result<bool> {
		for &input in inputs {
			if let BoolVal::Lit(x) = input {
				if Self::carry_into(db, bucket, c, x)? {
					return Ok(true);
				}
			}
		}
		Ok(false)
	}

	/// Carry `x` into column `c`, reporting whether it could be placed.
	///
	/// A column holding `x` already doubles it into the next, and a carry past
	/// the top would put the sum past the bound, so `x` is then false.
	fn carry_into<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		bucket: &mut [Vec<Lit>],
		c: usize,
		x: Lit,
	) -> Result<bool> {
		let Some(rest) = Self::carry_to(bucket, c, x) else {
			return Ok(false);
		};
		let end = min(rest, bucket.len());
		for column in &mut bucket[c..end] {
			let at = column.iter().position(|&y| y == x).unwrap();
			let _ = column.remove(at);
		}
		if rest < bucket.len() {
			bucket[rest].push(x);
		} else {
			db.add_clause([!x])?;
		}
		Ok(true)
	}

	/// The column that a carry of `x` into column `c` comes to rest in, or
	/// `None` where it meets `¬x`, whose sum with `x` is a constant the columns
	/// cannot hold.
	fn carry_to(bucket: &[Vec<Lit>], mut c: usize, x: Lit) -> Option<usize> {
		while c < bucket.len() && bucket[c].contains(&x) {
			c += 1;
		}
		(c >= bucket.len() || !bucket[c].contains(&!x)).then_some(c)
	}

	/// Encode `Σ cᵢ·litᵢ + constant ≷ k` over the literals themselves.
	fn encode_weighted<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		mut terms: Vec<(Lit, Coeff)>,
		constant: Coeff,
		cmp: LimitComp,
		k: Coeff,
	) -> Result {
		let rhs = k - constant;
		if rhs < 0 {
			return db.contradiction();
		}
		if rhs == 0 {
			// Every coefficient is positive, so a sum of zero fixes them all.
			return terms
				.into_iter()
				.try_for_each(|(lit, _)| db.add_clause([!lit]));
		}
		let rhs = PosCoeff::new(rhs);

		// A literal worth more than the bound never holds, and the columns
		// below stop at the bound's last bit.
		for &(lit, coef) in &terms {
			if coef > *rhs {
				db.add_clause([!lit])?;
			}
		}
		terms.retain(|&(_, coef)| coef <= *rhs);

		let mut k = as_binary(rhs, None);
		let bits = k.len();
		let first_zero = rhs.trailing_ones() as usize;
		debug_assert!(k[bits - 1]);

		let all_terms = || terms.iter().map(|&(lit, coef)| (lit, PosCoeff::new(coef)));

		let mut bucket = vec![Vec::new(); bits];
		for (i, bucket) in bucket.iter_mut().enumerate().take(bits) {
			for (lit, coef) in all_terms() {
				if *coef & (1 << i) != 0 {
					bucket.push(lit);
				}
			}
		}

		// Under `=` each bit is forced directly, which saves a literal; under
		// `≤` the sums stay in the buckets for the comparison below.
		let mut sum = vec![None; bits];
		// Under `=` a column with a known sum fixes the parity of its inputs,
		// and inputs whose parity is already fixed need no second circuit.
		let mut forced: Vec<Lit> = Vec::new();
		let mut fixed: Vec<(Vec<Lit>, bool)> = Vec::new();
		for b in 0..bits {
			match bucket[b].len() {
				0 => {
					if k[b] && cmp == LimitComp::Equal {
						return db.contradiction();
					}
				}
				1 => {
					let x = bucket[b].pop().unwrap();
					if cmp == LimitComp::Equal {
						let unit = if k[b] { x } else { !x };
						if !forced.contains(&unit) {
							db.add_clause([unit])?;
							forced.push(unit);
						}
					} else {
						sum[b] = Some(x);
					}
				}
				_ => {
					while bucket[b].len() >= 2 {
						let last = bucket[b].len() <= 3;
						let group = if last {
							bucket[b].split_off(0)
						} else {
							let i = bucket[b].len() - 3;
							bucket[b].split_off(i)
						};
						debug_assert!(group.len() == 3 || group.len() == 2);
						let lits = group.iter().copied().map(BoolVal::Lit).collect_vec();

						if last && cmp == LimitComp::Equal {
							// The result is known, so no literal is needed.
							let inputs = group
								.into_iter()
								.sorted_by_key(|&l| i32::from(l))
								.collect_vec();
							let key = (inputs, k[b]);
							if !fixed.contains(&key) {
								let _ = Self::sum_circuit(
									db,
									&lits,
									Some(BoolVal::Const(k[b])),
									String::new(),
								)?;
								fixed.push(key);
							}
						} else if cmp == LimitComp::Equal
							&& bucket[b].len() == 1
							&& (k[b] || Self::carry_to(&bucket, b + 1, bucket[b][0]).is_some())
						{
							// The known parity makes this sum the last input or
							// its negation.
							Self::output_other_input(
								db,
								&mut bucket,
								b,
								k[b],
								&lits,
								Self::sum_circuit,
							)?;
						} else if cmp != LimitComp::LessEq || !last || b >= first_zero {
							// Only bits above the first zero of `k` can matter.
							let sum = new_named_lit!(
								db,
								if last {
									crate::trace::subscripted_name("∑", b)
								} else {
									crate::trace::subscripted_name(
										&format!("iS{b}"),
										(bucket[b].len() / 3) + 1,
									)
								}
							);
							let _ = Self::sum_circuit(
								db,
								&lits,
								Some(BoolVal::Lit(sum)),
								String::new(),
							)?;
							bucket[b].push(sum);
						}

						// Under `=` two inputs of known sum differ and carry
						// nothing, or agree and carry either one.
						let known = last && cmp == LimitComp::Equal && lits.len() == 2;
						if known && (k[b] || Self::carry_either(db, &mut bucket, b + 1, &lits)?) {
							// Nothing is left to carry.
						} else if b + 1 >= bits {
							// A carry here would put the sum past `k`.
							let _ = Self::carry_circuit(
								db,
								&lits,
								Some(BoolVal::Const(false)),
								String::new(),
							)?;
						} else if last && cmp == LimitComp::Equal && bucket[b + 1].is_empty() {
							// The result is known, so no literal is needed.
							let _ = Self::carry_circuit(
								db,
								&lits,
								Some(BoolVal::Const(k[b + 1])),
								String::new(),
							)?;
							k[b + 1] = false;
						} else if last
							&& cmp == LimitComp::Equal
							&& bucket[b + 1].len() == 1
							// A carry on the variable of one of its own inputs gives
							// clauses that hold or repeat.
							&& !lits.iter().any(|l| matches!(l, BoolVal::Lit(x) if x.var() == bucket[b + 1][0].var()))
							&& (k[b + 1] || Self::carry_to(&bucket, b + 2, bucket[b + 1][0]).is_some())
						{
							// The next column's known sum makes this carry
							// its one other input or that input's negation.
							Self::output_other_input(
								db,
								&mut bucket,
								b + 1,
								k[b + 1],
								&lits,
								Self::carry_circuit,
							)?;
							k[b + 1] = false;
						} else {
							let carry_lit = new_named_lit!(
								db,
								if last {
									crate::trace::subscripted_name("c", b)
								} else {
									crate::trace::subscripted_name(
										&format!("iC{b}"),
										(bucket[b].len() / 3) + 1,
									)
								}
							);
							let _ = Self::carry_circuit(
								db,
								&lits,
								Some(BoolVal::Lit(carry_lit)),
								String::new(),
							)?;
							bucket[b + 1].push(carry_lit);
						}
					}
					debug_assert!(
						(cmp == LimitComp::Equal && bucket[b].is_empty())
							|| (cmp == LimitComp::LessEq
								&& (bucket[b].len() == 1 || b < first_zero))
					);
					sum[b] = bucket[b].pop();
				}
			}
		}
		debug_assert!(cmp != LimitComp::Equal || sum.iter().all(|x| x.is_none()));

		if cmp == LimitComp::LessEq {
			// A bucket that stayed empty means that bit of the sum is zero.
			let sum = sum
				.iter()
				.map(|&l| l.map_or(BoolVal::Const(false), BoolVal::Lit))
				.collect_vec();
			lex_leq_const(db, &sum, rhs, bits)?;
		}
		Ok(())
	}

	/// Give `circuit` over `lits` the output that column `c`'s known sum `k_c`
	/// makes its one other input `y`, or `¬y`, carrying `y` on where the two
	/// come to `2·y`.
	///
	/// The caller checks that [`Self::carry_into`] can place `y`.
	fn output_other_input<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		bucket: &mut [Vec<Lit>],
		c: usize,
		k_c: bool,
		lits: &[BoolVal],
		circuit: fn(&mut Db, &[BoolVal], Option<BoolVal>, String) -> Result<BoolVal>,
	) -> Result {
		let y = bucket[c].pop().unwrap();
		let _ = circuit(
			db,
			lits,
			Some(BoolVal::Lit(if k_c { !y } else { y })),
			String::new(),
		)?;
		if !k_c {
			let placed = Self::carry_into(db, bucket, c + 1, y)?;
			debug_assert!(placed, "the caller checks that it can be");
		}
		Ok(())
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for AdderEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for AdderEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Count> for AdderEncoder {
	fn encode(&self, db: &mut Db, con: &Count) -> Result {
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db> Encoder<Db, NormalizedBoolLinear> for AdderEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "adder_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedBoolLinear) -> Result {
		// Already the weighted literals the sum is built from, so there is no
		// integer to read them back out of.
		let terms = con.terms().iter().map(|&(lit, c)| (lit, *c)).collect_vec();
		Self::encode_weighted(db, terms, 0, con.cmp(), con.k())
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for AdderEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "adder_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		// Adding bit by bit has no use for how the terms are grouped.
		let (terms, constant) = Self::weighted_literals(db, con)?;
		Self::encode_weighted(db, terms, constant, con.cmp(), con.k())
	}
}

#[cfg(test)]
mod tests {
	use rangelist::RangeList;
	use traced_test::test;

	use crate::{
		decision::integer::IntVar,
		helpers::tests::{brute_force, linear_test_suite, models, prelude::*},
	};

	#[test]
	fn a_bit_worth_more_than_the_bound_is_ruled_out() {
		// The top bit of `x` is worth 128, which is past the bound's own bits.
		for cmp in [LimitComp::LessEq, LimitComp::Equal] {
			let mut cnf = Cnf::default();
			let x = IntVar::new(RangeList::from(0..=138));
			let con = NormalizedIntLinear::new(
				vec![(PosCoeff::new(1), x.clone())],
				cmp.clone(),
				PosCoeff::new(113),
			);
			AdderEncoder::default().encode(&mut cnf, &con).unwrap();
			let values = models(&cnf, |model| x.value(model));
			assert!(!values.is_empty());
			for value in values {
				assert!(value <= 113, "{value} is past the bound");
				assert!(cmp == LimitComp::LessEq || value == 113);
			}
		}
	}

	#[test]
	fn a_carried_input_already_in_the_next_column_moves_up() {
		assert_lean_linear(
			&LinearEncoder::<AdderEncoder>::default(),
			&[4, 4, 4, 3, 3],
			Comparator::Equal,
			14,
		);
	}

	#[test]
	fn a_carry_into_a_column_of_one_input_is_that_input() {
		assert_lean_linear(
			&LinearEncoder::<AdderEncoder>::default(),
			&[1, 1, 1, 2],
			Comparator::Equal,
			3,
		);
	}

	#[test]
	fn a_carry_is_never_one_of_its_own_inputs() {
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(3).iter_lits().collect_vec();
		let con = Linear::new(LinExp::from_slices(&[3, 5, 5], &lits), Comparator::Equal, 5);
		LinearEncoder::<AdderEncoder>::default()
			.encode(&mut cnf, &con)
			.unwrap();
		assert!(
			cnf.iter().all(|c| !c.iter().any(|&l| c.contains(&!l))),
			"a carry circuit whose output is one of its inputs has clauses that always hold"
		);
		assert_checker(&cnf, &con);
	}

	#[test]
	fn a_column_of_two_equal_inputs_carries_one_of_them() {
		assert_lean_linear(
			&LinearEncoder::<AdderEncoder>::default(),
			&[3, 4, 4, 1],
			Comparator::Equal,
			5,
		);
	}

	#[test]
	fn a_column_of_two_inputs_with_odd_sum_carries_nothing() {
		assert_lean_linear(
			&LinearEncoder::<AdderEncoder>::default(),
			&[5, 4, 1],
			Comparator::Equal,
			9,
		);
	}

	#[test]
	fn a_dense_coefficient_is_synthesised_rather_than_carried() {
		// `255·x` is eight partial products for the columns to carry, and one
		// subtraction to build outright.
		let mut table = format!(
			"{:>6} {:>8} {:>7} {:>8}\n",
			"c", "popcount", "vars", "clauses"
		);
		for c in [3, 5, 15, 85, 127, 255] {
			let mut cnf = Cnf::default();
			let x = IntVar::new(RangeList::from(0..=15));
			let con = NormalizedIntLinear::new(
				vec![(PosCoeff::new(c), x.clone())],
				LimitComp::LessEq,
				PosCoeff::new(c * 9),
			);
			AdderEncoder::default().encode(&mut cnf, &con).unwrap();
			assert!(
				x.has_binary_encoding() && !x.has_order_encoding(),
				"the adder reads a variable in binary, never in order form"
			);
			table += &format!(
				"{c:>6} {:>8} {:>7} {:>8}\n",
				(c as u32).count_ones(),
				cnf.num_vars(),
				cnf.num_clauses()
			);
		}
		expect_file!("linear/coefficients.size").assert_eq(&table);
	}

	#[test]
	fn a_literal_alone_in_two_buckets_is_forced_once() {
		assert_lean_linear(
			&LinearEncoder::<AdderEncoder>::default(),
			&[6, 1],
			Comparator::Equal,
			6,
		);
	}

	#[test]
	fn a_literal_on_two_zero_bits_of_the_bound_is_bounded_once() {
		assert_lean_linear(
			&LinearEncoder::<AdderEncoder>::default(),
			&[4, 3, 4],
			Comparator::LessEq,
			4,
		);
	}

	#[test]
	fn a_plain_constraint_weighs_the_literals_it_came_from() {
		// Reading a pseudo-Boolean constraint as integers and back has to give
		// what went in, or the adder pays for the detour.
		let mut cnf = Cnf::default();
		let lits: Vec<Lit> = (0..3).map(|_| cnf.new_lit()).collect();
		let coeffs = [1, 2, 5];
		let terms = lits
			.iter()
			.zip(coeffs)
			.map(|(&l, c)| {
				at_most_one_var(&mut cnf, &[(l, PosCoeff::new(c))], "x", true)
					.map(|x| (PosCoeff::new(1), x))
			})
			.collect::<Result<Vec<_>, _>>()
			.unwrap();
		let con = NormalizedIntLinear::new(terms, LimitComp::LessEq, PosCoeff::new(6));

		let (terms, constant) = AdderEncoder::weighted_literals(&mut cnf, &con).unwrap();
		assert_eq!(constant, 0);
		assert_eq!(
			terms,
			lits.iter().copied().zip(coeffs).collect_vec(),
			"the literals and coefficients should be the ones given"
		);
	}

	#[test]
	fn a_term_that_takes_away_negates_the_product_it_adds() {
		// `≥` reaches the adder as negated coefficients. Coprime coefficients
		// keep aggregation from dividing them.
		let doms = [RangeList::from(0..=15), RangeList::from(0..=15)];
		for (coeffs, cmp, k, products) in [
			([255, 254], Comparator::LessEq, 2800, [255, 254]),
			([255, 254], Comparator::GreaterEq, 2800, [255, 254]),
			([255, 254], Comparator::Equal, 2800, [255, 254]),
			([255, -254], Comparator::LessEq, 100, [255, 254]),
		] {
			let mut cnf = Cnf::default();
			let (x, y) = (
				IntVar::new(doms[0].clone()).with_label("x"),
				IntVar::new(doms[1].clone()).with_label("y"),
			);
			let exp = x.clone() * coeffs[0] + y.clone() * coeffs[1];
			LinearEncoder::<AdderEncoder>::default()
				.encode(&mut cnf, &Linear::new(exp, cmp, k))
				.unwrap();
			for (v, product) in [&x, &y].into_iter().zip(products) {
				assert!(
					v.has_binary_encoding() && !v.has_order_encoding(),
					"the adder reads a variable in binary, never in order form"
				);
				assert!(
					v.product(product).is_some(),
					"{coeffs:?} {cmp:?} {k} builds {product}·{v}"
				);
			}
			let mut seen = models(&cnf, |value| vec![x.value(value), y.value(value)]);
			seen.sort_unstable();
			seen.dedup();
			assert_eq!(
				seen,
				brute_force(&coeffs, &doms, cmp, k),
				"{coeffs:?} {cmp:?} {k}"
			);
		}
	}

	#[test]
	fn a_view_the_variable_has_is_not_a_reason_to_decline() {
		// What matters is whether the binary view has to be *made*, not whether
		// some other view happens to exist alongside it.
		let dense = 255;
		let built = |views: &dyn Fn(&mut Cnf, &IntVar)| {
			let mut cnf = Cnf::default();
			let x = IntVar::new(RangeList::from(0..=15));
			views(&mut cnf, &x);
			let con = NormalizedIntLinear::new(
				vec![(PosCoeff::new(dense), x.clone())],
				LimitComp::LessEq,
				PosCoeff::new(dense * 9),
			);
			AdderEncoder::default().encode(&mut cnf, &con).unwrap();
			x.product(dense).is_some()
		};

		assert!(built(&|_, _| {}), "a variable with no view yet");
		assert!(
			built(&|cnf, x| {
				x.require_binary_encoding(cnf).unwrap();
			}),
			"a variable already in binary"
		);
		assert!(
			built(&|cnf, x| {
				x.require_binary_encoding(cnf).unwrap();
				x.require_order_encoding(cnf).unwrap();
			}),
			"a variable in binary, whatever else it also has"
		);
		assert!(
			!built(&|cnf, x| {
				x.require_order_encoding(cnf).unwrap();
			}),
			"a variable held only in order form would have to be channelled"
		);
	}

	#[test]
	fn columns_with_the_same_inputs_fix_their_parity_once() {
		assert_lean_linear(
			&LinearEncoder::<AdderEncoder>::default(),
			&[1, 6, 6],
			Comparator::Equal,
			6,
		);
	}

	#[test]
	fn every_small_constraint_has_exactly_its_solutions() {
		assert_exact_on_small_linear(&LinearEncoder::<AdderEncoder>::default(), 4, 4);
	}

	#[test]
	fn every_small_integer_constraint_has_exactly_its_solutions() {
		assert_exact_on_small_int_linear(&LinearEncoder::<AdderEncoder>::default());
	}

	#[test]
	fn ripple_carry_adder_computes_the_sum() {
		for (x_bits, y_bits) in [(1, 1), (2, 2), (3, 1)] {
			let mut cnf = Cnf::default();
			let (x, y) = (
				binary_literals(&mut cnf, x_bits),
				binary_literals(&mut cnf, y_bits),
			);
			let z = AdderEncoder::ripple_carry_adder(&mut cnf, &x, &y, None, None).unwrap();

			let solutions = all_binary_solutions(&cnf, &[&x, &y, &z]);
			// Wide enough never to overflow, so each input has one model.
			assert_eq!(solutions.len(), 1 << (x_bits + y_bits));
			for s in &solutions {
				assert_eq!(s[2], s[0] + s[1], "{} + {} != {}", s[0], s[1], s[2]);
			}
		}
	}

	#[test]
	fn ripple_carry_adder_constrains_a_given_sum() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			binary_literals(&mut cnf, 2),
			binary_literals(&mut cnf, 2),
			binary_literals(&mut cnf, 2),
		);
		let _ = AdderEncoder::ripple_carry_adder(&mut cnf, &x, &y, None, Some(&z)).unwrap();

		let solutions = all_binary_solutions(&cnf, &[&x, &y, &z]);
		// `z` is only two bits wide, so sums that do not fit are ruled out.
		let expected: Vec<Vec<Coeff>> = (0..4)
			.flat_map(|a| (0..4).map(move |b| (a, b)))
			.filter(|(a, b)| a + b < 4)
			.map(|(a, b)| vec![a, b, a + b])
			.collect();
		assert_eq!(solutions, expected);
	}

	#[test]
	fn ripple_carry_adder_handles_fixed_bits() {
		// Shifts and grounding leave constant bits, which the adder folds in
		// rather than assuming every bit is a literal.
		let mut cnf = Cnf::default();
		let x = vec![
			BoolVal::Const(true),
			BoolVal::Lit(cnf.new_lit()),
			BoolVal::Const(false),
		];
		let y = vec![BoolVal::Const(true), BoolVal::Lit(cnf.new_lit())];
		let z = AdderEncoder::ripple_carry_adder(&mut cnf, &x, &y, None, None).unwrap();

		let solutions = all_binary_solutions(&cnf, &[&x, &y, &z]);
		assert_eq!(solutions.len(), 4);
		for s in &solutions {
			assert_eq!(s[2], s[0] + s[1], "{} + {} != {}", s[0], s[1], s[2]);
		}
	}

	card_test_suite!(AdderEncoder::default());
	card1_test_suite! {
		adder_encoder_card1, AdderEncoder::default()
	}
	linear_test_suite! {adder_encoder, AdderEncoder::default()}
}
