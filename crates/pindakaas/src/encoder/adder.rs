//! Encoding a linear constraint as the circuit that adds its terms up.
//!
//! The literals are bucketed by which bit of their coefficient they set, and
//! each bucket compressed three at a time by full adders. Also holds the sum
//! and carry circuits themselves, which the integer encoders build on.

use std::{cmp::max, num::NonZero};

use itertools::Itertools;

use crate::{
	constraint::{
		linear::{LimitComp, PosCoeff},
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		int_linear::{NormalizedIntLinear, Term},
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

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// Encoder for a linear constraint, as the circuit that adds its terms up.
///
/// Alone among the linear encoders it does not decompose: the terms are
/// summed by adders and the result compared against the bound, so the cost
/// follows the width of the coefficients rather than the number of terms.
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

/// Above this many literals, enumerating the assignments of the wrong parity
/// costs more clauses than a Tseitin transformation costs auxiliary variables.
const DIRECT_PARITY_LITS: usize = 4;

impl AdderEncoder {
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
			let t = (**c, x.clone());
			if let Some(bits) = Self::product_bits(db, &t)? {
				// The product's bits count up from the variable's least value.
				constant += t.0 * t.1.min();
				for (i, b) in bits.into_iter().enumerate() {
					match b {
						BoolVal::Lit(l) => weighted.push((l, 1 << i)),
						BoolVal::Const(true) => constant += 1 << i,
						BoolVal::Const(false) => {}
					}
				}
			} else {
				let (lits, offset) = t.1.as_weighted(db)?;
				weighted.extend(
					lits.into_iter()
						.map(|(l, w)| (l, t.0 * w))
						.filter(|&(_, w)| w != 0),
				);
				constant += t.0 * offset;
			}
		}
		Ok((weighted, constant))
	}

	/// The bits of the term's product, where forming it outright beats letting
	/// the columns carry the coefficient, and `None` where it does not.
	fn product_bits<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		t: &Term,
	) -> Result<Option<Vec<BoolVal>>, Unsatisfiable> {
		// Reading it in binary is free where that view exists, and costs a
		// channel where it does not.
		if !t.1.has_binary_encoding() && (t.1.has_order_encoding() || t.1.has_direct_encoding()) {
			return Ok(None);
		}
		if let Some(bits) = t.1.product(t.0) {
			return Ok(Some(bits));
		}
		let Ok(c) = u32::try_from(t.0) else {
			return Ok(None);
		};
		let Some(width) = NonZero::new(BinaryEncoding::required_bits(t.1.max() - t.1.min()) as u32)
		else {
			return Ok(None);
		};
		// Heuristic: below four set bits the partial products barely overlap,
		// so the columns carry them for almost nothing.
		if c.count_ones() < 4 {
			return Ok(None);
		}
		// Heuristic: one clause per column, against the adders SCM would need;
		// form the product only where it comes out ahead.
		let columns = (c.count_ones() * width.get()).saturating_sub(c.ilog2() + 1);
		let plan = ScmSolution::synthesize(c, ScmObjective::MinAdders(width));
		if plan.cost >= columns {
			return Ok(None);
		}
		Ok(Some(Self::scaled_bits(db, &t.1, t.0, plan)?))
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

		let input = x.binary_encoding(db)?.to_vec();
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
		let cmp = con.cmp();
		// Adding bit by bit has no use for how the terms are grouped.
		let (terms, constant) = Self::weighted_literals(db, con)?;
		let rhs = con.k() - constant;
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

		const ZERO: Coeff = 0;
		let bits = ZERO.leading_zeros() - rhs.leading_zeros();
		let mut k = as_binary(rhs, Some(bits));

		let first_zero = rhs.trailing_ones() as usize;
		let bits = bits as usize;
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
						db.add_clause([if k[b] { x } else { !x }])?;
					} else {
						sum[b] = Some(x);
					}
				}
				_ => {
					while bucket[b].len() >= 2 {
						let last = bucket[b].len() <= 3;
						let lits = if last {
							bucket[b].split_off(0)
						} else {
							let i = bucket[b].len() - 3;
							bucket[b].split_off(i)
						};
						debug_assert!(lits.len() == 3 || lits.len() == 2);
						let lits = lits.into_iter().map(BoolVal::Lit).collect_vec();

						if last && cmp == LimitComp::Equal {
							// The result is known, so no literal is needed.
							let _ = Self::sum_circuit(
								db,
								&lits,
								Some(BoolVal::Const(k[b])),
								String::new(),
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

						if b + 1 >= bits {
							// A carry here would put the sum past `k`.
							if lits.len() == 2 && cmp == LimitComp::Equal {
							} else {
								let _ = Self::carry_circuit(
									db,
									&lits,
									Some(BoolVal::Const(false)),
									String::new(),
								)?;
							}
						} else if last && cmp == LimitComp::Equal && bucket[b + 1].is_empty() {
							// The result is known, so no literal is needed.
							let _ = Self::carry_circuit(
								db,
								&lits,
								Some(BoolVal::Const(k[b + 1])),
								String::new(),
							)?;
							// The next bit of `k` is spent.
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

#[cfg(test)]
mod tests {
	use rangelist::RangeList;
	use traced_test::test;

	use crate::{
		decision::integer::IntVar,
		helpers::tests::{linear_test_suite, prelude::*},
	};

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
				let _ = x.binary_encoding(cnf).unwrap();
			}),
			"a variable already in binary"
		);
		assert!(
			built(&|cnf, x| {
				let _ = x.binary_encoding(cnf).unwrap();
				let _ = x.order_encoding(cnf).unwrap();
			}),
			"a variable in binary, whatever else it also has"
		);
		assert!(
			!built(&|cnf, x| {
				let _ = x.order_encoding(cnf).unwrap();
			}),
			"a variable held only in order form would have to be channelled"
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

	card_test_suite!(AdderEncoder::default());
	card1_test_suite! {
		adder_encoder_card1, AdderEncoder::default()
	}
	linear_test_suite! {adder_encoder, AdderEncoder::default()}
}
