use num::Integer;
use rustc_hash::FxHashMap;

use crate::{
	helpers::{as_binary, XorConstraint, XorEncoder},
	int::LitOrConst,
	linear::{LimitComp, PosCoeff},
	trace::{emit_clause, new_var},
	ClauseDatabase, Coefficient, Comparator, Encoder, Linear, Literal, Result, Unsatisfiable,
};

/// Encoder for the linear constraints that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
#[derive(Default)]
pub struct AdderEncoder {}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for AdderEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "adder_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		let pair = &lin
			.terms
			.iter()
			.flat_map(|part| part.iter().map(|(lit, coef)| (lit.clone(), **coef)))
			.collect::<FxHashMap<DB::Lit, C>>();

		debug_assert!(lin.cmp == LimitComp::LessEq || lin.cmp == LimitComp::Equal);
		// The number of relevant bits in k
		let bits = (C::zero().leading_zeros() - lin.k.leading_zeros()) as usize;
		let first_zero = lin.k.trailing_ones() as usize;
		let mut k = as_binary::<DB::Lit, C>(lin.k.clone(), Some(bits));
		debug_assert!(k[bits - 1]);

		// Create structure with which coefficients use which bits
		let mut bucket = vec![Vec::new(); bits];
		for (i, bucket) in bucket.iter_mut().enumerate().take(bits) {
			for (lit, coef) in pair {
				if *coef & (C::one() << i) != C::zero() {
					bucket.push(lit.clone());
				}
			}
		}

		// Compute the sums and carries for each bit layer
		// if comp == Equal, then this is directly enforced (to avoid creating additional literals)
		// otherwise, sum literals are left in the buckets for further processing
		let mut sum = vec![None; bits];
		for b in 0..bits {
			match bucket[b].len() {
				0 => {
					if k[b] && lin.cmp == LimitComp::Equal {
						return Err(Unsatisfiable);
					}
				}
				1 => {
					let x = bucket[b].pop().unwrap();
					if lin.cmp == LimitComp::Equal {
						emit_clause!(db, &[if k[b] { x.clone() } else { x.negate() }])?
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

						// Compute sum
						if last && lin.cmp == LimitComp::Equal {
							// No need to create a new literal, force the sum to equal the result
							sum_circuit(db, lits.as_slice(), LitOrConst::Const(k[b]))?;
						} else if lin.cmp != LimitComp::LessEq || !last || b >= first_zero {
							// Literal is not used for the less-than constraint unless a zero has been seen first
							let sum = new_var!(
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
							sum_circuit(db, lits.as_slice(), LitOrConst::Lit(sum.clone()))?;
							bucket[b].push(sum);
						}

						// Compute carry
						if b + 1 >= bits {
							// Carry will bring the sum to be greater than k, force to be false
							if lits.len() == 2 && lin.cmp == LimitComp::Equal {
								// Already encoded by the XOR to compute the sum
							} else {
								carry_circuit(db, &lits[..], LitOrConst::Const(false))?
							}
						} else if last && lin.cmp == LimitComp::Equal && bucket[b + 1].is_empty() {
							// No need to create a new literal, force the carry to equal the result
							carry_circuit(db, &lits[..], LitOrConst::Const(k[b + 1]))?;
							// Mark k[b + 1] as false (otherwise next step will fail)
							k[b + 1] = false;
						} else {
							let carry = new_var!(
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
							carry_circuit(db, lits.as_slice(), LitOrConst::Lit(carry.clone()))?;
							bucket[b + 1].push(carry);
						}
					}
					debug_assert!(
						(lin.cmp == LimitComp::Equal && bucket[b].is_empty())
							|| (lin.cmp == LimitComp::LessEq
								&& (bucket[b].len() == 1 || b < first_zero))
					);
					sum[b] = bucket[b].pop();
				}
			}
		}
		// In case of equality this has been enforced
		debug_assert!(lin.cmp != LimitComp::Equal || sum.iter().all(|x| x.is_none()));

		// Enforce less-than constraint
		if lin.cmp == LimitComp::LessEq {
			lex_leq_const(
				db,
				&sum.into_iter().map(|l| l.into()).collect::<Vec<_>>(),
				lin.k.clone(),
				bits,
			)?;
		}
		Ok(())
	}
}

/// Uses lexicographic constraint to constrain x:B ≦ k
#[cfg_attr(
	feature = "trace",
	tracing::instrument(name = "lex_lesseq_const", skip_all)
)]
pub(crate) fn lex_leq_const<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	x: &[LitOrConst<DB::Lit>],
	k: PosCoeff<C>,
	bits: usize,
) -> Result {
	// For every zero bit in k:
	// - either the `x` bit is also zero, or
	// - a higher `x` bit is zero that was one in k.
	let k = as_binary::<DB::Lit, C>(k, Some(bits));
	(0..bits).filter(|i| !k[*i]).try_for_each(|i| {
		clause(
			db,
			&(i..bits)
				.filter_map(|j| (j == i || k[j]).then(|| -x[j].clone()))
				.collect::<Vec<_>>(),
		)
	})
}

/// Uses lexicographic constraint to constrain x:B >= k
#[cfg_attr(feature = "trace", tracing::instrument(name = "lex_geq", skip_all))]
pub(crate) fn lex_geq_const<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	x: &[LitOrConst<DB::Lit>],
	k: PosCoeff<C>,
	bits: usize,
) -> Result {
	let k = as_binary::<DB::Lit, C>(k, Some(bits));
	(0..bits).filter(|i| k[*i]).try_for_each(|i| {
		clause(
			db,
			&(i..bits)
				.filter_map(|j| (j == i || !k[j]).then(|| x[j].clone()))
				.collect::<Vec<_>>(),
		)
	})
}

// TODO Implement Mul/Add for Lit (once merged with new Lit struct)
fn carry<DB: ClauseDatabase>(
	db: &mut DB,
	xs: &[LitOrConst<DB::Lit>],
	_lbl: String,
) -> Result<LitOrConst<DB::Lit>> {
	// The carry is true iff at least 2 out of 3 `xs` are true
	let (xs, trues) = filter_fixed_sum(xs);
	let carry = match &xs[..] {
		[] => (trues >= 2).into(), // trues is {0,1,2,3}
		[x] => match trues {
			0 => false.into(),
			1 => x.clone().into(),
			2 => true.into(),
			_ => unreachable!(),
		},
		[x, y] => match trues {
			0 => {
				let and = new_var!(db, _lbl);
				emit_clause!(db, &[x.negate(), y.negate(), and.clone()])?;
				emit_clause!(db, &[x.clone(), and.negate()])?;
				emit_clause!(db, &[y.clone(), and.negate()])?;
				and.into()
			}
			1 => {
				let or = new_var!(db, _lbl);
				emit_clause!(db, &[x.clone(), y.clone(), or.negate()])?;
				emit_clause!(db, &[x.negate(), or.clone()])?;
				emit_clause!(db, &[y.negate(), or.clone()])?;
				or.into()
			}
			_ => unreachable!(),
		},
		[x, y, z] => {
			assert!(trues == 0);
			let carry = new_var!(db, _lbl);

			emit_clause!(db, &[x.clone(), y.clone(), carry.negate()])?; // 2 false -> ~carry
			emit_clause!(db, &[x.clone(), z.clone(), carry.negate()])?; // " ..
			emit_clause!(db, &[y.clone(), z.clone(), carry.negate()])?;

			emit_clause!(db, &[x.negate(), y.negate(), carry.clone()])?; // 2 true -> carry
			emit_clause!(db, &[x.negate(), z.negate(), carry.clone()])?; // " ..
			emit_clause!(db, &[y.negate(), z.negate(), carry.clone()])?;
			carry.into()
		}
		_ => unreachable!(),
	};
	Ok(carry)
}

fn filter_fixed_sum<Lit: Literal>(xs: &[LitOrConst<Lit>]) -> (Vec<Lit>, usize) {
	let mut trues = 0;
	(
		xs.iter()
			.filter_map(|x| match x {
				LitOrConst::Lit(l) => Some(l.clone()),
				LitOrConst::Const(true) => {
					trues += 1;
					None
				}
				LitOrConst::Const(false) => None,
			})
			.collect(),
		trues,
	)
}

fn xor<DB: ClauseDatabase>(
	db: &mut DB,
	xs: &[LitOrConst<DB::Lit>],
	_lbl: String,
) -> Result<LitOrConst<DB::Lit>> {
	let (xs, trues) = filter_fixed_sum(xs);

	let is_even = match &xs[..] {
		[] => LitOrConst::Const(false), // TODO ?? why not `true`?
		[x] => LitOrConst::Lit(x.clone()),
		[x, y] => {
			assert!(trues <= 1);
			let is_even = new_var!(db, _lbl);

			emit_clause!(db, &[x.clone(), y.clone(), is_even.negate()])?; // 0
			emit_clause!(db, &[x.negate(), y.negate(), is_even.negate()])?; // 2

			emit_clause!(db, &[x.negate(), y.clone(), is_even.clone()])?; // 1
			emit_clause!(db, &[x.clone(), y.negate(), is_even.clone()])?; // 1
			LitOrConst::Lit(is_even)
		}
		[x, y, z] => {
			assert!(trues == 0);
			let is_even = new_var!(db, _lbl);

			emit_clause!(db, &[x.clone(), y.clone(), z.clone(), is_even.negate()])?; // 0
			emit_clause!(db, &[x.clone(), y.negate(), z.negate(), is_even.negate()])?; // 2
			emit_clause!(db, &[x.negate(), y.clone(), z.negate(), is_even.negate()])?; // 2
			emit_clause!(db, &[x.negate(), y.negate(), z.clone(), is_even.negate()])?; // 2

			emit_clause!(db, &[x.negate(), y.negate(), z.negate(), is_even.clone()])?; // 3
			emit_clause!(db, &[x.negate(), y.clone(), z.clone(), is_even.clone()])?; // 1
			emit_clause!(db, &[x.clone(), y.negate(), z.clone(), is_even.clone()])?; // 1
			emit_clause!(db, &[x.clone(), y.clone(), z.negate(), is_even.clone()])?; // 1
			LitOrConst::Lit(is_even)
		}
		_ => unimplemented!(),
	};

	// If trues is odd, negate sum
	Ok(if trues.is_even() { is_even } else { -is_even })
}

#[cfg_attr(feature = "trace", tracing::instrument(name = "log_enc_add", skip_all, fields(constraint = format!("{xs:?} + {ys:?}"))))]
pub(crate) fn log_enc_add_fn<DB: ClauseDatabase>(
	db: &mut DB,
	xs: &[LitOrConst<DB::Lit>],
	ys: &[LitOrConst<DB::Lit>],
	cmp: &Comparator,
	mut c: LitOrConst<DB::Lit>,
) -> Result<Vec<LitOrConst<DB::Lit>>> {
	assert!(cmp == &Comparator::Equal);
	let zs = (0..(itertools::max([xs.len(), ys.len()]).unwrap()) + 1)
		.map(|i| {
			let (x, y) = (bit(xs, i), bit(ys, i));
			let z = xor(db, &[x.clone(), y.clone(), c.clone()], format!("z_{}", i));
			c = carry(db, &[x, y, c.clone()], format!("c_{}", i + 1))?;
			z
		})
		.collect::<Result<Vec<_>>>()?;

	// Remove last bit if equal to second-to-last bit
	let zs = if zs.len() > 1 && zs[zs.len() - 1] == zs[zs.len() - 2] {
		zs[..(zs.len() - 1)].to_vec()
	} else {
		zs
	};

	Ok(zs)
}

fn bit<Lit: Literal>(x: &[LitOrConst<Lit>], i: usize) -> LitOrConst<Lit> {
	x.get(i)
		.map(LitOrConst::<Lit>::clone)
		.unwrap_or_else(|| x.last().unwrap().clone()) // 2 comp's sign extend (TODO maybe more efficient to just min(i, len(x)-1)
}

#[cfg_attr(feature = "trace", tracing::instrument(name = "log_enc_add", skip_all, fields(constraint = format!("{x:?} + {y:?} {cmp} {z:?}"))))]
pub(crate) fn log_enc_add_<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[LitOrConst<DB::Lit>],
	y: &[LitOrConst<DB::Lit>],
	cmp: &Comparator,
	z: &[LitOrConst<DB::Lit>],
) -> Result {
	let n = itertools::max([x.len(), y.len(), z.len()]).unwrap();

	match cmp {
		Comparator::Equal => {
			let c = &std::iter::once(LitOrConst::Const(false))
				.chain((1..n).map(|_i| {
					LitOrConst::Lit(new_var!(db, crate::trace::subscripted_name("c", _i)))
				}))
				.collect::<Vec<_>>();
			for i in 0..n {
				// sum circuit
				clause(db, &[bit(x, i), bit(y, i), bit(c, i), -bit(z, i)])?;
				clause(db, &[bit(x, i), -bit(y, i), -bit(c, i), -bit(z, i)])?;
				clause(db, &[-bit(x, i), bit(y, i), -bit(c, i), -bit(z, i)])?;
				clause(db, &[-bit(x, i), -bit(y, i), bit(c, i), -bit(z, i)])?;

				clause(db, &[-bit(x, i), -bit(y, i), -bit(c, i), bit(z, i)])?;
				clause(db, &[-bit(x, i), bit(y, i), bit(c, i), bit(z, i)])?;
				clause(db, &[bit(x, i), -bit(y, i), bit(c, i), bit(z, i)])?;
				clause(db, &[bit(x, i), bit(y, i), -bit(c, i), bit(z, i)])?;

				// carry circuit
				clause(db, &[bit(x, i), bit(y, i), -bit(c, i + 1)])?;
				clause(db, &[bit(x, i), bit(c, i), -bit(c, i + 1)])?;
				clause(db, &[bit(y, i), bit(c, i), -bit(c, i + 1)])?;
				clause(db, &[-bit(x, i), -bit(y, i), bit(c, i + 1)])?;
				clause(db, &[-bit(x, i), -bit(c, i), bit(c, i + 1)])?;
				clause(db, &[-bit(y, i), -bit(c, i), bit(c, i + 1)])?;
			}
			Ok(())
		}
		ineq => {
			let c = &(0..n)
				.map(|_i| LitOrConst::Lit(new_var!(db, crate::trace::subscripted_name("c", _i))))
				.chain(std::iter::once(LitOrConst::Const(true)))
				.collect::<Vec<_>>();

			assert!(
				y.iter().all(|yi| matches!(yi, LitOrConst::Const(false))),
				"Expected {y:?} to be zero for x<=z lex comparison"
			);

			// higher i -> more significant
			for i in 0..n {
				// c = all more significant bits are equal AND current one is
				// if up to i is equal, all preceding must be equal
				clause(db, &[-bit(c, i), bit(c, i + 1)])?;
				// if up to i is equal, x<->z
				clause(db, &[-bit(c, i), -bit(x, i), bit(z, i)])?;
				clause(db, &[-bit(c, i), -bit(z, i), bit(x, i)])?;

				// if not up to i is equal, either preceding bit was not equal, or x!=z
				clause(db, &[bit(c, i), -bit(c, i + 1), bit(x, i), bit(z, i)])?;
				clause(db, &[bit(c, i), -bit(c, i + 1), -bit(x, i), -bit(z, i)])?;

				// if preceding bits are equal, then x<=z (or x>=z)
				match ineq {
					Comparator::LessEq => clause(db, &[-bit(c, i + 1), -bit(x, i), bit(z, i)]),
					Comparator::GreaterEq => clause(db, &[-bit(c, i + 1), bit(x, i), -bit(z, i)]),
					Comparator::Equal => unreachable!(),
				}?;
			}

			Ok(())
		}
	}
}

fn clause<DB: ClauseDatabase>(db: &mut DB, lits: &[LitOrConst<DB::Lit>]) -> Result {
	if let Ok(clause) = lits
		.iter()
		.filter_map(|lit| match lit {
			// TODO does this one exit early on Err? Or did we wrap it the wrong way around?
			LitOrConst::Lit(lit) => Some(Ok(lit.clone())),
			LitOrConst::Const(true) => Some(Err(())), // clause satisfied
			LitOrConst::Const(false) => None,         // literal falsified
		})
		.collect::<std::result::Result<Vec<_>, ()>>()
	{
		emit_clause!(db, &clause)
	} else {
		Ok(())
	}
}

/// Encode the adder sum circuit
///
/// This function accepts either 2 literals as `input` (half adder) or 3
/// literals (full adder).
///
/// `output` can be either a literal, or a constant Boolean value.
#[cfg_attr(feature = "trace", tracing::instrument(name = "sum_circuit", skip_all, fields(constraint = trace_print_sum(input, &output))))]
fn sum_circuit<DB: ClauseDatabase>(
	db: &mut DB,
	input: &[DB::Lit],
	output: LitOrConst<DB::Lit>,
) -> Result {
	match output {
		LitOrConst::Lit(sum) => match input {
			[a, b] => {
				emit_clause!(db, &[a.negate(), b.negate(), sum.negate()])?;
				emit_clause!(db, &[a.negate(), b.clone(), sum.clone()])?;
				emit_clause!(db, &[a.clone(), b.negate(), sum.clone()])?;
				emit_clause!(db, &[a.clone(), b.clone(), sum.negate()])
			}
			[a, b, c] => {
				emit_clause!(db, &[a.clone(), b.clone(), c.clone(), sum.negate()])?;
				emit_clause!(db, &[a.clone(), b.negate(), c.negate(), sum.negate()])?;
				emit_clause!(db, &[a.negate(), b.clone(), c.negate(), sum.negate()])?;
				emit_clause!(db, &[a.negate(), b.negate(), c.clone(), sum.negate()])?;

				emit_clause!(db, &[a.negate(), b.negate(), c.negate(), sum.clone()])?;
				emit_clause!(db, &[a.negate(), b.clone(), c.clone(), sum.clone()])?;
				emit_clause!(db, &[a.clone(), b.negate(), c.clone(), sum.clone()])?;
				emit_clause!(db, &[a.clone(), b.clone(), c.negate(), sum])
			}
			_ => unreachable!(),
		},
		LitOrConst::Const(true) => XorEncoder::default().encode(db, &XorConstraint::new(input)),
		LitOrConst::Const(false) => match input {
			[a, b] => {
				emit_clause!(db, &[a.clone(), b.negate()])?;
				emit_clause!(db, &[a.negate(), b.clone()])
			}
			[a, b, c] => {
				emit_clause!(db, &[a.negate(), b.negate(), c.negate()])?;
				emit_clause!(db, &[a.negate(), b.clone(), c.clone()])?;
				emit_clause!(db, &[a.clone(), b.negate(), c.clone()])?;
				emit_clause!(db, &[a.clone(), b.clone(), c.negate()])
			}
			_ => unreachable!(),
		},
	}
}

#[cfg(feature = "trace")]
fn trace_print_sum<Lit: Literal>(input: &[Lit], output: &LitOrConst<Lit>) -> String {
	use crate::trace::trace_print_lit;
	let inner = itertools::join(input.iter().map(trace_print_lit), " ⊻ ");
	match output {
		LitOrConst::Lit(r) => format!("{} ≡ {}", trace_print_lit(r), inner),
		LitOrConst::Const(true) => inner,
		LitOrConst::Const(false) => format!("¬({inner})"),
	}
}

/// Encode the adder carry circuit
///
/// This function accepts either 2 literals as `input` (half adder) or 3
/// literals (full adder).
///
/// `output` can be either a literal, or a constant Boolean value.
#[cfg_attr(feature = "trace", tracing::instrument(name = "carry_circuit", skip_all, fields(constraint = trace_print_carry(input, &output))))]
fn carry_circuit<DB: ClauseDatabase>(
	db: &mut DB,
	input: &[DB::Lit],
	output: LitOrConst<DB::Lit>,
) -> Result {
	match output {
		LitOrConst::Lit(carry) => match input {
			[a, b] => {
				emit_clause!(db, &[a.negate(), b.negate(), carry.clone()])?;
				emit_clause!(db, &[a.clone(), carry.negate()])?;
				emit_clause!(db, &[b.clone(), carry.negate()])
			}
			[a, b, c] => {
				emit_clause!(db, &[a.clone(), b.clone(), carry.negate()])?;
				emit_clause!(db, &[a.clone(), c.clone(), carry.negate()])?;
				emit_clause!(db, &[b.clone(), c.clone(), carry.negate()])?;

				emit_clause!(db, &[a.negate(), b.negate(), carry.clone()])?;
				emit_clause!(db, &[a.negate(), c.negate(), carry.clone()])?;
				emit_clause!(db, &[b.negate(), c.negate(), carry])
			}
			_ => unreachable!(),
		},
		LitOrConst::Const(k) => match input {
			[a, b] => {
				if k {
					// TODO: Can we avoid this?
					emit_clause!(db, &[a.clone()])?;
					emit_clause!(db, &[b.clone()])
				} else {
					emit_clause!(db, &[a.negate(), b.negate()])
				}
			}
			[a, b, c] => {
				let neg = |x: &DB::Lit| if k { x.clone() } else { x.negate() };
				emit_clause!(db, &[neg(a), neg(b)])?;
				emit_clause!(db, &[neg(a), neg(c)])?;
				emit_clause!(db, &[neg(b), neg(c)])
			}
			_ => unreachable!(),
		},
	}
}

#[cfg(feature = "trace")]
fn trace_print_carry<Lit: Literal>(input: &[Lit], output: &LitOrConst<Lit>) -> String {
	use crate::trace::trace_print_lit;
	let inner = itertools::join(input.iter().map(trace_print_lit), " + ");
	match output {
		LitOrConst::Lit(r) => format!("{} ≡ ({} > 1)", trace_print_lit(r), inner),
		LitOrConst::Const(true) => format!("{inner} > 1"),
		LitOrConst::Const(false) => format!("{inner} ≤ 1"),
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		cardinality::tests::card_test_suite,
		cardinality_one::tests::card1_test_suite,
		helpers::tests::{assert_enc_sol, assert_sol, TestDB},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp, StaticLinEncoder,
		},
		Cardinality, CardinalityOne, Comparator, Encoder, LinExp, LinearConstraint, LinearEncoder,
		PairwiseEncoder,
	};

	#[test]
	fn test_pb_encode() {
		assert_enc_sol!(
			LinearEncoder::<StaticLinEncoder>::default(),
			4,
			&LinearConstraint::<i32,i32>::new(LinExp::from((1,1)) + (2,1) + (3,1) + (4,2),
			Comparator::LessEq,
			1)
			=>
			vec![
			vec![-4], vec![-3, -1], vec![-2, -1], vec![-3, -2]
			],
			vec![
				vec![-1, -2, -3, -4],
				vec![-1, -2, 3, -4],
				vec![-1, 2, -3, -4],
				vec![1, -2, -3, -4],
			]
		);
	}

	#[test]
	fn test_encoders() {
		// +7*x1 +10*x2 +4*x3 +4*x4 <= 9
		let mut db = TestDB::new(4).expect_solutions(vec![
			vec![-1, -2, -3, -4],
			vec![1, -2, -3, -4],
			vec![-1, -2, 3, -4],
			vec![-1, -2, -3, 4],
		]);
		// TODO encode this if encoder does not support constraint
		assert!(PairwiseEncoder::default()
			.encode(
				&mut db,
				&CardinalityOne {
					lits: vec![1, 2],
					cmp: LimitComp::LessEq
				}
			)
			.is_ok());
		assert!(PairwiseEncoder::default()
			.encode(
				&mut db,
				&CardinalityOne {
					lits: vec![3, 4],
					cmp: LimitComp::LessEq
				}
			)
			.is_ok());
		assert!(LinearEncoder::<StaticLinEncoder<AdderEncoder>>::default()
			.encode(
				&mut db,
				&LinearConstraint::<i32, i32>::new(
					LinExp::default()
						.add_choice(&[(1, 7), (2, 10)])
						.add_choice(&[(3, 4), (4, 4)]),
					Comparator::LessEq,
					9,
				),
			)
			.is_ok());
		db.check_complete();
	}

	linear_test_suite!(AdderEncoder::default());
	card1_test_suite!(AdderEncoder::default());
	card_test_suite!(AdderEncoder::default());
}
