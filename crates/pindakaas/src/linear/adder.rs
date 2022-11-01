use rustc_hash::FxHashMap;

use crate::{
	helpers::{XorConstraint, XorEncoder},
	int::LitOrConst,
	linear::{LimitComp, PosCoeff},
	trace::{emit_clause, new_var},
	ClauseDatabase, Coefficient, Encoder, Linear, Literal, Result, Unsatisfiable,
};

/// Encoder for the linear constraints that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
#[derive(Default)]
pub struct AdderEncoder {}

fn as_binary<C: Coefficient>(k: PosCoeff<C>, bits: usize) -> Vec<bool> {
	(0..bits)
		.map(|b| *k & (C::one() << b) != C::zero())
		.collect::<Vec<_>>()
}

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
		let mut k = as_binary(lin.k.clone(), bits);
		debug_assert!(k[bits - 1]);

		// Create structure with which coefficients use which bits
		let mut bucket = vec![Vec::new(); bits];
		for (i, bucker) in bucket.iter_mut().enumerate().take(bits) {
			for (lit, coef) in pair {
				if *coef & (C::one() << i) != C::zero() {
					bucker.push(lit.clone());
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
			lex_lesseq_const(db, sum.as_slice(), lin.k.clone(), bits)?;
		}
		Ok(())
	}
}

/// Uses lexicographic constraint to constrain x:B ≦ k
pub(crate) fn lex_lesseq_const<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	x: &[Option<DB::Lit>],
	k: PosCoeff<C>,
	bits: usize,
) -> Result {
	let k = as_binary(k, bits);
	// For every zero bit in k:
	// - either the `x` bit is also zero, or
	// - a higher `x` bit is zero that was one in k.
	for i in 0..bits {
		if !k[i] && x[i].is_some() {
			emit_clause!(
				db,
				&(i..bits)
					.filter_map(|j| if j == i || k[j] { x[j].clone() } else { None })
					.map(|lit| lit.negate())
					.collect::<Vec<DB::Lit>>()
			)?;
		}
	}
	Ok(())
}

/// Returns the result, `c`, of adding `a` to `b`, all encoded using the log encoding.
///
/// TODO: Should this use the IntEncoding::Log input??
#[allow(dead_code)]
pub(crate) fn log_enc_add<DB: ClauseDatabase>(
	db: &mut DB,
	a: &[DB::Lit],
	b: &[DB::Lit],
	bits: usize,
) -> Result<Vec<Option<DB::Lit>>> {
	let mut c = Vec::with_capacity(bits);
	let mut carry = None;
	for i in 0..bits {
		let b = [a.get(i), b.get(i), carry.as_ref()]
			.into_iter()
			.flatten()
			.cloned()
			.collect::<Vec<DB::Lit>>();
		match &b[..] {
			[] => {
				c.push(None);
				carry = None;
			}
			[x] => {
				c.push(Some(x.clone()));
				carry = None;
			}
			_ => {
				debug_assert!(b.len() <= 3);
				let sum = new_var!(db, crate::trace::subscripted_name("∑", i));
				sum_circuit(db, &b, LitOrConst::Lit(sum.clone()))?;
				c.push(Some(sum));
				carry = if i + 1 < bits {
					let carry = new_var!(db, crate::trace::subscripted_name("c", i));
					carry_circuit(db, &b, LitOrConst::Lit(carry.clone()))?;
					Some(carry)
				} else {
					carry_circuit(db, &b, LitOrConst::Const(false))?;
					None
				};
			}
		}
	}
	for l in a.iter().skip(bits) {
		emit_clause!(db, &[l.negate()])?;
	}
	for l in b.iter().skip(bits) {
		emit_clause!(db, &[l.negate()])?;
	}
	Ok(c)
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
		cardinality_one::tests::card1_test_suite,
		helpers::tests::{assert_enc_sol, assert_sol, TestDB},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp, StaticLinEncoder,
		},
		CardinalityOne, Checker, Comparator, Encoder, LinExp, LinearConstraint, LinearEncoder,
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
}
