use itertools::Itertools;
use rustc_hash::FxHashMap;

use super::PosCoeff;
use crate::{
	helpers::{as_binary, XorConstraint, XorEncoder},
	int::LitOrConst,
	linear::LimitComp,
	trace::{emit_clause, new_var},
	ClauseDatabase, Coeff, Comparator, Encoder, Linear, Lit, Result, Unsatisfiable,
};

/// Encoder for the linear constraints that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
#[derive(Default)]
pub struct AdderEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, Linear> for AdderEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "adder_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut DB, lin: &Linear) -> Result {
		let pair = &lin
			.terms
			.iter()
			.flat_map(|part| part.iter().map(|&(lit, coef)| (lit, coef)))
			.collect::<FxHashMap<_, _>>();

		debug_assert!(lin.cmp == LimitComp::LessEq || lin.cmp == LimitComp::Equal);
		// The number of relevant bits in k
		let bits = Coeff::from(0).leading_zeros() - lin.k.leading_zeros();
		let mut k = as_binary(lin.k, Some(bits));

		let first_zero = lin.k.trailing_ones() as usize;
		let bits = bits as usize;
		debug_assert!(k[bits - 1]);

		// Create structure with which coefficients use which bits
		let mut bucket = vec![Vec::new(); bits];
		for (i, bucket) in bucket.iter_mut().enumerate().take(bits) {
			for (lit, coef) in pair {
				if **coef & (1 << i) != 0 {
					bucket.push(*lit);
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
						emit_clause!(db, [if k[b] { x } else { !x }])?
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
							sum_circuit(db, lits.as_slice(), LitOrConst::Lit(sum))?;
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
							carry_circuit(db, lits.as_slice(), LitOrConst::Lit(carry))?;
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
				lin.k,
				bits as u32,
			)?;
		}
		Ok(())
	}
}

/// Uses lexicographic constraint to constrain x:B ≦ k
#[cfg_attr(
	feature = "trace",
	tracing::instrument(name = "lex_leq_const", skip_all, fields(constraint = format!("{x:?} <= {k}")))
)]
pub(crate) fn lex_leq_const<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[LitOrConst],
	k: PosCoeff,
	bits: u32,
) -> Result {
	// For every zero bit in k:
	// - either the `x` bit is also zero, or
	// - a higher `x` bit is zero that was one in k.
	let k = as_binary(k, Some(bits));
	let bits = bits as usize;

	(0..bits)
		.filter(|i| !k.get(*i).unwrap_or(&false))
		.try_for_each(|i| {
			emit_filtered_clause(
				db,
				(i..bits)
					.filter(|j| (*j == i || *k.get(*j).unwrap_or(&false)))
					.map(|j| !x[j])
					.collect_vec(),
			)
		})
}

/// Uses lexicographic constraint to constrain x:B >= k
#[cfg_attr(
	feature = "trace",
	tracing::instrument(name = "lex_geq_const", skip_all, fields(constraint = format!("{x:?} >= {k} over {bits} bits")))
)]
pub(crate) fn lex_geq_const<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[LitOrConst],
	k: PosCoeff,
	bits: u32,
) -> Result {
	let k = as_binary(k, Some(bits));
	let bits = bits as usize;

	(0..bits)
		.filter(|i| *k.get(*i).unwrap_or(&false))
		.try_for_each(|i| {
			emit_filtered_clause(
				db,
				(i..bits)
					.filter(|j| (*j == i || !k.get(*j).unwrap_or(&false)))
					.map(|j| x[j])
					.collect_vec(),
			)
		})
}

// TODO Implement Mul/Add for Lit (once merged with new Lit struct)

#[cfg_attr(feature = "trace", tracing::instrument(name = "carry", skip_all, fields(constraint = format!("{xs:?} >= 2"))))]
fn carry<DB: ClauseDatabase>(db: &mut DB, xs: &[LitOrConst], _lbl: String) -> Result<LitOrConst> {
	// The carry is true iff at least 2 out of 3 `xs` are true
	let (xs, trues) = filter_fixed_sum(xs);
	let carry = match &xs[..] {
		[] => (trues >= 2).into(), // trues is {0,1,2,3}
		[x] => match trues {
			0 => false.into(),
			1 => (*x).into(),
			2 => true.into(),
			_ => unreachable!(),
		},
		[x, y] => match trues {
			0 => {
				let and = new_var!(db, _lbl);
				emit_clause!(db, [!x, !y, and])?;
				emit_clause!(db, [*x, !and])?;
				emit_clause!(db, [*y, !and])?;
				and.into()
			}
			1 => {
				let or = new_var!(db, _lbl);
				emit_clause!(db, [*x, *y, !or])?;
				emit_clause!(db, [!x, or])?;
				emit_clause!(db, [!y, or])?;
				or.into()
			}
			_ => unreachable!(),
		},
		[x, y, z] => {
			assert!(trues == 0);
			let carry = new_var!(db, _lbl);

			emit_clause!(db, [*x, *y, !carry])?; // 2 false -> ~carry
			emit_clause!(db, [*x, *z, !carry])?; // " ..
			emit_clause!(db, [*y, *z, !carry])?;

			emit_clause!(db, [!x, !y, carry])?; // 2 true -> carry
			emit_clause!(db, [!x, !z, carry])?; // " ..
			emit_clause!(db, [!y, !z, carry])?;
			carry.into()
		}
		_ => unreachable!(),
	};
	Ok(carry)
}

fn filter_fixed_sum(xs: &[LitOrConst]) -> (Vec<Lit>, usize) {
	let mut trues = 0;
	(
		xs.iter()
			.filter_map(|x| match x {
				LitOrConst::Lit(l) => Some(*l),
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

#[cfg_attr(feature = "trace", tracing::instrument(name = "xor", skip_all, fields(constraint = format!("(+) {xs:?}"))))]
fn xor<DB: ClauseDatabase>(db: &mut DB, xs: &[LitOrConst], _lbl: String) -> Result<LitOrConst> {
	let (xs, trues) = filter_fixed_sum(xs);

	let is_even = match &xs[..] {
		[] => LitOrConst::Const(false), // TODO ?? why not `true`?
		[x] => LitOrConst::Lit(*x),
		[x, y] => {
			assert!(trues <= 1);
			let is_even = new_var!(db, _lbl);

			emit_clause!(db, [*x, *y, !is_even])?; // 0
			emit_clause!(db, [!x, !y, !is_even])?; // 2

			emit_clause!(db, [!x, *y, is_even])?; // 1
			emit_clause!(db, [*x, !y, is_even])?; // 1
			LitOrConst::Lit(is_even)
		}
		[x, y, z] => {
			assert!(trues == 0);
			let is_even = new_var!(db, _lbl);

			emit_clause!(db, [*x, *y, *z, !is_even])?; // 0
			emit_clause!(db, [*x, !y, !z, !is_even])?; // 2
			emit_clause!(db, [!x, *y, !z, !is_even])?; // 2
			emit_clause!(db, [!x, !y, *z, !is_even])?; // 2

			emit_clause!(db, [!x, !y, !z, is_even])?; // 3
			emit_clause!(db, [!x, *y, *z, is_even])?; // 1
			emit_clause!(db, [*x, !y, *z, is_even])?; // 1
			emit_clause!(db, [*x, *y, !z, is_even])?; // 1
			LitOrConst::Lit(is_even)
		}
		_ => unimplemented!(),
	};

	// If trues is odd, negate sum
	Ok(if trues % 2 == 0 { is_even } else { !is_even })
}

#[cfg_attr(feature = "trace", tracing::instrument(name = "log_enc_add", skip_all, fields(constraint = format!("[{c}] + [{}] + [{}] {cmp}", xs.iter().rev().map(|x| format!("{x}")).collect_vec().join(","), ys.iter().rev().map(|x| format!("{x}")).collect_vec().join(",")))))]
pub(crate) fn log_enc_add_fn<DB: ClauseDatabase>(
	db: &mut DB,
	xs: &[LitOrConst],
	ys: &[LitOrConst],
	cmp: &Comparator,
	mut c: LitOrConst,
	bits: Option<u32>,
) -> Result<Vec<LitOrConst>> {
	assert!(cmp == &Comparator::Equal);
	let max_bits = itertools::max([xs.len(), ys.len()]).unwrap() + 1;
	let bits = bits.unwrap_or(max_bits as u32) as usize;

	let zs = (0..bits)
		.map(|i| {
			let (x, y) = (bit(xs, i), bit(ys, i));
			let z = xor(db, &[x, y, c], format!("z_{}", i));
			c = carry(db, &[x, y, c], format!("c_{}", i + 1))?;
			z
		})
		.collect::<Result<Vec<_>>>()?;

	// TODO avoid c being created by constraining (x+y+c >= 2 ) <-> false in last iteration if bits<max_bits
	// prevent overflow;
	// TODO this should just happen for all c_i's for bits < i <= max_bits
	if bits < max_bits {
		if let LitOrConst::Lit(c) = c {
			emit_clause!(db, [!c])?;
		}
	}

	// TODO Check if last bits are equal? But then might return unexpected number of bits
	Ok(zs)
}

fn bit(x: &[LitOrConst], i: usize) -> LitOrConst {
	*x.get(i).unwrap_or(&LitOrConst::Const(false))
}

#[cfg_attr(feature = "trace", tracing::instrument(name = "log_enc_add", skip_all, fields(constraint = format!("{x:?} + {y:?} {cmp} {z:?}"))))]
pub(crate) fn log_enc_add_<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[LitOrConst],
	y: &[LitOrConst],
	cmp: &Comparator,
	z: &[LitOrConst],
) -> Result {
	let n = itertools::max([x.len(), y.len(), z.len()]).unwrap();
	let bit = |x: &[LitOrConst], i: usize| -> LitOrConst {
		*x.get(i).unwrap_or(&LitOrConst::Const(false))
	};

	match cmp {
		Comparator::Equal => {
			let c = &std::iter::once(LitOrConst::Const(false))
				.chain((1..n).map(|_i| {
					LitOrConst::Lit(new_var!(db, crate::trace::subscripted_name("c", _i)))
				}))
				.collect_vec();
			for i in 0..n {
				// sum circuit
				emit_filtered_clause(db, [bit(x, i), bit(y, i), bit(c, i), !bit(z, i)])?;
				emit_filtered_clause(db, [bit(x, i), !bit(y, i), !bit(c, i), !bit(z, i)])?;
				emit_filtered_clause(db, [!bit(x, i), bit(y, i), !bit(c, i), !bit(z, i)])?;
				emit_filtered_clause(db, [!bit(x, i), !bit(y, i), bit(c, i), !bit(z, i)])?;

				emit_filtered_clause(db, [!bit(x, i), !bit(y, i), !bit(c, i), bit(z, i)])?;
				emit_filtered_clause(db, [!bit(x, i), bit(y, i), bit(c, i), bit(z, i)])?;
				emit_filtered_clause(db, [bit(x, i), !bit(y, i), bit(c, i), bit(z, i)])?;
				emit_filtered_clause(db, [bit(x, i), bit(y, i), !bit(c, i), bit(z, i)])?;

				// carry circuit
				emit_filtered_clause(db, [bit(x, i), bit(y, i), !bit(c, i + 1)])?;
				emit_filtered_clause(db, [bit(x, i), bit(c, i), !bit(c, i + 1)])?;
				emit_filtered_clause(db, [bit(y, i), bit(c, i), !bit(c, i + 1)])?;
				emit_filtered_clause(db, [!bit(x, i), !bit(y, i), bit(c, i + 1)])?;
				emit_filtered_clause(db, [!bit(x, i), !bit(c, i), bit(c, i + 1)])?;
				emit_filtered_clause(db, [!bit(y, i), !bit(c, i), bit(c, i + 1)])?;
			}
			Ok(())
		}
		_ => {
			todo!("Removed log_enc_add inequality; based on 2-comp");
			/*
			let c = &(0..n)
				.map(|_i| LitOrConst::Lit(new_var!(db, crate::trace::subscripted_name("c", _i))))
				.chain(std::iter::once(LitOrConst::Const(true)))
				.collect_vec();

			// Ensure z/x have same length
			// let x = &sign_extend(x, LitOrConst::Const(false), n);
			// let z = &sign_extend(z, LitOrConst::Const(false), n);
			let x = &sign_extend(x, !(x.last().unwrap().clone()), n);
			let z = &sign_extend(z, !(z.last().unwrap().clone()), n);

			assert!(
				y.iter().all(|yi| matches!(yi, LitOrConst::Const(false))),
				"Expected {y:?} to be zero for x<=z lex comparison"
			);

			// higher i -> more significant
			for i in 0..n {
				// c = all more significant bits are equal AND current one is
				// if up to i is equal, all preceding must be equal
				emit_filtered_clause(db, [!bit(c, i), bit(c, i + 1)])?;
				// if up to i is equal, x<->z
				emit_filtered_clause(db, [!bit(c, i), !bit(x, i), bit(z, i)])?;
				emit_filtered_clause(db, [!bit(c, i), !bit(z, i), bit(x, i)])?;

				// if not up to i is equal, either preceding bit was not equal, or x!=z
				emit_filtered_clause(db, [bit(c, i), !bit(c, i + 1), bit(x, i), bit(z, i)])?;
				emit_filtered_clause(db, [bit(c, i), !bit(c, i + 1), !bit(x, i), !bit(z, i)])?;

				// if preceding bits are equal, then x<=z (or x>=z)
				match ineq {
					Comparator::LessEq => {
						emit_filtered_clause(db, [!bit(c, i + 1), !bit(x, i), bit(z, i)])
					}
					Comparator::GreaterEq => {
						emit_filtered_clause(db, [!bit(c, i + 1), bit(x, i), !bit(z, i)])
					}
					Comparator::Equal => unreachable!(),
				}?;
			}

			Ok(())
			*/
		}
	}
}

fn emit_filtered_clause<DB: ClauseDatabase, I: IntoIterator<Item = LitOrConst>>(
	db: &mut DB,
	lits: I,
) -> Result {
	if let Ok(clause) = lits
		.into_iter()
		.filter_map(|lit| match lit {
			LitOrConst::Lit(lit) => Some(Ok(lit)),
			LitOrConst::Const(true) => Some(Err(())), // clause satisfied
			LitOrConst::Const(false) => None,         // literal falsified
		})
		.collect::<std::result::Result<Vec<_>, ()>>()
	{
		emit_clause!(db, clause)
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
fn sum_circuit<DB: ClauseDatabase>(db: &mut DB, input: &[Lit], output: LitOrConst) -> Result {
	match output {
		LitOrConst::Lit(sum) => match *input {
			[a, b] => {
				emit_clause!(db, [!a, !b, !sum])?;
				emit_clause!(db, [!a, b, sum])?;
				emit_clause!(db, [a, !b, sum])?;
				emit_clause!(db, [a, b, !sum])
			}
			[a, b, c] => {
				emit_clause!(db, [a, b, c, !sum])?;
				emit_clause!(db, [a, !b, !c, !sum])?;
				emit_clause!(db, [!a, b, !c, !sum])?;
				emit_clause!(db, [!a, !b, c, !sum])?;

				emit_clause!(db, [!a, !b, !c, sum])?;
				emit_clause!(db, [!a, b, c, sum])?;
				emit_clause!(db, [a, !b, c, sum])?;
				emit_clause!(db, [a, b, !c, sum])
			}
			_ => unreachable!(),
		},
		LitOrConst::Const(true) => XorEncoder::default().encode(db, &XorConstraint::new(input)),
		LitOrConst::Const(false) => match *input {
			[a, b] => {
				emit_clause!(db, [a, !b])?;
				emit_clause!(db, [!a, b])
			}
			[a, b, c] => {
				emit_clause!(db, [!a, !b, !c])?;
				emit_clause!(db, [!a, b, c])?;
				emit_clause!(db, [a, !b, c])?;
				emit_clause!(db, [a, b, !c])
			}
			_ => unreachable!(),
		},
	}
}

#[cfg(feature = "trace")]
fn trace_print_sum(input: &[Lit], output: &LitOrConst) -> String {
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
fn carry_circuit<DB: ClauseDatabase>(db: &mut DB, input: &[Lit], output: LitOrConst) -> Result {
	match output {
		LitOrConst::Lit(carry) => match *input {
			[a, b] => {
				emit_clause!(db, [!a, !b, carry])?;
				emit_clause!(db, [a, !carry])?;
				emit_clause!(db, [b, !carry])
			}
			[a, b, c] => {
				emit_clause!(db, [a, b, !carry])?;
				emit_clause!(db, [a, c, !carry])?;
				emit_clause!(db, [b, c, !carry])?;

				emit_clause!(db, [!a, !b, carry])?;
				emit_clause!(db, [!a, !c, carry])?;
				emit_clause!(db, [!b, !c, carry])
			}
			_ => unreachable!(),
		},
		LitOrConst::Const(k) => match *input {
			[a, b] => {
				if k {
					// TODO: Can we avoid this?
					emit_clause!(db, [a])?;
					emit_clause!(db, [b])
				} else {
					emit_clause!(db, [!a, !b])
				}
			}
			[a, b, c] => {
				let neg = |x: Lit| if k { x } else { !x };
				emit_clause!(db, [neg(a), neg(b)])?;
				emit_clause!(db, [neg(a), neg(c)])?;
				emit_clause!(db, [neg(b), neg(c)])
			}
			_ => unreachable!(),
		},
	}
}

#[cfg(feature = "trace")]
fn trace_print_carry(input: &[Lit], output: &LitOrConst) -> String {
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
		helpers::tests::{assert_enc_sol, assert_sol, lits, TestDB},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp, StaticLinEncoder,
		},
		Cardinality, CardinalityOne, Comparator, Encoder, LinExp, LinearConstraint, LinearEncoder,
		PairwiseEncoder,
	};

	// TODO deprecated for log_enc_add inequality
	// #[test]
	fn _test_lex_geq() {
		let mut db = TestDB::new(5);
		let x = &[
			LitOrConst::from(Lit::from(db.new_var())),
			LitOrConst::from(Lit::from(db.new_var())),
			LitOrConst::from(false),
		];
		let y = &[LitOrConst::from(false)];
		let z = &[
			LitOrConst::from(Lit::from(db.new_var())),
			LitOrConst::from(Lit::from(db.new_var())),
			LitOrConst::from(Lit::from(db.new_var())),
		];
		log_enc_add_(&mut db, x, y, &Comparator::GreaterEq, z).unwrap();
	}

	#[test]
	fn test_pb_encode() {
		assert_enc_sol!(
			LinearEncoder::<StaticLinEncoder>::default(),
			4,
			&LinearConstraint::new(
				LinExp::from_slices(&[1,1,1,2], &lits![1,2,3,4]),
				Comparator::LessEq,
				1
			)
			=>
			vec![
				lits![-4], lits![-3, -1], lits![-2, -1], lits![-3, -2]
			],
			vec![
				lits![-1, -2, -3, -4],
				lits![-1, -2, 3, -4],
				lits![-1, 2, -3, -4],
				lits![1, -2, -3, -4],
			]
		);
	}

	#[test]
	fn test_encoders() {
		// +7*x1 +10*x2 +4*x3 +4*x4 <= 9
		let mut db = TestDB::new(4).expect_solutions(vec![
			lits![-1, -2, -3, -4],
			lits![1, -2, -3, -4],
			lits![-1, -2, 3, -4],
			lits![-1, -2, -3, 4],
		]);
		// TODO encode this if encoder does not support constraint
		assert!(PairwiseEncoder::default()
			.encode(
				&mut db,
				&CardinalityOne {
					lits: lits![1, 2],
					cmp: LimitComp::LessEq
				}
			)
			.is_ok());
		assert!(PairwiseEncoder::default()
			.encode(
				&mut db,
				&CardinalityOne {
					lits: lits![3, 4],
					cmp: LimitComp::LessEq
				}
			)
			.is_ok());
		assert!(LinearEncoder::<StaticLinEncoder<AdderEncoder>>::default()
			.encode(
				&mut db,
				&LinearConstraint::new(
					LinExp::default()
						.add_choice(&[(1.into(), 7), (2.into(), 10)])
						.add_choice(&[(3.into(), 4), (4.into(), 4)]),
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
