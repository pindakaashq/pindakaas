use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
	helpers::{as_binary, emit_clause, new_var},
	int::LitOrConst,
	linear::{LimitComp, PosCoeff},
	ClauseDatabase, Coeff, Encoder, Formula, Linear, Lit, Result, TseitinEncoder, Unsatisfiable,
};

/// Encoder for the linear constraints that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct AdderEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, Linear> for AdderEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
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
		const ZERO: Coeff = 0;
		let bits = ZERO.leading_zeros() - lin.k.leading_zeros();
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
						emit_clause!(db, [if k[b] { x } else { !x }])?;
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
								carry_circuit(db, &lits[..], LitOrConst::Const(false))?;
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
			lex_leq_const(db, sum.as_slice(), lin.k, bits)?;
		}
		Ok(())
	}
}

/// Uses lexicographic constraint to constrain x:B ≦ k
#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "lex_lesseq_const", skip_all)
)]
pub(crate) fn lex_leq_const<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[Option<Lit>],
	k: PosCoeff,
	bits: usize,
) -> Result {
	let k = as_binary(k, Some(bits as u32));
	// For every zero bit in k:
	// - either the `x` bit is also zero, or
	// - a higher `x` bit is zero that was one in k.
	for i in 0..bits {
		if !k[i] && x[i].is_some() {
			emit_clause!(
				db,
				(i..bits)
					.filter_map(|j| if j == i || k[j] { x[j] } else { None })
					.map(|lit| !lit)
			)?;
		}
	}
	Ok(())
}

/// Uses lexicographic constraint to constrain x:B >= k
#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "lex_geq", skip_all)
)]
pub(crate) fn lex_geq_const<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[Option<Lit>],
	k: PosCoeff,
	bits: usize,
) -> Result {
	let k = as_binary(k, Some(bits as u32));
	for i in 0..bits {
		if k[i] && x[i].is_some() {
			emit_clause!(
				db,
				(i..bits).filter_map(|j| if j == i || !k[j] { x[j] } else { None })
			)?;
		}
	}
	Ok(())
}

/// Constrains the slice `z`, to be the result of adding `x` to `y`, all encoded using the log encoding.
///
/// TODO: Should this use the IntEncoding::Log input??
pub(crate) fn log_enc_add<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[Lit],
	y: &[Lit],
	cmp: &LimitComp,
	z: &[Lit],
) -> Result {
	log_enc_add_(
		db,
		&x.iter().copied().map(LitOrConst::from).collect_vec(),
		&y.iter().copied().map(LitOrConst::from).collect_vec(),
		cmp,
		&z.iter().copied().map(LitOrConst::from).collect_vec(),
	)
}

#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "log_enc_add", skip_all, fields(constraint = format!("{x:?} + {y:?} {cmp} {z:?}"))))]
pub(crate) fn log_enc_add_<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[LitOrConst],
	y: &[LitOrConst],
	cmp: &LimitComp,
	z: &[LitOrConst],
) -> Result {
	let n = itertools::max([x.len(), y.len(), z.len()]).unwrap();

	let bit = |x: &[LitOrConst], i: usize| -> LitOrConst {
		x.get(i).unwrap_or(&LitOrConst::Const(false)).clone()
	};

	match cmp {
		LimitComp::Equal => {
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
		LimitComp::LessEq => {
			let c = &(0..n)
				.map(|_i| LitOrConst::Lit(new_var!(db, crate::trace::subscripted_name("c", _i))))
				.chain(std::iter::once(LitOrConst::Const(true)))
				.collect_vec();

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

				// if preceding bits are equal, then x<=z
				emit_filtered_clause(db, [!bit(c, i + 1), !bit(x, i), bit(z, i)])?;
			}

			emit_filtered_clause(db, [!bit(x, n - 1), bit(z, n - 1)])?;

			Ok(())
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
#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "sum_circuit", skip_all, fields(constraint = trace_print_sum(input, &output))))]
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
		LitOrConst::Const(true) => {
			let xor = Formula::Xor(input.iter().map(|&l| Formula::Atom(l)).collect_vec());
			TseitinEncoder.encode(db, &xor)
		}
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

#[cfg(any(feature = "tracing", test))]
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
#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "carry_circuit", skip_all, fields(constraint = trace_print_carry(input, &output))))]
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

#[cfg(any(feature = "tracing", test))]
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
	use traced_test::test;

	use super::*;
	use crate::{
		cardinality::tests::card_test_suite,
		cardinality_one::tests::card1_test_suite,
		helpers::tests::{assert_checker, assert_encoding, assert_solutions, expect_file},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp, StaticLinEncoder,
		},
		solver::NextVarRange,
		Cardinality, CardinalityOne, Cnf, Comparator, Encoder, LinExp, LinearConstraint,
		LinearEncoder, PairwiseEncoder,
	};

	#[test]
	fn test_pb_encode() {
		let mut cnf = Cnf::default();
		let vars = cnf.next_var_range(4).unwrap().iter_lits().collect_vec();
		LinearEncoder::<StaticLinEncoder>::default()
			.encode(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::from_slices(&[1, 1, 1, 2], &vars),
					Comparator::LessEq,
					1,
				),
			)
			.unwrap();

		assert_encoding(&cnf, &expect_file!["linear/adder/test_pb_encode.cnf"]);
		assert_solutions(&cnf, vars, &expect_file!["linear/adder/test_pb_encode.sol"]);
	}

	#[test]
	fn test_encoders() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf
			.next_var_range(4)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		// TODO encode this if encoder does not support constraint
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![c, d],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();
		// +7*x1 +10*x2 +4*x3 +4*x4 <= 9
		LinearEncoder::<StaticLinEncoder<AdderEncoder>>::default()
			.encode(
				&mut cnf,
				&LinearConstraint::new(
					LinExp::default()
						.add_choice(&[(a, 7), (b, 10)])
						.add_choice(&[(c, 4), (d, 4)]),
					Comparator::LessEq,
					9,
				),
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vec![a, b, c, d],
			&expect_file!["linear/adder/test_encoders.sol"],
		);
	}

	linear_test_suite!(AdderEncoder::default());
	card1_test_suite!(AdderEncoder::default());
	card_test_suite!(AdderEncoder::default());
}
