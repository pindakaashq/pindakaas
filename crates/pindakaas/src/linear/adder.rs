use std::collections::HashMap;

use crate::{
	helpers::{XorConstraint, XorEncoder},
	linear::{LimitComp, PosCoeff},
	new_var, ClauseDatabase, Coefficient, Encoder, Linear, Literal, Result, Unsatisfiable,
};

/// Encoder for the linear constraints that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
#[derive(Default)]
pub struct AdderEncoder {}

fn to_bin<C: Coefficient>(k: PosCoeff<C>, bits: usize) -> Vec<bool> {
	(0..bits)
		.map(|b| *k & (C::one() << b) != C::zero())
		.collect::<Vec<_>>()
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for AdderEncoder {
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		let pair = &lin
			.terms
			.iter()
			.flat_map(|part| part.iter().map(|(lit, coef)| (lit.clone(), **coef)))
			.collect::<HashMap<DB::Lit, C>>();

		debug_assert!(lin.cmp == LimitComp::LessEq || lin.cmp == LimitComp::Equal);
		// The number of relevant bits in k
		let bits = (C::zero().leading_zeros() - lin.k.leading_zeros()) as usize;
		let first_zero = lin.k.trailing_ones() as usize;
		let mut k = to_bin(lin.k.clone(), bits);
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
						db.add_clause(&[if k[b] { x } else { x.negate() }])?
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
							force_sum(db, &XorConstraint::new(&lits), k[b])?;
						} else if lin.cmp != LimitComp::LessEq || !last || b >= first_zero {
							// Literal is not used for the less-than constraint unless a zero has been seen first
							let sum = db.new_var();
							create_sum_lit(db, lits.as_slice(), &sum)?;
							bucket[b].push(sum);
						}

						// Compute carry
						if b + 1 >= bits {
							// Carry will bring the sum to be greater than k, force to be false
							if lits.len() == 2 && lin.cmp == LimitComp::Equal {
								// Already encoded by the XOR to compute the sum
							} else {
								force_carry(db, &lits[..], false)?
							}
						} else if last && lin.cmp == LimitComp::Equal && bucket[b + 1].is_empty() {
							// No need to create a new literal, force the carry to equal the result
							force_carry(db, &lits[..], k[b + 1])?;
							// Mark k[b + 1] as false (otherwise next step will fail)
							k[b + 1] = false;
						} else {
							let carry = db.new_var();
							create_carry_lit(db, lits.as_slice(), &carry)?;
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
			x_bin_le(db, sum.as_slice(), lin.k.clone(), bits)?;
		}
		Ok(())
	}
}

/// Uses lexicographic constraint to constrain x:B ≦ k
pub(crate) fn x_bin_le<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	x: &[Option<DB::Lit>],
	k: PosCoeff<C>,
	bits: usize,
) -> Result {
	let k = to_bin(k, bits);
	// For every zero bit in k:
	// - either the `x` bit is also zero, or
	// - a higher `x` bit is zero that was one in k.
	for i in 0..bits {
		if !k[i] && x[i].is_some() {
			db.add_clause(
				&(i..bits)
					.filter_map(|j| if j == i || k[j] { x[j].clone() } else { None })
					.map(|lit| lit.negate())
					.collect::<Vec<DB::Lit>>(),
			)?;
		}
	}
	Ok(())
}

/// Constrains the result, `c`, of adding `a` to `b`, all encoded using the log encoding.
///
/// TODO: Should this use the IntEncoding::Log input??
pub(crate) fn log_enc_add<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[DB::Lit],
	y: &[DB::Lit],
	z: &[DB::Lit],
	bits: usize,
) -> Result {
	let mut carry = None;
	for i in 0..bits {
		let sum = z.get(i).unwrap();
		let b = [x.get(i), y.get(i), carry.as_ref()]
			.into_iter()
			.flatten()
			.cloned()
			.collect::<Vec<DB::Lit>>();
		debug_assert!(b.len() <= 3);
		create_sum_lit(db, &b, sum)?;
		if i + 1 < bits {
			let c = new_var!(db, format!("c_{i}"));
			create_carry_lit(db, &b, &c)?;
			carry = Some(c);
		} else {
			force_carry(db, &b, false)?;
		}
	}
	for l in x.iter().skip(bits) {
		db.add_clause(&[l.negate()])?;
	}
	for l in y.iter().skip(bits) {
		db.add_clause(&[l.negate()])?;
	}
	Ok(())
}

/// Create a literal that represents the sum bit when adding lits together using an adder
/// circuit
///
/// Warning: Internal function expect 2 ≤ lits.len() ≤ 3
fn create_sum_lit<DB: ClauseDatabase>(db: &mut DB, lits: &[DB::Lit], sum: &DB::Lit) -> Result {
	#[cfg(debug_assertions)]
	println!(
		"Encode sum of {} as {}",
		lits.iter()
			.map(|l| db.to_label(l))
			.collect::<Vec<_>>()
			.join(", "),
		db.to_label(sum)
	);
	match lits {
		[a] => {
			db.add_clause(&[a.negate(), sum.clone()])?;
			db.add_clause(&[a.clone(), sum.negate()])?;
		}
		[a, b] => {
			db.add_clause(&[a.negate(), b.negate(), sum.negate()])?;
			db.add_clause(&[a.negate(), b.clone(), sum.clone()])?;
			db.add_clause(&[a.clone(), b.negate(), sum.clone()])?;
			db.add_clause(&[a.clone(), b.clone(), sum.negate()])?;
		}
		[a, b, c] => {
			db.add_clause(&[a.clone(), b.clone(), c.clone(), sum.negate()])?;
			db.add_clause(&[a.clone(), b.negate(), c.negate(), sum.negate()])?;
			db.add_clause(&[a.negate(), b.clone(), c.negate(), sum.negate()])?;
			db.add_clause(&[a.negate(), b.negate(), c.clone(), sum.negate()])?;

			db.add_clause(&[a.negate(), b.negate(), c.negate(), sum.clone()])?;
			db.add_clause(&[a.negate(), b.clone(), c.clone(), sum.clone()])?;
			db.add_clause(&[a.clone(), b.negate(), c.clone(), sum.clone()])?;
			db.add_clause(&[a.clone(), b.clone(), c.negate(), sum.clone()])?;
		}
		_ => unreachable!(),
	}
	Ok(())
}

/// Force circuit that represents the sum bit when adding lits together using an adder
/// circuit to take the value k
fn force_sum<DB: ClauseDatabase>(db: &mut DB, xor: &XorConstraint<DB::Lit>, k: bool) -> Result {
	if k {
		XorEncoder::default().encode(db, xor)
	} else {
		match xor.lits {
			[a, b] => {
				db.add_clause(&[a.clone(), b.negate()])?;
				db.add_clause(&[a.negate(), b.clone()])
			}
			[a, b, c] => {
				db.add_clause(&[a.negate(), b.negate(), c.negate()])?;
				db.add_clause(&[a.negate(), b.clone(), c.clone()])?;
				db.add_clause(&[a.clone(), b.negate(), c.clone()])?;
				db.add_clause(&[a.clone(), b.clone(), c.negate()])
			}
			_ => unreachable!(),
		}
	}
}

/// Create a literal that represents the carry bit when adding lits together using an adder
/// circuit
///
/// Warning: Internal function expect 2 ≤ lits.len() ≤ 3
fn create_carry_lit<DB: ClauseDatabase>(db: &mut DB, lits: &[DB::Lit], carry: &DB::Lit) -> Result {
	#[cfg(debug_assertions)]
	println!(
		"Encode carry of {} as {}",
		lits.iter()
			.map(|l| db.to_label(l))
			.collect::<Vec<_>>()
			.join(", "),
		db.to_label(carry)
	);
	match lits {
		[_] => {
			db.add_clause(&[carry.negate()])?;
		}
		[a, b] => {
			db.add_clause(&[a.negate(), b.negate(), carry.clone()])?;
			db.add_clause(&[a.clone(), carry.negate()])?;
			db.add_clause(&[b.clone(), carry.negate()])?;
		}
		[a, b, c] => {
			db.add_clause(&[a.clone(), b.clone(), carry.negate()])?;
			db.add_clause(&[a.clone(), c.clone(), carry.negate()])?;
			db.add_clause(&[b.clone(), c.clone(), carry.negate()])?;

			db.add_clause(&[a.negate(), b.negate(), carry.clone()])?;
			db.add_clause(&[a.negate(), c.negate(), carry.clone()])?;
			db.add_clause(&[b.negate(), c.negate(), carry.clone()])?;
		}
		_ => unreachable!(),
	}
	Ok(())
}

/// Force the circuit that represents the carry bit when adding lits together using an adder
/// circuit to take the value k
fn force_carry<DB: ClauseDatabase>(db: &mut DB, lits: &[DB::Lit], k: bool) -> Result {
	match lits {
		[_] => {
			if k {
				Err(Unsatisfiable)
			} else {
				Ok(())
			}
		}
		[a, b] => {
			if k {
				// TODO: Can we avoid this?
				db.add_clause(&[a.clone()])?;
				db.add_clause(&[b.clone()])
			} else {
				db.add_clause(&[a.negate(), b.negate()])
			}
		}
		[a, b, c] => {
			let neg = |x: &DB::Lit| if k { x.clone() } else { x.negate() };
			db.add_clause(&[neg(a), neg(b)])?;
			db.add_clause(&[neg(a), neg(c)])?;
			db.add_clause(&[neg(b), neg(c)])
		}
		_ => unreachable!(),
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		cardinality_one::tests::card1_test_suite,
		helpers::tests::assert_sol,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		CardinalityOne, Checker, Encoder,
	};
	linear_test_suite!(AdderEncoder::default());
	card1_test_suite!(AdderEncoder::default());
}
