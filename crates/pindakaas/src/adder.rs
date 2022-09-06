use std::collections::HashMap;

use crate::helpers::encode_xor;
use crate::{
	ClauseDatabase, ClauseSink, Comparator, Literal, Part, PositiveCoefficient, Result,
	Unsatisfiable,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
pub fn encode_bool_lin_adder<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	db: &mut DB,
	partition: &[Part<Lit, PC>],
	cmp: Comparator,
	k: PC,
) -> Result {
	let pair = &partition
		.iter()
		.flat_map(|part| part.iter().map(|(lit, coef)| (lit.clone(), *coef)))
		.collect::<HashMap<Lit, PC>>();

	debug_assert!(cmp == Comparator::LessEq || cmp == Comparator::Equal);
	// The number of relevant bits in k
	let bits = (PC::zero().leading_zeros() - k.leading_zeros()) as usize;
	let first_zero = k.trailing_ones() as usize;
	let mut k = (0..bits)
		.map(|b| k & (PC::one() << b) != PC::zero())
		.collect::<Vec<bool>>();
	debug_assert!(k[bits - 1]);

	// Create structure with which coefficients use which bits
	let mut bucket = vec![Vec::new(); bits];
	for (i, bucker) in bucket.iter_mut().enumerate().take(bits) {
		for (lit, coef) in pair {
			if *coef & (PC::one() << i) != PC::zero() {
				bucker.push(lit.clone());
			}
		}
	}

	// Compute the sums and carries for each bit layer
	// if comp == Equal, then this is directly enforced (to avoid creating additional literals)
	// otherwise, sum literals are left in the buckets for further processing
	let mut sum = vec![None; bits];
	for b in 0..bits {
		if bucket[b].is_empty() {
			if k[b] && cmp == Comparator::Equal {
				return Err(Unsatisfiable);
			}
		} else if bucket[b].len() == 1 {
			let x = bucket[b].pop().unwrap();
			if cmp == Comparator::Equal {
				db.add_clause(&[if k[b] { x } else { x.negate() }])?
			} else {
				sum[b] = Some(x);
			}
		} else {
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
				if last && cmp == Comparator::Equal {
					// No need to create a new literal, force the sum to equal the result
					force_sum(db, lits.as_slice(), k[b])?;
				} else if cmp != Comparator::LessEq || b >= first_zero {
					// Literal is not used for the less-than constraint unless a zero has been seen first
					bucket[b].push(create_sum_lit(db, lits.as_slice())?);
				}

				// Compute carry
				if b + 1 >= bits {
					// Carry will bring the sum to be greater than k, force to be false
					if lits.len() == 2 && cmp == Comparator::Equal {
						// Already encoded by the XOR to compute the sum
					} else {
						force_carry(db, &lits[..], false)?
					}
				} else if last && cmp == Comparator::Equal && bucket[b + 1].is_empty() {
					// No need to create a new literal, force the carry to equal the result
					force_carry(db, &lits[..], k[b + 1])?;
					// Mark k[b + 1] as false (otherwise next step will fail)
					k[b + 1] = false;
				} else {
					bucket[b + 1].push(create_carry_lit(db, lits.as_slice())?);
				}
			}
			debug_assert!(
				(cmp == Comparator::Equal && bucket[b].is_empty())
					|| (cmp == Comparator::LessEq && (bucket[b].len() == 1 || b < first_zero))
			);
			sum[b] = bucket[b].pop();
		}
	}
	// In case of equality this has been enforced
	debug_assert!(cmp != Comparator::Equal || sum.iter().all(|x| x.is_none()));

	// Enforce less-than constraint
	if cmp == Comparator::LessEq {
		// For every zero bit in k:
		// - either the sum bit is also zero, or
		// - a higher sum bit is zero that was one in k.
		for i in 0..bits {
			if !k[i] && sum[i].is_some() {
				db.add_clause(
					&(i..bits)
						.filter_map(|j| if j == i || k[j] { sum[j].clone() } else { None })
						.map(|lit| lit.negate())
						.collect::<Vec<Lit>>(),
				)?;
			}
		}
	}
	Ok(())
}

/// Create a literal that represents the sum bit when adding lits together using an adder
/// circuit
///
/// Warning: Internal function expect 2 ≤ lits.len() ≤ 3
fn create_sum_lit<Lit: Literal, DB: ClauseDatabase<Lit = Lit> + ?Sized>(
	db: &mut DB,
	lits: &[Lit],
) -> Result<Lit> {
	let sum = db.new_var();
	match lits {
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
	Ok(sum)
}

/// Force circuit that represents the sum bit when adding lits together using an adder
/// circuit to take the value k
fn force_sum<Lit: Literal, DB: ClauseSink<Lit = Lit> + ?Sized>(
	db: &mut DB,
	lits: &[Lit],
	k: bool,
) -> Result {
	if k {
		encode_xor(db, lits)
	} else {
		match lits {
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
fn create_carry_lit<Lit: Literal, DB: ClauseDatabase<Lit = Lit> + ?Sized>(
	db: &mut DB,
	lits: &[Lit],
) -> Result<Lit> {
	let carry = db.new_var();
	match lits {
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
	Ok(carry)
}

/// Force the circuit that represents the carry bit when adding lits together using an adder
/// circuit to take the value k
fn force_carry<Lit: Literal, DB: ClauseSink<Lit = Lit> + ?Sized>(
	db: &mut DB,
	lits: &[Lit],
	k: bool,
) -> Result {
	match lits {
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
			let neg = |x: &Lit| if k { x.clone() } else { x.negate() };
			db.add_clause(&[neg(a), neg(b)])?;
			db.add_clause(&[neg(a), neg(c)])?;
			db.add_clause(&[neg(b), neg(c)])
		}
		_ => unreachable!(),
	}
}
