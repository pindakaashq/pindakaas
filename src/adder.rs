// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::helpers::encode_xor;
use crate::{
	ClauseDatabase, ClauseSink, Comparator, Literal, PositiveCoefficient, Result, Unsatisfiable,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
pub fn encode_pb_adder<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	db: &mut DB,
	pair: &[(PC, Lit)],
	comp: Comparator,
	k: PC,
) -> Result {
	// The number of relevant bits in k
	let bits = (PC::zero().count_zeros() - k.count_zeros()) as usize;
	let mut k = (0..bits)
		.map(|b| k & (PC::one() << b) != PC::zero())
		.collect::<Vec<bool>>();
	debug_assert_eq!(k[bits - 1], true);

	// Create structure with which coefficients use which bits
	let mut bucket = vec![Vec::new(); bits];
	for b in 0..bits {
		for (coef, lit) in pair {
			if *coef & (PC::one() << b) != PC::zero() {
				bucket[b].push(lit.clone());
			}
		}
	}

	// Compute the sums and carries for each bit layer
	// if comp == Equal, then this is directly enforced (to avoid creating additional literals)
	// otherwise, sum literals are left in the buckets for further processing
	let mut sum = vec![None; bits];
	for b in 0..bits {
		if bucket[b].is_empty() {
			if k[b] && comp == Comparator::Equal {
				return Err(Unsatisfiable);
			}
		} else if bucket[b].len() == 1 {
			let x = bucket[b].pop().unwrap();
			if k[b] && comp == Comparator::Equal {
				db.add_clause(&[x])?
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
				if last && comp == Comparator::Equal {
					// No need to create a new literal, force the sum to equal the result
					force_sum(db, lits.as_slice(), k[b])?;
				} else {
					bucket[b].push(create_sum_lit(db, lits.as_slice())?);
				}

				// Compute carry
				if b + 1 >= bucket.len() {
					// Carry will bring the sum to be greater than k, force to be false
					force_carry(db, &lits[..], false)?
				} else if last && comp == Comparator::Equal && bucket[b + 1].is_empty() {
					// No need to create a new literal, force the carry to equal the result
					force_carry(db, &lits[..], k[b + 1])?;
					// Mark k[b + 1] as false (otherwise next step will fail)
					k[b + 1] = false;
				} else {
					bucket[b + 1].push(create_carry_lit(db, lits.as_slice())?);
				}
			}
			debug_assert!(
				(comp == Comparator::Equal && bucket[b].is_empty())
					|| (comp == Comparator::LessEq && bucket[b].len() == 1)
			);
			sum[b] = bucket[b].pop();
		}
	}
	// In case of equality this has been enforced
	debug_assert!(comp != Comparator::Equal || sum.iter().all(|x| x.is_none()));

	// Enforce less-than constraint
	if comp == Comparator::LessEq {
		// For every zero bit in k:
		// - either the sum bit is also zero, or
		// - a higher sum bit is zero that was one in k.
		for i in 0..bits {
			if !k[i] && sum[i].is_some() {
				db.add_clause(
					&(i..bits)
						.filter_map(|j| if j == i || k[j] { sum[j].clone() } else { None })
						.map(|lit| -lit)
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
) -> std::result::Result<Lit, Unsatisfiable> {
	let sum = db.new_lit();
	match lits {
		[a, b] => {
			db.add_clause(&[-a.clone(), -b.clone(), -sum.clone()])?;
			db.add_clause(&[-a.clone(), b.clone(), sum.clone()])?;
			db.add_clause(&[a.clone(), -b.clone(), sum.clone()])?;
			db.add_clause(&[a.clone(), b.clone(), -sum.clone()])?;
		}
		[a, b, c] => {
			db.add_clause(&[a.clone(), b.clone(), c.clone(), -sum.clone()])?;
			db.add_clause(&[a.clone(), -b.clone(), -c.clone(), -sum.clone()])?;
			db.add_clause(&[-a.clone(), b.clone(), -c.clone(), -sum.clone()])?;
			db.add_clause(&[-a.clone(), -b.clone(), c.clone(), -sum.clone()])?;

			db.add_clause(&[-a.clone(), -b.clone(), -c.clone(), sum.clone()])?;
			db.add_clause(&[-a.clone(), b.clone(), c.clone(), sum.clone()])?;
			db.add_clause(&[a.clone(), -b.clone(), c.clone(), sum.clone()])?;
			db.add_clause(&[a.clone(), b.clone(), -c.clone(), sum.clone()])?;
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
				db.add_clause(&[a.clone(), -b.clone()])?;
				db.add_clause(&[-a.clone(), b.clone()])
			}
			[a, b, c] => {
				db.add_clause(&[-a.clone(), -b.clone(), -c.clone()])?;
				db.add_clause(&[-a.clone(), b.clone(), c.clone()])?;
				db.add_clause(&[a.clone(), -b.clone(), c.clone()])?;
				db.add_clause(&[a.clone(), b.clone(), -c.clone()])
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
) -> std::result::Result<Lit, Unsatisfiable> {
	let carry = db.new_lit();
	match lits {
		[a, b] => {
			db.add_clause(&[-a.clone(), -b.clone(), carry.clone()])?;
			db.add_clause(&[a.clone(), -carry.clone()])?;
			db.add_clause(&[b.clone(), -carry.clone()])?;
		}
		[a, b, c] => {
			db.add_clause(&[a.clone(), b.clone(), -carry.clone()])?;
			db.add_clause(&[a.clone(), c.clone(), -carry.clone()])?;
			db.add_clause(&[b.clone(), c.clone(), -carry.clone()])?;

			db.add_clause(&[-a.clone(), -b.clone(), carry.clone()])?;
			db.add_clause(&[-a.clone(), -c.clone(), carry.clone()])?;
			db.add_clause(&[-a.clone(), -b.clone(), carry.clone()])?;
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
				db.add_clause(&[-a.clone(), -b.clone()])
			}
		}
		[a, b, c] => {
			let neg = |x: Lit| if k { x } else { -x };
			db.add_clause(&[neg(a.clone()), neg(b.clone())])?;
			db.add_clause(&[neg(a.clone()), neg(c.clone())])?;
			db.add_clause(&[neg(b.clone()), neg(c.clone())])
		}
		_ => unreachable!(),
	}
}
