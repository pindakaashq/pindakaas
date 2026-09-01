//! Encoding a linear constraint as the circuit that adds its terms up.
//!
//! The literals are bucketed by which bit of their coefficient they set, and
//! each bucket compressed three at a time by full adders. Also holds the sum
//! and carry circuits themselves, which the integer encoders build on.

use std::cmp::max;

use itertools::Itertools;

use crate::{
	constraint::{
		bool_linear::{LimitComp, PosCoeff},
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		int_linear::NormalizedIntLinear,
		propositional_logic::{Formula, TseitinEncoder},
	},
	decision::integer::lex_leq_const,
	helpers::{as_binary, bit, new_named_lit},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Result, Unsatisfiable,
};

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// Encoder for the linear constraints that ∑ coeffᵢ·litᵢ ≷ k using a binary
/// adders circuits
pub struct AdderEncoder {}

/// Above this many literals, enumerating the assignments of the wrong parity
/// costs more clauses than a Tseitin transformation costs auxiliary variables.
const DIRECT_PARITY_LITS: usize = 4;

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
				// carry = x ∧ y
				db.add_clause([!x, !y, carry])?;
				db.add_clause([x, !carry])?;
				db.add_clause([y, !carry])?;
			}
			[x, y] => {
				debug_assert_eq!(trues, 1);
				// carry = x ∨ y
				db.add_clause([x, y, !carry])?;
				db.add_clause([!x, carry])?;
				db.add_clause([!y, carry])?;
			}
			[x, y, z] => {
				debug_assert_eq!(trues, 0);
				// Two false inputs force no carry, two true inputs force one.
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
		// A given sum may be wider than the inputs can reach, and its top bits
		// still have to be driven to zero rather than left free.
		let max_bits = max(max(xs.len(), ys.len()) + 1, zs.map_or(0, <[_]>::len));
		let bits = bits.unwrap_or(max_bits);
		let mut c = BoolVal::Const(false);
		(0..max_bits)
			.map(|i| {
				let (x, y) = (bit(xs, i), bit(ys, i));
				let z = match zs {
					// Relational: the sum bit is given, so constrain it.
					Some(zs) => Some(bit(zs, i)),
					// Functional: create a bit, unless it is past the requested
					// width and therefore has to be zero.
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
		// Forbid every assignment of the wrong parity. That is `2ⁿ⁻¹` clauses
		// and no auxiliary variables, which beats Tseitin at adder widths.
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
		// Adding bit by bit has no use for how the terms are grouped, so the
		// constraint is weighed back out into the literals standing for it.
		let (weighed, constant) = con.as_weighted(db)?;
		let rhs = con.k() - constant;
		if rhs < 0 {
			return db.contradiction();
		}
		if rhs == 0 {
			// Every coefficient is positive, so a sum of zero is every literal
			// being false, whichever way it is compared.
			return weighed
				.into_iter()
				.try_for_each(|(lit, _)| db.add_clause([!lit]));
		}
		let rhs = PosCoeff::new(rhs);

		// The number of relevant bits in k
		const ZERO: Coeff = 0;
		let bits = ZERO.leading_zeros() - rhs.leading_zeros();
		let mut k = as_binary(rhs, Some(bits));

		let first_zero = rhs.trailing_ones() as usize;
		let bits = bits as usize;
		debug_assert!(k[bits - 1]);

		let all_terms = || {
			weighed
				.iter()
				.map(|&(lit, coef)| (lit, PosCoeff::new(coef)))
		};

		// Create structure with which coefficients use which bits
		let mut bucket = vec![Vec::new(); bits];
		for (i, bucket) in bucket.iter_mut().enumerate().take(bits) {
			for (lit, coef) in all_terms() {
				if *coef & (1 << i) != 0 {
					bucket.push(lit);
				}
			}
		}

		// Compute the sums and carries for each bit layer
		// if comp == Equal, then this is directly enforced (to avoid creating
		// additional literals) otherwise, sum literals are left in the buckets
		// for further processing
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

						// Compute sum
						if last && cmp == LimitComp::Equal {
							// No need to create a new literal, force the sum to
							// equal the result
							let _ = Self::sum_circuit(
								db,
								&lits,
								Some(BoolVal::Const(k[b])),
								String::new(),
							)?;
						} else if cmp != LimitComp::LessEq || !last || b >= first_zero {
							// Literal is not used for the less-than constraint
							// unless a zero has been seen first
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

						// Compute carry
						if b + 1 >= bits {
							// Carry will bring the sum to be greater than k,
							// force to be false
							if lits.len() == 2 && cmp == LimitComp::Equal {
								// Already encoded by the XOR to compute the sum
							} else {
								let _ = Self::carry_circuit(
									db,
									&lits,
									Some(BoolVal::Const(false)),
									String::new(),
								)?;
							}
						} else if last && cmp == LimitComp::Equal && bucket[b + 1].is_empty() {
							// No need to create a new literal, force the carry
							// to equal the result
							let _ = Self::carry_circuit(
								db,
								&lits,
								Some(BoolVal::Const(k[b + 1])),
								String::new(),
							)?;
							// Mark k[b + 1] as false (otherwise next step will
							// fail)
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
		// In case of equality this has been enforced
		debug_assert!(cmp != LimitComp::Equal || sum.iter().all(|x| x.is_none()));

		// Enforce less-than constraint
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
	use traced_test::test;

	use crate::helpers::tests::{linear_test_suite, prelude::*};

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
			// The sum is wide enough to never overflow, so every assignment of
			// the inputs extends to exactly one model.
			assert_eq!(solutions.len(), 1 << (x_bits + y_bits));
			for s in &solutions {
				assert_eq!(s[2], s[0] + s[1], "{} + {} != {}", s[0], s[1], s[2]);
			}
		}
	}

	#[test]
	fn ripple_carry_adder_handles_fixed_bits() {
		// Shifting and grounding a binary encoding leaves constant bits in it,
		// so the adder has to fold them into the sum and the carry rather than
		// assume every bit is a literal.
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
