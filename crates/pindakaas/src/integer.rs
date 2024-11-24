mod assignment;
mod bin;
mod con;
mod decompose;
pub(crate) mod display;
mod dom;
pub(crate) mod enc;
pub(crate) mod helpers;
mod model;
mod ord;
mod res;
mod term;
pub(crate) mod var;

pub use assignment::{Assignment, MapSol};

pub use con::{Lin, LinExp};
pub use decompose::Decompose;
pub use dom::Dom;
pub use helpers::Format;
pub use model::{Consistency, Decomposer, Model, ModelConfig};
pub use term::Term;
pub use var::{IntVar, IntVarRef};

use crate::bool_linear::PosCoeff;
use crate::helpers::as_binary;
use crate::helpers::emit_clause;
use crate::helpers::emit_filtered_clause;
use crate::helpers::new_var;
use enc::LitOrConst;

use itertools::Itertools;

use crate::{ClauseDatabase, Lit, Result};

/// Uses lexicographic constraint to constrain x:B ≦ k
#[cfg_attr(
	feature = "tracing",
	tracing::instrument(name = "lex_leq_const", skip_all, fields(constraint = format!("{x:?} <= {k}")))
)]
pub(crate) fn lex_leq_const<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[LitOrConst],
	k: PosCoeff,
	bits: usize,
) -> Result {
	// For every zero bit in k:
	// - either the `x` bit is also zero, or
	// - a higher `x` bit is zero that was one in k.
	let k = as_binary(k, Some(bits));

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
	feature = "tracing",
	tracing::instrument(name = "lex_geq_const", skip_all, fields(constraint = format!("{x:?} >= {k} over {bits} bits")))
)]
pub(crate) fn lex_geq_const<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[LitOrConst],
	k: PosCoeff,
	bits: usize,
) -> Result {
	let k = as_binary(k, Some(bits));

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

// TODO implement for given false carry
#[cfg_attr(feature = "tracing", tracing::instrument(name = "carry", skip_all, fields(constraint = format!("{xs:?} >= 2"))))]
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

#[cfg_attr(feature = "tracing", tracing::instrument(name = "xor", skip_all, fields(constraint = format!("(+) {xs:?}"))))]
fn xor<DB: ClauseDatabase>(db: &mut DB, xs: &[LitOrConst], _lbl: String) -> Result<LitOrConst> {
	let (xs, trues) = filter_fixed_sum(xs);

	let is_even = match &xs[..] {
		[] => LitOrConst::Const(false), // TODO why not `true`?
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

// TODO [?] functional version has duplication with relational version
#[cfg_attr(feature = "tracing", tracing::instrument(name = "log_enc_add", skip_all, fields(constraint = format!("[{}] + [{}] = ", xs.iter().rev().map(|x| format!("{x}")).collect_vec().join(","), ys.iter().rev().map(|x| format!("{x}")).collect_vec().join(",")))))]
pub(crate) fn log_enc_add_fn<DB: ClauseDatabase>(
	db: &mut DB,
	xs: &[LitOrConst],
	ys: &[LitOrConst],
	bits: Option<usize>,
) -> Result<Vec<LitOrConst>> {
	let max_bits = itertools::max([xs.len(), ys.len()]).unwrap() + 1;
	let bits = bits.unwrap_or(max_bits);
	let mut c = LitOrConst::Const(false);

	let zs = (0..bits)
		.map(|i| {
			let (x, y) = (bit(xs, i), bit(ys, i));
			let z = xor(db, &[x, y, c], format!("z_{}", i)); // sum
			c = carry(db, &[x, y, c], format!("c_{}", i + 1))?; // carry
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

	// TODO If lasts lits are equal, it could mean they can be truncated (at least true for 2-comp)? But then they might return unexpected number of bits in some cases. Needs thinking.
	Ok(zs)
}

fn bit(x: &[LitOrConst], i: usize) -> LitOrConst {
	*x.get(i).unwrap_or(&LitOrConst::Const(false))
}
