use crate::{
	int::{next_int_var, IntVarEnc, IntVarOrd, TernLeConstraint, TernLeEncoder},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, Result,
};
use iset::IntervalSet;

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight Counter (SWC)
#[derive(Clone, Default)]
pub struct SwcEncoder<C: Coefficient> {
	add_consistency: bool,
	cutoff: C,
}

impl<C: Coefficient> SwcEncoder<C> {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_cutoff(&mut self, c: C) -> &mut Self {
		self.cutoff = c;
		self
	}
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for SwcEncoder<C> {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "swc_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		// self.cutoff = -C::one();
		// self.add_consistency = true;
		// TODO not possible to fix since both closures use db?
		#[allow(clippy::needless_collect)]
		let xs = lin.terms
			.iter()
			.map(|part| IntVarEnc::Ord(IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone())))
			.collect::<Vec<_>>();
		let n = xs.len();
		xs.into_iter().enumerate().reduce(|(_, v), (i, x)| {
			let dom = num::iter::range_inclusive(C::one(), std::cmp::min(v.ub() + x.ub(), *lin.k))
				.map(|j| j..(j + C::one()))
				.collect::<IntervalSet<_>>();

			let next = next_int_var(
				db,
				dom,
				self.cutoff,
				self.add_consistency,
				&format!("w_{i}"),
			);

			TernLeEncoder::default()
				.encode(db, &TernLeConstraint::new(&v, &x, LimitComp::LessEq, &next))
				.unwrap();

			// If the last aux var is binary, we need to always encode consistency to limit the total sum
			if i == n - 1 && !self.add_consistency {
				if let IntVarEnc::Bin(next_bin) = &next {
					next_bin.consistent(db).unwrap();
				}
			}

			(i + 1, next)
		});
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		helpers::tests::assert_sol,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Checker, Encoder,
	};

	linear_test_suite!(SwcEncoder::default());
	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
}
