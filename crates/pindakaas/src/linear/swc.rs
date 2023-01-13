use crate::{
	int::{next_int_var, IntVarEnc, IntVarOrd, TernLeConstraint, TernLeEncoder},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, Result,
};
use iset::IntervalSet;
use itertools::Itertools;

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight Counter (SWC)
#[derive(Clone, Default)]
pub struct SwcEncoder<C: Coefficient> {
	add_consistency: bool,
	cutoff: Option<C>,
}

impl<C: Coefficient> SwcEncoder<C> {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_cutoff(&mut self, c: Option<C>) -> &mut Self {
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
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone(), format!("x_{i}")).into()
			})
			.collect::<Vec<IntVarEnc<_, _>>>();
		let n = xs.len();

		// TODO not possible to fix since both closures use db?
		#[allow(clippy::needless_collect)]
		let ys = std::iter::once(IntVarEnc::Const(C::zero()))
			.chain(
				(1..=n)
					.map(|i| {
						next_int_var(
							db,
							num::iter::range_inclusive(C::one() - *lin.k, C::zero())
								.map(|j| j..(j + C::one()))
								.collect::<IntervalSet<_>>(),
							self.cutoff,
							self.add_consistency,
							format!("y_{i}"),
						)
					})
					.take(n),
			)
			.collect::<Vec<_>>();

		ys.into_iter()
			.tuple_windows()
			.zip(xs.into_iter())
			.for_each(|((y_curr, y_next), x)| {
				// x_i + y_{i+1} <= y_i
				TernLeEncoder::default()
					.encode(
						db,
						&TernLeConstraint::new(&x, &y_next, LimitComp::LessEq, &y_curr),
					)
					.unwrap();

				// TODO If the last aux var is binary, we need to always encode consistency to limit the total sum
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
		Encoder,
	};

	linear_test_suite!(SwcEncoder::default());
	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
}
