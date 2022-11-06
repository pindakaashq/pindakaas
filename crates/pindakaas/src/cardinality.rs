use crate::{
	linear::{LimitComp, LinMarker, Linear, PosCoeff},
	CardinalityOne, Checker, ClauseDatabase, Coefficient, Encoder, Literal,
};

#[derive(Clone, Debug)]
pub struct Cardinality<Lit: Literal, C: Coefficient> {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff<C>,
}

impl<Lit: Literal, C: Coefficient> From<CardinalityOne<Lit>> for Cardinality<Lit, C> {
	fn from(card1: CardinalityOne<Lit>) -> Self {
		Self {
			lits: card1.lits,
			cmp: card1.cmp,
			k: C::one().into(),
		}
	}
}

impl<Lit: Literal, C: Coefficient> Cardinality<Lit, C> {
	#[cfg(feature = "trace")]
	#[allow(dead_code)] // FIXME: Remove when used
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(self.lits.iter().map(trace_print_lit), " + ");
		let op = if self.cmp == LimitComp::LessEq {
			"≤"
		} else {
			"="
		};
		format!("{x} {op} {:?}", *self.k)
	}
}

impl<Lit: Literal, C: Coefficient> Checker for Cardinality<Lit, C> {
	type Lit = Lit;

	fn check(&self, solution: &[Self::Lit]) -> Result<(), crate::CheckError<Self::Lit>> {
		Linear::from(self.clone()).check(solution)
	}
}

// Automatically implement AtMostOne encoding when you can encode Cardinality constraints
impl<DB: ClauseDatabase, Enc: Encoder<DB, Cardinality<DB::Lit, i8>> + CardMarker>
	Encoder<DB, CardinalityOne<DB::Lit>> for Enc
{
	fn encode(&mut self, db: &mut DB, con: &CardinalityOne<DB::Lit>) -> crate::Result {
		self.encode(db, &Cardinality::<DB::Lit, i8>::from(con.clone()))
	}
}
// local marker trait, to ensure the previous definition only applies within this crate
pub(crate) trait CardMarker {}
impl<T: LinMarker> CardMarker for T {}
