mod bin;
mod con;
mod decompose;
mod display;
mod dom;
pub(crate) mod enc;
pub(crate) mod helpers;
mod int_var;
mod model;
mod ord;
mod res;
mod term;

pub use con::{Lin, LinExp};
pub use decompose::{Decompose, ModelDecomposer};
pub use dom::Dom;
pub(crate) use enc::{IntVarEnc, LitOrConst};
pub(crate) use helpers::required_lits;
pub use helpers::Format;
pub use int_var::{IntVar, IntVarId, IntVarRef};
pub(crate) use model::Cse;
pub use model::{Assignment, Consistency, Decomposer, GtSort, Model, ModelConfig, Obj, Scm};
pub use term::Term;

use crate::{CheckError, LinExp as PbLinExp, Valuation};

impl PbLinExp {
	pub(crate) fn assign<F: Valuation + ?Sized>(&self, solution: &F) -> Result<Coeff, CheckError> {
		self.iter().try_fold(self.add, |acc, (_, terms)| {
			Ok(acc
				+ terms.into_iter().fold(0, |acc, (lit, coef)| {
					acc + if solution
						.value(*lit)
						.unwrap_or_else(|| panic!("TODO unassigned"))
					{
						coef
					} else {
						&0
					}
				}) * self.mult)
		})
	}
}

use crate::{Coeff, Result};
