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
pub use model::{Assignment, Consistency, Decomposer, Model, ModelConfig, Obj, Scm};
pub use term::Term;

use crate::{CheckError, LinExp as PbLinExp, Valuation};

impl PbLinExp {
	pub(crate) fn assign<F: Valuation + ?Sized>(&self, solution: &F) -> Result<Coeff, CheckError> {
		self.iter().try_fold(self.add, |acc, (_, terms)| {
			Ok(acc
				+ terms.into_iter().fold(0, |acc, (lit, coef)| {
					acc + solution
						.value(*lit)
						.unwrap_or_else(|| panic!("TODO unassigned"))
						.then_some(coef)
						.unwrap_or(&0)
				}) * self.mult)
			// let is_consistent = match constraint {
			// 	Some(Constraint::AtMostOne) => assignments.iter().filter(|(lit,_,a)| lit == a).count() <= 1,
			// 	Some(Constraint::ImplicationChain) =>  assignments.iter().map(|(lit,_,a)| lit == a).tuple_windows().all(|(a, b)| a.cmp(&b).is_ge()),
			// 	Some(Constraint::Domain { lb, ub }) => {
			// 		// divide by first coeff to get int assignment
			// // TODO what if there are two constraint groups?
			// if assignments.is_empty() {
			// let a = self.add;
			// assert!(lb <= a && a <= ub, "For a constant, we expect consistency in checking but got !({lb}<={a}<={ub})");
			// true
			// } else {
			// let a = self.add + evaluate(&assignments).div(assignments[0].1);
			// lb <= a && a <= ub
			// }
			// 	},
			// 	None => true
			// };

			// if is_consistent {
			// 	Ok(acc+evaluate(&assignments) * self.mult)
			// } else {
			// 	Err(CheckError::Unsatisfiable(Unsatisfiable))
			// }
		})
	}
}

use crate::{Coeff, Result};
