mod bin;
mod constrain;
mod display;
mod dom;
mod enc;
pub(crate) mod helpers;
mod model;
mod ord;
mod scm;

use itertools::Itertools;

pub(crate) use constrain::{TernLeConstraint, TernLeEncoder};
pub use dom::Dom;
pub(crate) use enc::{IntVarBin, IntVarEnc, IntVarOrd, LitOrConst};
pub(crate) use helpers::required_lits;
pub use helpers::Format;
pub use model::{
	Assignment, Consistency, Decompose, Decomposer, IntVar, IntVarId, IntVarRef, Lin, LinExp,
	Model, ModelConfig, Obj, Scm, Term,
};

use crate::{CheckError, Coefficient, LinExp as PbLinExp, Literal};

impl<Lit: Literal, C: Coefficient> PbLinExp<Lit, C> {
	pub(crate) fn assign(&self, solution: &[Lit]) -> Result<C, CheckError<Lit>> {
		let evaluate = |assignments: &Vec<(Lit, C, Lit)>| {
			assignments
				.iter()
				.fold(C::zero(), |acc, (lit, coef, assignment)| {
					acc + if lit == assignment { *coef } else { C::zero() }
				})
		};
		self.iter().try_fold(self.add, |acc, (_,terms) | {
			let assignments: Vec<(Lit,C,Lit)> = terms.into_iter().map(|(lit,coef)| {
				let assignment = solution.iter()
					.find(|x| x.var() == lit.var())
					.unwrap_or_else(|| panic!("Could not find lit {lit:?} in solution {solution:?}; perhaps this variable did not occur in any clause"));
				(lit.clone(), *coef,assignment.clone())
			}).collect();

				Ok(acc+evaluate(&assignments) * self.mult)
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

pub(crate) fn display_dom<C: Coefficient>(dom: &[C]) -> String {
	const ELIPSIZE: usize = 8;
	if dom.is_empty() {
		return String::from("{}");
	}
	let (lb, ub) = (*dom.first().unwrap(), *dom.last().unwrap());
	if dom.len() > ELIPSIZE && C::from(dom.len()).unwrap() == ub - lb + C::one() {
		format!("{}..{}", dom.first().unwrap(), dom.last().unwrap())
	} else if dom.len() > ELIPSIZE {
		format!(
			"{{{},..,{ub}}} ({}|{})",
			dom.iter().take(ELIPSIZE).join(","),
			dom.len(),
			required_lits(lb, ub)
		)
	} else {
		format!("{{{}}}", dom.iter().join(","))
	}
}
