mod constrain;
mod display;
mod enc;
mod helpers;
mod model;

use itertools::Itertools;
use std::collections::BTreeSet;

pub(crate) use constrain::{TernLeConstraint, TernLeEncoder};
pub(crate) use enc::{IntVarBin, IntVarEnc, IntVarOrd, LitOrConst};
pub use model::{Consistency, IntVar, Lin, LinExp, Model, Term};

use crate::{
	linear::Constraint, CheckError, Coefficient, LinExp as PbLinExp, Literal, Unsatisfiable,
};

use self::enc::GROUND_BINARY_AT_LB;

impl<Lit: Literal, C: Coefficient> PbLinExp<Lit, C> {
	pub(crate) fn assign(&self, solution: &[Lit]) -> Result<C, CheckError<Lit>> {
		let evaluate = |assignments: &Vec<(Lit, C, Lit)>| {
			assignments
				.iter()
				.fold(C::zero(), |acc, (lit, coef, assignment)| {
					acc + if lit == assignment { *coef } else { C::zero() }
				})
		};
		self.iter().fold(Ok(self.add), |acc, (constraint,terms) | {
            let assignments = terms.into_iter().map(|(lit,coef)| {
                let assignment = solution.iter().find(|x| x.var() == lit.var()).unwrap_or_else(|| panic!("Could not find lit {lit:?} in solution {solution:?}; perhaps this variable did not occur in any clause"));
                                                    (
                    lit.clone(),*coef,assignment.clone())
                    }).collect::<Vec<(Lit,C,Lit)>>();

            let is_consistent = match constraint {
                Some(Constraint::AtMostOne) => assignments.iter().filter(|(lit,_,a)| lit == a).count() <= 1,
                Some(Constraint::ImplicationChain) =>  assignments.iter().map(|(lit,_,a)| lit == a).tuple_windows().all(|(a, b)| a.cmp(&b).is_ge()),
                Some(Constraint::Domain { lb, ub }) => {
                    // divide by first coeff to get int assignment
                    let a = evaluate(&assignments).div(assignments[0].1);
                    if GROUND_BINARY_AT_LB {
                        a <= ub - lb
                    } else {
                    lb <= a && a <= ub
                    }
                },
                None => true
            };

            if is_consistent {
                Ok(acc?+evaluate(&assignments) * self.mult)
            } else {
                Err(CheckError::Unsatisfiable(Unsatisfiable))
            }
		})
	}
}

pub(crate) fn display_dom<C: Coefficient>(dom: &BTreeSet<C>) -> String {
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
			IntVar::required_bits(lb, ub)
		)
	} else {
		format!("{{{}}}", dom.iter().join(","))
	}
}
