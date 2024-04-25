mod constrain;
mod enc;
mod model;

use std::collections::BTreeSet;

pub(crate) use constrain::{TernLeConstraint, TernLeEncoder};
pub(crate) use enc::{IntVarBin, IntVarEnc, IntVarOrd, LitOrConst};
use itertools::Itertools;
pub(crate) use model::{Consistency, IntVar, Lin, Model};

use self::enc::GROUND_BINARY_AT_LB;
use crate::{linear::Constraint, CheckError, Coeff, LinExp, Result, Unsatisfiable, Valuation};

impl LinExp {
	pub(crate) fn value<F: Valuation + ?Sized>(&self, sol: &F) -> Result<Coeff, CheckError> {
		let mut total = self.add;
		for (constraint, terms) in self.iter() {
			// Calculate sum for constraint
			let sum = terms
				.iter()
				.filter(|(lit, _)| sol.value(*lit).expect("missing assignment to literal"))
				.map(|(_, i)| i)
				.sum();
			match constraint {
				Some(Constraint::AtMostOne) => {
					if sum != 0
						&& terms
							.iter()
							.filter(|&(l, _)| sol.value(*l).unwrap_or(true))
							.count() > 1
					{
						return Err(Unsatisfiable.into());
					}
				}
				Some(Constraint::ImplicationChain) => {
					if terms
						.iter()
						.map(|(l, _)| *l)
						.tuple_windows()
						.any(|(a, b)| !sol.value(a).unwrap_or(false) & sol.value(b).unwrap_or(true))
					{
						return Err(Unsatisfiable.into());
					}
				}
				Some(Constraint::Domain { lb, ub }) => {
					// divide by first coeff to get int assignment
					if GROUND_BINARY_AT_LB {
						if sum > ub - lb {
							return Err(Unsatisfiable.into());
						}
					} else if lb > sum || sum > ub {
						return Err(Unsatisfiable.into());
					}
				}
				None => {}
			};
			total += sum;
		}
		Ok(total * self.mult)
	}
}

pub(crate) fn display_dom(dom: &BTreeSet<Coeff>) -> String {
	const ELIPSIZE: usize = 8;
	let (lb, ub) = (*dom.first().unwrap(), *dom.last().unwrap());
	if dom.len() > ELIPSIZE && dom.len() == (ub - lb + 1) as usize {
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
