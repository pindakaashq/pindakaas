use std::fmt::{self, Display};

use crate::{Coefficient, Lin, Literal, Model, Term};
use itertools::Itertools;

use super::{display_dom, model::Obj, IntVar, LinExp};

impl<Lit: Literal, C: Coefficient> Display for Model<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for con in &self.cons {
			writeln!(f, "{}", con)?;
		}
		writeln!(f, "obj: {}", self.obj)?;
		Ok(())
	}
}

impl<Lit: Literal, C: Coefficient> Display for Term<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{:+}·{}", self.c, self.x.borrow())
	}
}

impl<Lit: Literal, C: Coefficient> Display for LinExp<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.terms.iter().join(" "))
	}
}

impl<Lit: Literal, C: Coefficient> Display for Obj<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Obj::Minimize(exp) => write!(f, "min {exp}"),
			Obj::Maximize(exp) => write!(f, "max {exp}"),
			Obj::Satisfy => write!(f, "sat"),
		}
	}
}

impl<Lit: Literal, C: Coefficient> Display for Lin<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if self.is_tern() {
			write!(
				f,
				"{} {} {} {}",
				self.exp.terms[0],
				self.exp.terms[1],
				self.cmp,
				self.exp.terms[2].clone() * -C::one(),
			)
		} else {
			write!(f, "{} {} {}", self.exp, self.cmp, self.k,)
		}
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVar<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{} ∈ {}", self.lbl(), display_dom::<Lit, C>(&self.dom))
	}
}
