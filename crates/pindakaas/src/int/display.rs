use std::fmt::{self, Display};

use crate::{int::IntVarEnc, Coefficient, Lin, Literal, Model, Term};
use itertools::Itertools;

use super::{model::Obj, IntVar, LinExp};

const SHOW_IDS: bool = false;

impl<Lit: Literal, C: Coefficient> Display for Model<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for con in &self.cons {
			writeln!(f, "{}", con)?;
		}
		if !self.obj.is_satisfy() {
			writeln!(f, "obj: {}", self.obj)?;
		}
		writeln!(f, "num_var: {}", self.num_var)?;
		Ok(())
	}
}

impl<Lit: Literal, C: Coefficient> Display for LinExp<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let s = self.terms.iter().join(" ");
		if &s[..2] == "+ " {
			write!(f, "{}", &s[2..])
		} else {
			write!(f, "{}", s)
		}
	}
}

impl<Lit: Literal, C: Coefficient> Display for Term<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if self.c.is_zero() {
			write!(f, "+ 0")
		} else if self.c.is_one() {
			write!(f, "+ ({})", self.x.borrow())
		} else if self.c == -C::one() {
			write!(f, "- ({})", self.x.borrow())
		} else if self.c.is_positive() {
			write!(f, "+ {}·({})", self.c, self.x.borrow())
		} else {
			write!(f, "- ({}·{})", self.c.abs(), self.x.borrow())
		}
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
		// if self.is_tern() && false {
		// 	write!(
		// 		f,
		// 		"{} {} {} {}",
		// 		self.exp.terms[0].borrow(),
		// 		self.exp.terms[1].borrow(),
		// 		self.cmp,
		// 		self.exp.terms[2].borrow().clone() * -C::one(),
		// 	)
		// } else {
		write!(f, "{} {} {}", self.exp, self.cmp, self.k,)
		// }
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVar<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}{}{} ∈ {}",
			self.lbl(),
			match self.e {
				Some(IntVarEnc::Bin(_)) => ":B",
				Some(IntVarEnc::Ord(_)) => ":O",
				Some(IntVarEnc::Const(_)) => unreachable!(),
				None => "",
			},
			if SHOW_IDS {
				format!("#{}", self.id)
			} else {
				String::from("")
			},
			self.dom,
		)
	}
}
