use std::fmt::{self, Display};

use crate::Lin;
use crate::{int::IntVarEnc, Coefficient, Literal, Model, Term};
use itertools::Itertools;

use super::{model::Obj, IntVar, LinExp};

pub(crate) const SHOW_IDS: bool = false;
const SHOW_LITS: bool = false;
/// Whether to rewrite x1 + .. + xn # 0 as x1 + .. + x_(n-1) # - xn
const SHOW_K_0: bool = true;

impl<Lit: Literal, C: Coefficient> Display for Model<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if SHOW_IDS {
			writeln!(f, "num_var: {}", self.num_var)?;
		} else {
			writeln!(f)?;
		}
		for con in &self.cons {
			writeln!(f, "\t{}", con)?;
		}
		if !self.obj.is_satisfy() {
			writeln!(f, "\tobj: {}", self.obj)?;
		}
		Ok(())
	}
}

impl<Lit: Literal, C: Coefficient> Display for LinExp<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let s = self.terms.iter().join(" ");
		if s.len() >= 2 && &s[..2] == "+ " {
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
		let lbl = self
			.lbl
			.as_ref()
			.map(|lbl| format!("{}: ", lbl))
			.unwrap_or_default();
		if SHOW_K_0 && self.k.is_zero() && self.exp.terms.len() > 1 {
			// Put in LinExp to avoid printing '+' at start
			if let Some((rhs, lhs)) = self.exp.terms.split_last() {
				write!(
					f,
					"{}\t{} {} {}",
					lbl,
					LinExp {
						terms: lhs.to_vec()
					},
					self.cmp,
					LinExp {
						terms: vec![rhs.clone() * -C::one()]
					},
				)
			} else {
				panic!();
			}
		} else {
			write!(f, "{}{} {} {}", lbl, self.exp, self.cmp, self.k,)
		}
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVar<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}{} ∈ {} {}",
			self.lbl(),
			match self.e {
				Some(IntVarEnc::Bin(_)) => ":B",
				Some(IntVarEnc::Ord(_)) => ":O",
				Some(IntVarEnc::Const(_)) => unreachable!(),
				None => "",
			},
			self.dom,
			if SHOW_LITS {
				format!("[{}]", self.lits().iter().sorted().join(", "))
			} else {
				format!("{}L", self.lits().len())
			},
		)
	}
}