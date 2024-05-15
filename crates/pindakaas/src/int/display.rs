use std::fmt::{self, Display};

use itertools::Itertools;

use super::{
	model::{Obj, USE_CSE},
	Cse, IntVar, LinExp,
};
use crate::{int::IntVarEnc, Assignment, Lin, Model, Term};

pub(crate) const SHOW_IDS: bool = false;
const SHOW_LITS: bool = true;
/// Whether to rewrite x1 + .. + xn # 0 as x1 + .. + x_(n-1) # - xn
const SHOW_K_0: bool = true;

impl Display for Model {
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
		if USE_CSE {
			writeln!(f, "\tCSE: {}", self.cse)?;
		}
		Ok(())
	}
}

impl Display for Assignment {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			self.0
				.iter()
				.sorted()
				.map(|(_, (lbl, a))| format!("{}={}", lbl, a))
				.join(", ")
		)
	}
}

impl Display for LinExp {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let s = self.terms.iter().join(" ");
		if s.len() >= 2 && &s[..2] == "+ " {
			write!(f, "{}", &s[2..])
		} else {
			write!(f, "{}", s)
		}
	}
}

impl Display for Term {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.c {
			0 => write!(f, "+ 0"),
			1 => write!(f, "+ ({})", self.x.borrow()),
			-1 => write!(f, "- ({})", self.x.borrow()),
			c if c.is_positive() => write!(f, "+ {}·({})", c, self.x.borrow()),
			c => write!(f, "- ({}·{})", c.abs(), self.x.borrow()),
		}
	}
}

impl Display for Obj {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Obj::Minimize(exp) => write!(f, "min {exp}"),
			Obj::Maximize(exp) => write!(f, "max {exp}"),
			Obj::Satisfy => write!(f, "sat"),
		}
	}
}

impl Display for Lin {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let lbl = self
			.lbl
			.as_ref()
			.map(|lbl| format!("{}: ", lbl))
			.unwrap_or_default();
		if SHOW_K_0
			&& self.k == 0
			&& self.exp.terms.len() > 1
			&& self.exp.terms.last().unwrap().c.is_negative()
		{
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
						terms: vec![rhs.clone() * -1]
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

impl fmt::Display for IntVar {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}{}{} ∈ {} {}",
			self.lbl(),
			match self.e.as_ref() {
				Some(IntVarEnc::Bin(x_bin)) => format!(
					":B{}",
					(if SHOW_LITS {
						x_bin
							.as_ref()
							.map(|x_bin| format!(" [{x_bin}]"))
							.unwrap_or_default()
					} else {
						String::new()
					})
				),
				Some(IntVarEnc::Ord(_)) => ":O".to_string(),
				None => String::new(),
			},
			self.add_consistency.then_some("!").unwrap_or_default(),
			self.dom,
			if SHOW_LITS {
				format!("[{}]", self.lits().iter().sorted().join(", "))
			} else {
				format!("{}L", self.lits().len())
			},
		)
	}
}

impl Display for Cse {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{:?}",
			self.0
				.iter()
				.sorted_by_key(|(k, _)| *k)
				.map(|((id, c, cmp), v)| format!("{c}*x#{id} {cmp} {v}"))
				.join(", ")
		)
	}
}
