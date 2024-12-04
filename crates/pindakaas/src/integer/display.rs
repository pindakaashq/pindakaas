// TODO Refactor: move display to where struct has its other impls
use crate::integer::{enc::IntVarEnc, Lin, Model, Term};
use std::fmt::{self, Display};

use itertools::Itertools;

use crate::integer::IntVar;
use crate::integer::{model::Cse, Dom, LinExp};
use crate::Coeff;

use super::model::{Obj, USE_CSE};

/// Show the integer variable's ID
pub(crate) const SHOW_IDS: bool = false;
/// Show the encoding literals of the integer variable
const SHOW_LITS: Option<usize> = Some(5);
/// Whether to rewrite x1 + .. + xn # 0 as x1 + .. + x_(n-1) # - xn
const SHOW_K_0: bool = true;
/// Show domain density
const SHOW_DOM_DENSITY: bool = false;

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
		if SHOW_K_0
			&& self.k == 0
			&& self.exp.terms.len() > 1
			&& self.exp.terms.last().unwrap().c.is_negative()
		{
			// Put in LinExp to avoid printing '+' at start
			if let Some((rhs, lhs)) = self.exp.terms.split_last() {
				write!(
					f,
					"{}:\t{} {} {}",
					self.lbl,
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
			write!(f, "{}:\t{} {} {}", self.lbl, self.exp, self.cmp, self.k)
		}
	}
}

impl Display for IntVar {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}{}{} ∈ {}{}",
			self.lbl(),
			match self.e.as_ref() {
				Some(IntVarEnc::Bin(_)) => String::from(":B"),
				Some(IntVarEnc::Ord(_)) => String::from(":O"),
				None => String::new(),
			},
			if self.add_consistency { "" } else { "!" },
			self.dom,
			if let Some(l) = SHOW_LITS {
				format!("[{}]", elipsize(&self.lits().iter().collect_vec(), Some(l)))
			} else if !self.lits().is_empty() {
				format!(" [{}|]", self.lits().len())
			} else {
				String::new()
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

fn elipsize<T: Display>(x: &[T], e: Option<usize>) -> String {
	let e = e.map(|e| e).unwrap_or(x.len());
	if x.len() < e {
		x.iter().take(e).join(",")
	} else {
		format!(
			"{},..,{}|{}",
			x.len(),
			x.iter().take(e).join(","),
			x.last().unwrap()
		)
	}
}

impl Display for Dom {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		// TODO replaced {..} by |..| since logger interprets {/} wrong
		let dom = self.iter().collect::<Vec<_>>();
		if dom.is_empty() {
			return write!(f, "||");
		}
		let (lb, ub) = (*dom.first().unwrap(), *dom.last().unwrap());
		const ELIPSIZE: Option<usize> = Some(4);

		if dom.len() > 1 && Coeff::try_from(dom.len()).unwrap() == ub - lb + 1 {
			write!(f, "|{}..{}|{}", dom.len(), lb, ub)?;
		} else {
			write!(
				f,
				"|{}|{}",
				elipsize(&dom.iter().collect_vec(), ELIPSIZE),
				if dom.len() <= 1 || !SHOW_DOM_DENSITY {
					String::from("")
				} else {
					format!("{:.0}%", self.density() * 100.0)
				}
			)?
		}
		Ok(())
	}
}
