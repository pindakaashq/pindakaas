use std::collections::BTreeSet;

use itertools::Itertools;

use super::Dom;
use crate::{
	helpers::{emit_clause, negate_cnf, new_var},
	ClauseDatabase, Lit, Var,
};

#[derive(Debug, Clone, Default)]
pub(crate) struct OrdEnc {
	pub(crate) x: Vec<Lit>,
}

impl From<Vec<Lit>> for OrdEnc {
	fn from(x: Vec<Lit>) -> Self {
		Self { x }
	}
}

impl OrdEnc {
	pub(crate) fn new<DB: ClauseDatabase>(db: &mut DB, dom: &Dom, _lbl: &str) -> Self {
		Self {
			x: dom
				.iter()
				.skip(1)
				.map(|_v| new_var!(db, format!("{_lbl}≥{_v}")))
				.collect(),
		}
	}

	// TODO difficulty turning this into iterator?
	// pub fn iter(&self) -> impl Iterator<Item = Vec<.....>> {
	pub(crate) fn ineqs(&self, up: bool) -> Vec<(Vec<Vec<Lit>>, bool)> {
		if up {
			[(vec![], false)]
				.into_iter()
				.chain(self.x.iter().map(|x| (vec![vec![*x]], true)))
				.collect()
		} else {
			self.x
				.iter()
				.map(|x| (vec![vec![!x]], true))
				.chain([(vec![], false)])
				.collect()
		}
	}

	/// From domain position to cnf
	pub(crate) fn geq(&self, p: Option<usize>) -> Vec<Vec<Lit>> {
		match p {
			Some(0) => {
				vec![]
			} // true
			Some(p) => {
				vec![vec![self.x[p - 1]]]
			} // lit
			None => {
				vec![vec![]]
			} // false
		}
	}

	// TODO could maybe be removed since we always use geq now..
	/// From domain position to cnf
	pub(crate) fn _ineq(&self, p: Option<usize>, up: bool) -> Vec<Vec<Lit>> {
		let geq = match p {
			Some(0) => {
				vec![]
			} // true
			Some(p) => {
				vec![vec![self.x[p - 1]]]
			} // lit
			None => {
				vec![vec![]]
			} // false
		};
		if up {
			geq
		} else {
			negate_cnf(geq)
		}
	}

	pub(crate) fn consistent<DB: ClauseDatabase>(&mut self, db: &mut DB) -> crate::Result {
		self.x.iter().tuple_windows().try_for_each(|(a, b)| {
			if a.var() != b.var() {
				emit_clause!(db, [!b, *a])
			} else {
				Ok(())
			}
		})
	}

	pub(crate) fn lits(&self) -> BTreeSet<Var> {
		self.x.clone().into_iter().map(|lit| lit.var()).collect()
	}

	pub(crate) fn iter(&self) -> impl Iterator<Item = &Lit> {
		self.x.iter()
	}
}

impl std::fmt::Display for OrdEnc {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "[{}]", self.x.iter().join(", "))
	}
}

#[cfg(test)]
mod tests {
	use crate::{
		helpers::tests::{assert_encoding, expect_file},
		Cnf,
	};

	use super::*;
	#[test]
	fn test_ineq() {
		let mut cnf = Cnf::default();
		let x = OrdEnc::new(&mut cnf, &Dom::new([2, 5, 6, 7, 9]), "ord");

		for k in 0..=3 {
			assert_encoding(
				&Cnf::try_from(x.geq(Some(k))).unwrap(),
				&expect_file![format!("integer/ord/geq_{k}.cnf")],
			);
		}
	}
}
