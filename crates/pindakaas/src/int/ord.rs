use std::collections::BTreeSet;

use itertools::Itertools;

use super::Dom;
use crate::{
	helpers::negate_cnf,
	trace::{emit_clause, new_var},
	ClauseDatabase, Lit, Var,
};

#[derive(Debug, Clone)]
pub(crate) struct OrdEnc {
	pub(crate) x: Vec<Lit>,
}

impl OrdEnc {
	pub(crate) fn new<DB: ClauseDatabase>(db: &mut DB, dom: &Dom, _lbl: Option<&String>) -> Self {
		let _lbl = _lbl.cloned().unwrap_or(String::from("b"));
		Self {
			x: dom
				.iter()
				.skip(1)
				.map(|_v| new_var!(db, format!("{_lbl}≥{_v}")))
				.collect(),
		}
	}

	pub(crate) fn from_lits(x: &[Lit]) -> Self {
		Self { x: x.to_vec() }
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

	pub(crate) fn consistent<DB: ClauseDatabase>(&self, db: &mut DB) -> crate::Result {
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
	use super::*;
	use crate::helpers::tests::{lits, TestDB};
	#[test]
	fn test_ineq() {
		let mut db = TestDB::new(0);
		let x = OrdEnc::new(&mut db, &Dom::from_slice(&[2, 5, 6, 7, 9]), None);

		for (dom_pos, expected_cnf) in [
			(Some(0), vec![]),
			(Some(1), vec![lits![1]]),
			(Some(2), vec![lits![2]]),
			(Some(3), vec![lits![3]]),
			(Some(4), vec![lits![4]]),
			(None, vec![lits![]]),
		] {
			assert_eq!(
				x.geq(dom_pos),
				expected_cnf,
				"Domain pos {dom_pos:?} was expected to return {expected_cnf:?}"
			);
		}
	}
}
