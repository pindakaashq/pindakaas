use crate::{Coeff, IntVarId, Lit, Valuation, Var};
use std::{cmp::Ordering, collections::HashMap, ops::Index};

use itertools::Itertools;

// TODO [?] equivalent of Valuation, could be merged?
/// A structure holding an integer assignment to `Model`
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct Assignment(pub HashMap<IntVarId, (String, Coeff)>);

impl Ord for Assignment {
	fn cmp(&self, other: &Self) -> Ordering {
		self.0.iter().sorted().cmp(other.0.iter().sorted())
	}
}

impl PartialOrd for Assignment {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Index<&IntVarId> for Assignment {
	type Output = (String, Coeff);

	fn index(&self, id: &IntVarId) -> &Self::Output {
		&self.0[id]
	}
}

impl Assignment {
	pub(crate) fn partialize(self, max_var: &IntVarId) -> Self {
		Self(self.0.into_iter().filter(|(k, _)| k <= max_var).collect())
	}
}

#[derive(Debug)]
pub struct MapSol(HashMap<Var, bool>);

impl From<Vec<Lit>> for MapSol {
	fn from(value: Vec<Lit>) -> Self {
		Self(
			value
				.into_iter()
				.map(|lit| (lit.var(), !lit.is_negated()))
				.collect::<HashMap<_, _>>(),
		)
	}
}

// TODO can't get this to compile inside
// impl TryInto<Vec<Lit>> for MapSol {
// 	type Error = ();
// 	fn try_into(self) -> Result<Vec<Lit>, Self::Error> {
// 		if self.0.is_empty() {
// 			Ok(vec![])
// 		} else if self.0.keys().min().unwrap() == &Var::from(1)
// 			&& self
// 				.0
// 				.keys()
// 				.tuple_windows()
// 				.all(|(a, b)| &a.next_var().unwrap() == b)
// 		{
// 			Ok(self
// 				.0
// 				.keys()
// 				.sorted()
// 				.map(|k| {
// 					let lit = Lit::from(*k);
// 					if self.value(lit).unwrap() {
// 						lit
// 					} else {
// 						!lit
// 					}
// 				})
// 				.collect())
// 		} else {
// 			Err(())
// 		}
// 	}
// }

impl TryFrom<MapSol> for Vec<Lit> {
	type Error = ();
	fn try_from(v: MapSol) -> Result<Self, Self::Error> {
		let vars = v.0.keys().cloned().sorted().collect_vec();
		if v.0.is_empty() {
			Ok(vec![])
		} else if vars.first().unwrap() == &Var::from(1)
			&& vars
				.iter()
				.tuple_windows()
				.all(|(a, b)| &a.next_var().unwrap() == b)
		{
			Ok(vars
				.into_iter()
				.map(|k| {
					let lit = Lit::from(k);
					if v.value(lit).unwrap() {
						lit
					} else {
						!lit
					}
				})
				.collect())
		} else {
			Err(())
		}
	}
}

impl Valuation for MapSol {
	fn value(&self, lit: Lit) -> Option<bool> {
		self.0
			.get(&lit.var())
			.copied()
			.map(|a| if lit.is_negated() { !a } else { a })
	}
}
