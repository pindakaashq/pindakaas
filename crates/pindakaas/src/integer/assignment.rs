use crate::{Coeff, Lit, Valuation, Var};
use std::{
	cmp::Ordering,
	fmt::{Display, Formatter},
};

use itertools::Itertools;
use rustc_hash::FxHashMap;

use super::{IntVar, IntVarRef};

// TODO [?] equivalent of Valuation, could be merged?
/// A structure holding an integer assignment to `Model`
#[derive(Debug, Default, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Assignment(FxHashMap<String, (Coeff, Option<MapSol>)>);

impl Assignment {
	pub fn new<F: Valuation + ?Sized>(xs: impl Iterator<Item = IntVarRef>, sol: &F) -> Self {
		Self::from(
			xs.map(|x| {
				(
					x.clone(),
					(
						x.borrow().assign(sol).unwrap(),
						Some(MapSol::new(x.borrow().lits(), sol)),
					),
				)
			})
			.collect_vec(),
		)
	}

	pub fn value(&self, x: &IntVar) -> Option<Coeff> {
		self.0.get(&x.lbl()).map(|(a, _)| *a)
	}

	// TODO make sensible
	pub fn sol(&self, x: &IntVar) -> Option<Option<MapSol>> {
		self.0.get(&x.lbl()).map(|(_, sol)| sol.clone())
	}

	// /// Return assignment of a subset of variables
	// pub fn partialize(&self, xs: &[IntVarRef]) -> Self {
	// 	Self::from(
	// 		xs.iter()
	// 			.map(|x| (x.clone(), (self.value(&x.borrow()).unwrap(), None)))
	// 			.collect_vec(),
	// 	)
	// }
}

impl From<Vec<(IntVarRef, Coeff)>> for Assignment {
	fn from(value: Vec<(IntVarRef, Coeff)>) -> Self {
		Self::from(
			value
				.into_iter()
				.map(|(var, a)| (var, (a, None)))
				.collect_vec(),
		)
	}
}
impl From<Vec<(IntVarRef, (Coeff, Option<MapSol>))>> for Assignment {
	fn from(value: Vec<(IntVarRef, (Coeff, Option<MapSol>))>) -> Self {
		Self(
			value
				.into_iter()
				.map(|(var, a)| (var.borrow().lbl(), a))
				// .sorted_by_key(|(x, _)| x.clone()) // sorting makes serialization output a little nicer
				.collect(),
		)
	}
}

impl Display for Assignment {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			self.0
				.iter()
				.sorted_by_key(|(lbl, _)| *lbl)
				.map(|(lbl, (a, s))| format!(
					"{}={} [{}]",
					lbl,
					a,
					s.as_ref().map(|s| format!("{s}")).unwrap_or_default()
				))
				.join(", "),
		)
	}
}

impl Ord for Assignment {
	fn cmp(&self, other: &Self) -> Ordering {
		self.0
			.iter()
			.map(|(x, (a, _))| (x, a))
			.sorted()
			.cmp(other.0.iter().map(|(x, (a, _))| (x, a)).sorted())
	}
}

impl PartialOrd for Assignment {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

// impl Index<&IntVarId> for Assignment {
// 	type Output = (String, Coeff);
// 	fn index(&self, id: &IntVarId) -> &Self::Output {
// 		&self.0[id]
// 	}
// }

#[derive(Debug, Default, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MapSol(pub(crate) FxHashMap<Var, bool>);

impl MapSol {
	pub fn new<V, I, F>(vars: I, sol: &F) -> Self
	where
		V: Into<Lit>,
		I: IntoIterator<Item = V> + Clone,
		F: Valuation + ?Sized,
	{
		Self(
			vars.into_iter()
				.map(|v| v.into())
				.map(|v| (v.clone().var(), sol.value(v)))
				.collect(),
		)
	}
	pub fn iter(&self) -> impl Iterator<Item = Lit> + use<'_> {
		self.0
			.iter()
			.map(|(&v, &b)| if b { Lit::from(v) } else { !Lit::from(v) })
	}
}

// #[derive(Debug, Default, Clone, PartialEq)]
// pub struct MapSol(pub(crate) FxHashMap<Var, bool>);

// impl From<CadicalSol>
// /// Show MapSol as sol file
// // using Display for this since (W)Cnf does it similarly
// impl From<MapSol> for Vec<Vec<Lit>> {
// 	fn from(value: MapSol) -> Self {
// 		value
// 			.0
// 			.iter()
// 			.map(|(&k, &v)| if v { Lit::from(k) } else { !Lit::from(k) })
// 			.collect()
// 	}
// }

impl Display for MapSol {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			self.iter()
				.sorted_by_key(|lit| lit.var())
				.map(|lit| format!("{:?}", lit))
				.join(", ")
		)
	}
}

// impl From<Vec<Lit>> for MapSol {
// 	fn from(value: &[Lit]) -> Self {
// 		Self(
// 			value
// 				.into_iter()
// 				.map(|lit| (lit.var(), !lit.is_negated()))
// 				.collect::<FxHashMap<_, _>>(),
// 		)
// 	}
// }

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
					if v.value(lit) {
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
	fn value(&self, lit: Lit) -> bool {
		if let Some(&a) = self.0.get(&lit.var()) {
			if lit.is_negated() {
				!a
			} else {
				a
			}
		} else {
			panic!("Literal {lit} was not assigned")
		}
	}
}
