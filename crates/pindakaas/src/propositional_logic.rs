use std::{fmt::Display, iter::once, ops::Not};

use itertools::{Itertools, Position};

use crate::{ClauseDatabase, Cnf, Encoder, Lit, Result};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
	Atom(Lit),
	Not(Box<Formula>),
	And(Vec<Formula>),
	Or(Vec<Formula>),
	Implies(Box<Formula>, Box<Formula>),
	Equiv(Vec<Formula>),
	Xor(Vec<Formula>),
	IfThenElse {
		cond: Box<Formula>,
		then: Box<Formula>,
		els: Box<Formula>,
	},
}

impl Formula {
	pub fn clausify(&self) -> Result<Cnf> {
		let mut cnf = Cnf::default();
		cnf.encode(self, &TseitinEncoder)?;
		Ok(cnf)
	}

	/// Helper function to bind the (sub) formula to a name (literal) for the tseitin encoding.
	fn bind(&self, db: &mut impl ClauseDatabase, name: Option<Lit>) -> Result<Lit> {
		// let name = name.unwrap_or_else(|| db.new_var().into());
		Ok(match self {
			Formula::Atom(lit) => {
				if let Some(name) = name {
					db.add_clause(vec![!name, *lit])?;
					db.add_clause(vec![name, !lit])?;
					name
				} else {
					*lit
				}
			}
			Formula::Not(f) => !(f.bind(db, name)?),
			Formula::And(sub) => {
				assert_ne!(sub.len(), 0, "unable to bind empty and formula");
				if sub.len() == 1 {
					return sub[0].bind(db, name);
				}
				let name = name.unwrap_or_else(|| db.new_var().into());
				let lits = sub
					.iter()
					.map(|f| f.bind(db, None))
					.collect::<Result<Vec<_>>>()?;
				// not name -> (not lits[0] or not lits[1] or ...)
				db.add_clause(once(name).chain(lits.iter().map(|l| !l)))?;
				for lit in lits {
					// name -> lit
					db.add_clause([!name, lit])?;
				}
				name
			}
			Formula::Or(sub) => {
				assert_ne!(sub.len(), 0, "unable to bind empty or formula");
				if sub.len() == 1 {
					return sub[0].bind(db, name);
				}
				let name = name.unwrap_or_else(|| db.new_var().into());
				let lits = sub
					.iter()
					.map(|f| f.bind(db, None))
					.collect::<Result<Vec<_>>>()?;
				for lit in &lits {
					// not name -> not lit
					db.add_clause([name, !lit])?;
				}
				// name -> (lit[0] or lit[1] or ...)
				db.add_clause(once(!name).chain(lits.into_iter()))?;
				name
			}
			Formula::Implies(left, right) => {
				let name = name.unwrap_or_else(|| db.new_var().into());
				let left = left.bind(db, None)?;
				let right = right.bind(db, None)?;
				// name -> (left -> right)
				db.add_clause([!name, !left, right])?;
				// !name -> !(left -> right)
				// i.e, (!name -> left) and (!name -> !right)
				db.add_clause([name, left])?;
				db.add_clause([name, !right])?;
				name
			}
			Formula::Equiv(sub) => {
				assert!(
					sub.len() < 2,
					"unable to bind the equivalence of less than 2 formulas"
				);
				let name = name.unwrap_or_else(|| db.new_var().into());
				let lits = sub
					.iter()
					.map(|f| f.bind(db, None))
					.collect::<Result<Vec<_>>>()?;
				for (x, y) in lits.iter().tuple_windows() {
					// name -> (x <-> y)
					db.add_clause([!name, !x, *y])?;
					db.add_clause([!name, *x, !y])?;
				}
				db.add_clause(once(name).chain(lits.iter().map(|l| !l)))?;
				db.add_clause(once(name).chain(lits.into_iter()))?;
				name
			}
			Formula::Xor(sub) => {
				assert_ne!(sub.len(), 0, "unable to bind empty xor formula");
				if sub.len() == 1 {
					return sub[0].bind(db, name);
				}
				let name = name.unwrap_or_else(|| db.new_var().into());
				let mut lits = sub
					.iter()
					.map(|f| f.bind(db, None))
					.collect::<Result<Vec<_>>>()?;

				let mut left = lits.pop().unwrap();
				for (pos, right) in lits.into_iter().with_position() {
					let new_name = match pos {
						Position::Last | Position::Only => name,
						_ => db.new_var().into(),
					};
					// new_name -> (left xor right)
					db.add_clause([!new_name, !left, !right])?;
					db.add_clause([!new_name, left, right])?;
					// !new_name -> !(left xor right)
					db.add_clause([new_name, !left, right])?;
					db.add_clause([new_name, left, !right])?;

					left = new_name;
				}
				// let mut
				name
			}
			Formula::IfThenElse { cond, then, els } => {
				let name = name.unwrap_or_else(|| db.new_var().into());
				let cond = cond.bind(db, None)?;
				let then = then.bind(db, None)?;
				let els = els.bind(db, None)?;
				// name -> (cond -> then)
				db.add_clause([!name, !cond, then])?;
				// name -> (not cond -> els)
				db.add_clause([!name, cond, els])?;

				// inverse implications
				db.add_clause([name, !cond, !then])?;
				db.add_clause([name, cond, !els])?;
				db.add_clause([name, !then, !els])?;

				name
			}
		})
	}
}

impl Not for Formula {
	type Output = Formula;
	fn not(self) -> Self {
		match self {
			Formula::Atom(l) => Formula::Atom(!l),
			Formula::Not(f) => *f,
			_ => Formula::Not(Box::new(self)),
		}
	}
}

impl Display for Formula {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Formula::Atom(l) => write!(f, "{l}"),
			Formula::Not(sub) => write!(f, "¬({})", sub),
			Formula::And(sub) => write!(
				f,
				"{}",
				sub.iter()
					.format_with(" ∧ ", |elt, f| f(&format_args!("({elt})")))
			),
			Formula::Or(sub) => write!(
				f,
				"{}",
				sub.iter()
					.format_with(" ∨ ", |elt, f| f(&format_args!("({elt})")))
			),
			Formula::Implies(x, y) => write!(f, "({x}) → ({y})"),
			Formula::Equiv(sub) => write!(
				f,
				"{}",
				sub.iter()
					.format_with(" ≡ ", |elt, f| f(&format_args!("({elt})")))
			),
			Formula::Xor(sub) => write!(
				f,
				"{}",
				sub.iter()
					.format_with(" ⊻ ", |elt, f| f(&format_args!("({elt})")))
			),
			Formula::IfThenElse { cond, then, els } => {
				write!(f, "if ({cond}) then ({then}) else ({els}) endif")
			}
		}
	}
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct TseitinEncoder;

impl<DB: ClauseDatabase> Encoder<DB, Formula> for TseitinEncoder {
	fn encode(&self, db: &mut DB, f: &Formula) -> Result {
		match f {
			Formula::Atom(l) => db.add_clause([*l]),
			Formula::Not(f) => match f.as_ref() {
				Formula::Atom(l) => db.add_clause([!l]),
				Formula::Not(f) => self.encode(db, f),
				Formula::And(sub) => {
					let neg_sub = sub.iter().map(|f| !(f.clone())).collect();
					self.encode(db, &Formula::Or(neg_sub))
				}
				Formula::Or(sub) => {
					let neg_sub = sub.iter().map(|f| !(f.clone())).collect();
					self.encode(db, &Formula::And(neg_sub))
				}
				_ => {
					let l = f.bind(db, None)?;
					db.add_clause([!l])
				}
			},
			Formula::And(sub) => {
				for f in sub {
					self.encode(db, f)?;
				}
				Ok(())
			}
			Formula::Or(sub) => {
				let lits = sub
					.iter()
					.map(|f| f.bind(db, None))
					.collect::<Result<Vec<_>, _>>()?;
				db.add_clause(lits)
			}
			Formula::Implies(left, right) => {
				let x = left.bind(db, None)?;
				let mut cdb = db.with_conditions(vec![!x]);
				self.encode(&mut cdb, right)
			}
			Formula::Equiv(sub) => {
				match sub.len() {
					0 => return Ok(()),
					1 => return self.encode(db, &sub[0]),
					_ => {
						let mut name = sub.iter().find_map(|f| {
							if let Formula::Atom(l) = f {
								Some(*l)
							} else {
								None
							}
						});
						for f in sub.iter() {
							name = Some(f.bind(db, name)?);
						}
					}
				}
				Ok(())
			}
			Formula::Xor(sub) => match sub.len() {
				0 => Ok(()),
				1 => self.encode(db, &sub[0]),
				_ => {
					let mut sub = sub.clone();
					let a = sub.pop().map(|f| f.bind(db, None)).unwrap()?;
					let b = if sub.len() > 1 {
						Formula::Xor(sub).bind(db, None)
					} else {
						sub.pop().map(|f| f.bind(db, None)).unwrap()
					}?;
					db.add_clause([a, b])?;
					db.add_clause([!a, !b])
				}
			},
			Formula::IfThenElse { cond, then, els } => {
				let name = cond.bind(db, None)?;
				let mut cdb = db.with_conditions(vec![!name]);
				self.encode(&mut cdb, then)?;
				let mut cdb = db.with_conditions(vec![name]);
				self.encode(&mut cdb, els)
			}
		}
	}
}
