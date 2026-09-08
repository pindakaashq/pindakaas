//! The Tseitin transformation: naming each subformula with a literal, and
//! stating what makes that literal hold.

use std::iter::once;

use itertools::Itertools;

use crate::{
	constraint::propositional_logic::Formula, BoolVal, ClauseDatabase, ClauseDatabaseTools,
	Encoder, Lit, Result,
};

#[derive(Default, Debug, Clone, PartialEq, Eq)]
/// Tseitin encoding with one representative literal per compound sub-formula.
///
/// # Examples
///
/// ```rust
/// use pindakaas::{
///     constraint::propositional_logic::{Formula, TseitinEncoder},
///     ClauseDatabaseTools, Cnf,
/// };
/// let mut cnf = Cnf::default();
/// let (x, y, z) = cnf.new_lits();
/// let formula = (Formula::Atom(x) & y) | z;
/// cnf.encode(&formula, &TseitinEncoder)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
pub struct TseitinEncoder;

impl<Db> Encoder<Db, Formula<BoolVal>> for TseitinEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	fn encode(&self, db: &mut Db, con: &Formula<BoolVal>) -> Result {
		match con.clone().resolve() {
			Err(false) => {
				db.contradiction()?;
				unreachable!();
			}
			Err(true) => Ok(()),
			Ok(con) => self.encode(db, &con),
		}
	}
}

impl<Db> Encoder<Db, Formula<Lit>> for TseitinEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	fn encode(&self, db: &mut Db, f: &Formula<Lit>) -> Result {
		match f {
			Formula::Atom(l) => db.add_clause([*l]),
			Formula::Not(f) => match f.as_ref() {
				&Formula::Atom(l) => db.add_clause([!l]),
				Formula::Not(f) => self.encode(db, f.as_ref()),
				Formula::And(sub) => {
					let neg_sub = sub.iter().map(|f| !(f.clone())).collect();
					self.encode(db, &Formula::Or(neg_sub))
				}
				Formula::Or(sub) => {
					let neg_sub = sub.iter().map(|f| !(f.clone())).collect();
					self.encode(db, &Formula::And(neg_sub))
				}
				Formula::Implies(x, y) => {
					self.encode(db, x.as_ref())?;
					self.encode(db, &!y.as_ref().clone())
				}
				Formula::IfThenElse { cond, then, els } => {
					let name = bind(cond, db, None)?;
					let neg_then: Formula<Lit> = !*then.clone();
					db.encode_implied(&[name], &neg_then, self)?;
					let neg_els: Formula<Lit> = !*els.clone();
					db.encode_implied(&[!name], &neg_els, self)
				}
				Formula::Equiv(sub) if sub.len() == 2 => {
					self.encode(db, &Formula::Xor(sub.clone()))
				}
				Formula::Xor(sub) if sub.len() == 2 => {
					self.encode(db, &Formula::Equiv(sub.clone()))
				}
				Formula::Xor(sub) if sub.len() % 2 != 0 => {
					let neg_sub = sub.iter().map(|f| !(f.clone())).collect();
					self.encode(db, &Formula::Xor(neg_sub))
				}
				_ => {
					let l = bind(f, db, None)?;
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
				if sub.is_empty() {
					db.contradiction()?;
					unreachable!();
				}
				let lits = sub
					.iter()
					.map(|f| bind(f, db, None))
					.collect::<Result<Vec<_>, _>>()?;
				db.add_clause(lits)
			}
			Formula::Implies(left, right) => {
				let x = bind(left, db, None)?;
				db.encode_implied(&[x], right.as_ref(), self)
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
							name = Some(bind(f, db, name)?);
						}
					}
				}
				Ok(())
			}
			Formula::Xor(sub) => match sub.len() {
				0 => {
					db.contradiction()?;
					unreachable!()
				}
				1 => self.encode(db, &sub[0]),
				_ => {
					let mut sub = sub.clone();
					let b = sub.pop().map(|f| bind(&f, db, None)).unwrap()?;
					let a = if sub.len() > 1 {
						bind(&Formula::Xor(sub), db, None)
					} else {
						sub.pop().map(|f| bind(&f, db, None)).unwrap()
					}?;
					db.add_clause([a, b])?;
					db.add_clause([!a, !b])
				}
			},
			Formula::IfThenElse { cond, then, els } => {
				let name = bind(cond, db, None)?;
				db.encode_implied(&[name], then.as_ref(), self)?;
				db.encode_implied(&[!name], els.as_ref(), self)
			}
		}
	}
}

fn bind<Db: ClauseDatabase + ?Sized>(
	formula: &Formula<Lit>,
	db: &mut Db,
	name: Option<Lit>,
) -> Result<Lit> {
	Ok(match formula {
		Formula::Atom(lit) => {
			if let Some(name) = name {
				if *lit != name {
					db.add_clause([!name, *lit])?;
					db.add_clause([name, !*lit])?;
				}
				name
			} else {
				*lit
			}
		}
		Formula::Not(f) => !(bind(f, db, name.map(|lit| !lit))?),
		Formula::And(sub) => {
			match sub.len() {
				0 => {
					let name = name.unwrap_or_else(|| db.new_var().into());
					db.add_clause([name])?;
					name
				}
				1 => return bind(&sub[0], db, name),
				_ => {
					let name = name.unwrap_or_else(|| db.new_var().into());
					let lits: Vec<_> = sub.iter().map(|f| bind(f, db, None)).try_collect()?;
					// not name -> (not lits[0] or not lits[1] or ...)
					db.add_clause(once(name).chain(lits.iter().map(|&l| !l)))?;
					for lit in lits {
						// name -> lit
						db.add_clause([!name, lit])?;
					}
					name
				}
			}
		}
		Formula::Or(sub) => {
			match sub.len() {
				0 => {
					let name = name.unwrap_or_else(|| db.new_var().into());
					db.add_clause([!name])?;
					name
				}
				1 => return bind(&sub[0], db, name),
				_ => {
					let name = name.unwrap_or_else(|| db.new_var().into());
					let lits: Vec<_> = sub.iter().map(|f| bind(f, db, None)).try_collect()?;
					for &lit in &lits {
						// not name -> not lit
						db.add_clause([name, !lit])?;
					}
					// name -> (lit[0] or lit[1] or ...)
					db.add_clause(once(!name).chain(lits))?;
					name
				}
			}
		}
		Formula::Implies(left, right) => {
			let name = name.unwrap_or_else(|| db.new_var().into());
			let left = bind(left, db, None)?;
			let right = bind(right, db, None)?;
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
				sub.len() >= 2,
				"unable to bind the equivalence of less than 2 formulas"
			);
			let name = name.unwrap_or_else(|| db.new_var().into());
			let lits = sub
				.iter()
				.map(|f| bind(f, db, None))
				.collect::<Result<Vec<_>>>()?;
			for (x, y) in lits.iter().copied().tuple_windows() {
				// name -> (x <-> y)
				db.add_clause([!name, !x, y])?;
				db.add_clause([!name, x, !y])?;
			}
			db.add_clause(once(name).chain(lits.iter().map(|&l| !l)))?;
			db.add_clause(once(name).chain(lits))?;
			name
		}
		Formula::Xor(sub) => {
			assert_ne!(sub.len(), 0, "unable to bind empty xor formula");
			if sub.len() == 1 {
				return bind(&sub[0], db, name);
			}
			let name = name.unwrap_or_else(|| db.new_var().into());
			let mut lits = sub
				.iter()
				.map(|f| bind(f, db, None))
				.collect::<Result<Vec<_>>>()?;

			let mut left = lits.pop().unwrap();
			for (pos, right) in lits.into_iter().with_position() {
				let new_name = if pos.is_last() {
					name
				} else {
					db.new_var().into()
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
			let cond = bind(cond, db, None)?;
			let then = bind(then, db, None)?;
			let els = bind(els, db, None)?;
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
