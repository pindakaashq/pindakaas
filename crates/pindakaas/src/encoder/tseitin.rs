//! The Tseitin transformation: naming compound subformulas with literals [^1].
//!
//! Clauses state what makes each representative hold, avoiding the exponential
//! expansion of distributing formulas into CNF.
//!
//! [^1]: G. S. Tseitin, "On the complexity of derivation in propositional
//! calculus", Studies in Constructive Mathematics and Mathematical Logic, Part
//! II (1968) 115–125.

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
		Formula::And(sub) => match sub.len() {
			0 => {
				let name = name.unwrap_or_else(|| db.new_var().into());
				db.add_clause([name])?;
				name
			}
			1 => return bind(&sub[0], db, name),
			_ => {
				let name = name.unwrap_or_else(|| db.new_var().into());
				let lits: Vec<_> = sub.iter().map(|f| bind(f, db, None)).try_collect()?;
				db.add_clause(once(name).chain(lits.iter().map(|&l| !l)))?;
				for lit in lits {
					db.add_clause([!name, lit])?;
				}
				name
			}
		},
		Formula::Or(sub) => match sub.len() {
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
					db.add_clause([name, !lit])?;
				}
				db.add_clause(once(!name).chain(lits))?;
				name
			}
		},
		Formula::Implies(left, right) => {
			let name = name.unwrap_or_else(|| db.new_var().into());
			let left = bind(left, db, None)?;
			let right = bind(right, db, None)?;
			db.add_clause([!name, !left, right])?;
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
				db.add_clause([!new_name, !left, !right])?;
				db.add_clause([!new_name, left, right])?;
				db.add_clause([new_name, !left, right])?;
				db.add_clause([new_name, left, !right])?;

				left = new_name;
			}
			name
		}
		Formula::IfThenElse { cond, then, els } => {
			let name = name.unwrap_or_else(|| db.new_var().into());
			let cond = bind(cond, db, None)?;
			let then = bind(then, db, None)?;
			let els = bind(els, db, None)?;
			db.add_clause([!name, !cond, then])?;
			db.add_clause([!name, cond, els])?;

			db.add_clause([name, !cond, !then])?;
			db.add_clause([name, cond, !els])?;
			db.add_clause([name, !then, !els])?;

			name
		}
	})
}

impl TseitinEncoder {
	/// Encode `condition → f` where every literal of `conditions` holds.
	fn encode_implied_by<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		condition: Lit,
		f: &Formula<Lit>,
		conditions: &mut Vec<Lit>,
	) -> Result {
		conditions.push(condition);
		let result = self.encode_under(db, f, conditions);
		let _ = conditions.pop();
		result
	}

	/// Encode `f` where every literal of `conditions` holds, as a clause that
	/// states it holding unless one of them is false.
	///
	/// Only the clauses that state `f` take the negated conditions; the clauses
	/// [`bind`] adds define fresh literals and hold whatever the conditions
	/// are. A contradiction under conditions falsifies one of them.
	fn encode_under<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		f: &Formula<Lit>,
		conditions: &mut Vec<Lit>,
	) -> Result {
		match f {
			Formula::Atom(l) => Self::state(db, conditions, [*l]),
			Formula::Not(f) => match f.as_ref() {
				&Formula::Atom(l) => Self::state(db, conditions, [!l]),
				Formula::Not(f) => self.encode_under(db, f.as_ref(), conditions),
				Formula::And(sub) => {
					let neg_sub = sub.iter().map(|f| !(f.clone())).collect();
					self.encode_under(db, &Formula::Or(neg_sub), conditions)
				}
				Formula::Or(sub) => {
					let neg_sub = sub.iter().map(|f| !(f.clone())).collect();
					self.encode_under(db, &Formula::And(neg_sub), conditions)
				}
				Formula::Implies(x, y) => {
					self.encode_under(db, x.as_ref(), conditions)?;
					self.encode_under(db, &!y.as_ref().clone(), conditions)
				}
				Formula::IfThenElse { cond, then, els } => {
					let name = bind(cond, db, None)?;
					let neg_then: Formula<Lit> = !*then.clone();
					self.encode_implied_by(db, name, &neg_then, conditions)?;
					let neg_els: Formula<Lit> = !*els.clone();
					self.encode_implied_by(db, !name, &neg_els, conditions)
				}
				Formula::Equiv(sub) if sub.len() == 2 => {
					self.encode_under(db, &Formula::Xor(sub.clone()), conditions)
				}
				Formula::Xor(sub) if sub.len() == 2 => {
					self.encode_under(db, &Formula::Equiv(sub.clone()), conditions)
				}
				Formula::Xor(sub) if sub.len() % 2 != 0 => {
					let neg_sub = sub.iter().map(|f| !(f.clone())).collect();
					self.encode_under(db, &Formula::Xor(neg_sub), conditions)
				}
				_ => {
					let l = bind(f, db, None)?;
					Self::state(db, conditions, [!l])
				}
			},
			Formula::And(sub) => {
				for f in sub {
					self.encode_under(db, f, conditions)?;
				}
				Ok(())
			}
			Formula::Or(sub) => {
				let lits = sub
					.iter()
					.map(|f| bind(f, db, None))
					.collect::<Result<Vec<_>, _>>()?;
				Self::state(db, conditions, lits)
			}
			Formula::Implies(left, right) => {
				let x = bind(left, db, None)?;
				self.encode_implied_by(db, x, right.as_ref(), conditions)
			}
			Formula::Equiv(sub) => {
				match sub.len() {
					0 => return Ok(()),
					1 => return self.encode_under(db, &sub[0], conditions),
					_ if conditions.is_empty() => {
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
					_ => {
						// One shared name would state the equivalence in a
						// definition, so each side is bound on its own.
						let lits = sub
							.iter()
							.map(|f| bind(f, db, None))
							.collect::<Result<Vec<_>, _>>()?;
						for &l in &lits[1..] {
							Self::state(db, conditions, [!lits[0], l])?;
							Self::state(db, conditions, [lits[0], !l])?;
						}
					}
				}
				Ok(())
			}
			Formula::Xor(sub) => match sub.len() {
				0 => Self::state(db, conditions, []),
				1 => self.encode_under(db, &sub[0], conditions),
				_ => {
					let mut sub = sub.clone();
					let b = sub.pop().map(|f| bind(&f, db, None)).unwrap()?;
					let a = if sub.len() > 1 {
						bind(&Formula::Xor(sub), db, None)
					} else {
						sub.pop().map(|f| bind(&f, db, None)).unwrap()
					}?;
					Self::state(db, conditions, [a, b])?;
					Self::state(db, conditions, [!a, !b])
				}
			},
			Formula::IfThenElse { cond, then, els } => {
				let name = bind(cond, db, None)?;
				self.encode_implied_by(db, name, then.as_ref(), conditions)?;
				self.encode_implied_by(db, !name, els.as_ref(), conditions)
			}
		}
	}

	/// Add `clause` where every literal of `conditions` holds, which without
	/// conditions is a contradiction where `clause` is empty.
	fn state<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		conditions: &[Lit],
		clause: impl IntoIterator<Item = Lit>,
	) -> Result {
		db.add_clause(conditions.iter().map(|&c| !c).chain(clause))
	}
}

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
		self.encode_under(db, f, &mut Vec::new())
	}
}
