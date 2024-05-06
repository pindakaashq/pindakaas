use std::{fmt::Display, iter::once, ops::Not};

use itertools::{Itertools, Position};

use crate::{ClauseDatabase, Cnf, Encoder, Lit, Result, Unsatisfiable};

/// A propositional logic formula
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
	///A atomic formula (a literal)
	Atom(Lit),
	/// The negation of a sub-formula
	Not(Box<Formula>),
	/// A conjunction of two or more sub-formulas
	And(Vec<Formula>),
	/// A disjunction of two or more sub-formulas
	Or(Vec<Formula>),
	/// An implication of two sub-formulas
	Implies(Box<Formula>, Box<Formula>),
	/// The equivalence of two or more sub-formulas
	Equiv(Vec<Formula>),
	/// An exclusive or of two or more sub-formulas
	Xor(Vec<Formula>),
	/// A choice between two sub-formulas
	IfThenElse {
		cond: Box<Formula>,
		then: Box<Formula>,
		els: Box<Formula>,
	},
}

impl Formula {
	/// Convert propositional logic formula to CNF
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
					if *lit != name {
						db.add_clause([!name, *lit])?;
						db.add_clause([name, !lit])?;
					}
					name
				} else {
					*lit
				}
			}
			Formula::Not(f) => !(f.bind(db, name)?),
			Formula::And(sub) => {
				match sub.len() {
					0 => {
						let name = name.unwrap_or_else(|| db.new_var().into());
						db.add_clause([name])?;
						name
					}
					1 => return sub[0].bind(db, name),
					_ => {
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
				}
			}
			Formula::Or(sub) => {
				match sub.len() {
					0 => return Err(Unsatisfiable),
					1 => return sub[0].bind(db, name),
					_ => {
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
				}
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
					sub.len() >= 2,
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
				Formula::Implies(x, y) => {
					self.encode(db, x)?;
					self.encode(db, &!(**y).clone())
				}
				Formula::IfThenElse { cond, then, els } => {
					let name = cond.bind(db, None)?;
					let mut cdb = db.with_conditions(vec![!name]);
					let neg_then: Formula = !*then.clone();
					self.encode(&mut cdb, &neg_then)?;
					let mut cdb = db.with_conditions(vec![name]);
					let neg_els: Formula = !*els.clone();
					self.encode(&mut cdb, &neg_els)
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
				if sub.is_empty() {
					return Err(Unsatisfiable);
				}
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
				0 => Err(crate::Unsatisfiable),
				1 => self.encode(db, &sub[0]),
				_ => {
					let mut sub = sub.clone();
					let b = sub.pop().map(|f| f.bind(db, None)).unwrap()?;
					let a = if sub.len() > 1 {
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

#[cfg(test)]
mod tests {
	use crate::{
		helpers::tests::{assert_enc_sol, lits},
		Encoder, Formula, Lit, TseitinEncoder,
	};

	#[test]
	fn encode_prop_and() {
		assert_enc_sol!(
			TseitinEncoder,
			3,
			&Formula::And(vec![
				Formula::Atom(1.into()),
				Formula::Atom(2.into()),
				Formula::Atom(3.into()),
			])
			=> vec![lits![1], lits![2], lits![3]],
			vec![lits![1, 2, 3],]
		);
		assert_enc_sol!(
			TseitinEncoder,
			3,
			&Formula::Equiv(vec![
				Formula::Atom(3.into()),
					Formula::And(vec![
					Formula::Atom(1.into()),
					Formula::Atom(2.into()),
				])
			])
			=> vec![lits![-1, -2, 3], lits![1, -3], lits![2, -3]],
			vec![lits![1, 2, 3], lits![-1, 2, -3], lits![-1, -2, -3], lits![1, -2, -3]]
		);
	}

	#[test]
	fn encode_prop_or() {
		assert_enc_sol!(
			TseitinEncoder,
			3,
			&Formula::Or(vec![
				Formula::Atom(1.into()),
				Formula::Atom(2.into()),
				Formula::Atom(3.into()),
			])
			=> vec![lits![1, 2, 3]],
			vec![lits![1,2,3], lits![-1,2,3], lits![1,-2,3], lits![1,2,-3], lits![-1,-2,3], lits![1,-2,-3],lits![-1,2,-3],]
		);
		assert_enc_sol!(
			TseitinEncoder,
			3,
			&Formula::Equiv(vec![
				Formula::Atom(3.into()),
				Formula::Or(vec![
					Formula::Atom(1.into()),
					Formula::Atom(2.into()),
				])
			])
			=> vec![lits![1, 2, -3], lits![-1, 3], lits![-2, 3]],
			vec![lits![1, 2, 3], lits![-1, 2, 3], lits![-1, -2, -3], lits![1, -2, 3]]
		);
	}

	#[test]
	fn encode_prop_implies() {
		assert_enc_sol!(
			TseitinEncoder,
			2,
			&Formula::Implies(
				Box::new(Formula::Atom(1.into())),
				Box::new(Formula::Atom(2.into()))
			)
			=> vec![lits![-1, 2]],
			vec![lits![-1, -2], lits![1, 2], lits![-1, 2]]
		);
		assert_enc_sol!(
			TseitinEncoder,
			3,
			&Formula::Equiv(
				vec![
				Formula::Atom(3.into()),
				Formula::Implies(
					Box::new(Formula::Atom(1.into())),
					Box::new(Formula::Atom(2.into())),
				)]
			)
			=> vec![lits![-1, 2, -3], lits![1, 3], lits![-2, 3]],
			vec![lits![1, 2, 3], lits![1, -2, -3], lits![-1, -2, 3], lits![-1, 2, 3]]
		);
	}

	#[test]
	fn encode_prop_equiv() {
		assert_enc_sol!(
			TseitinEncoder,
			4,
			&Formula::Equiv(vec![
				Formula::Atom(1.into()),
				Formula::Atom(2.into()),
				Formula::Atom(3.into()),
				Formula::Atom(4.into())
			])
			=> vec![lits![-1, 2], lits![1, -2], lits![1, -3], lits![-1, 3], lits![1, -4], lits![-1, 4]],
			vec![lits![1, 2, 3, 4], lits![-1, -2, -3, -4]]
		);
		assert_enc_sol!(
			TseitinEncoder,
			3,
			&Formula::Equiv(vec![
				Formula::Atom(3.into()),
				Formula::Equiv(vec![
					Formula::Atom(1.into()),
					Formula::Atom(2.into()),
				])
			])
			=> vec![lits![-1, 2, -3], lits![1, -2, -3], lits![-1, -2, 3], lits![1, 2, 3]],
			vec![lits![1, 2, 3], lits![-1, 2, -3], lits![-1, -2, 3], lits![1, -2, -3]]
		);
	}

	#[test]
	fn encode_prop_xor() {
		assert_enc_sol!(
			TseitinEncoder,
			4,
			&Formula::Xor(vec![
				Formula::Atom(1.into()),
				Formula::Atom(2.into()),
				Formula::Atom(3.into()),
				Formula::Atom(4.into()),
			])
			=> vec![
				lits![-1, -3, -6], lits![1, 3, -6], lits![1, -3, 6], lits![-1, 3, 6],
				lits![-2, -5, -6], lits![2, -5, 6], lits![2, 5, -6], lits![-2, 5, 6],
				lits![4, 5], lits![-4, -5]],
			vec![lits![-1, 2, 3, 4], lits![1, -2, 3, 4], lits![1, 2, -3, 4], lits![1, 2, 3, -4], lits![-1, -2, -3, 4], lits![-1, -2, 3, -4], lits![-1, 2, -3, -4], lits![1, -2, -3, -4]]
		);
		assert_enc_sol!(
			TseitinEncoder,
			4,
			&Formula::Equiv(vec![
				Formula::Atom(4.into()),
				Formula::Xor(vec![
					Formula::Atom(1.into()),
					Formula::Atom(2.into()),
					Formula::Atom(3.into()),
				])
			])
			=> vec![lits![-1, -3, -5], lits![1, 3, -5], lits![-1, 3, 5], lits![1, -3, 5], lits![-2, -4, -5], lits![2, -4, 5], lits![2, 4, -5], lits![-2, 4, 5]],
			vec![lits![-1, -2, -3, -4], lits![-1, -2, 3, 4], lits![-1, 2, -3, 4], lits![-1, 2, 3, -4], lits![1, -2, -3, 4], lits![1, -2, 3, -4], lits![1, 2, -3, -4], lits![1, 2, 3, 4]]
		);
	}

	#[test]
	fn encode_prop_ite() {
		assert_enc_sol!(
			TseitinEncoder,
			3,
			&Formula::IfThenElse{
				cond: Box::new(Formula::Atom(1.into())),
				then: Box::new(Formula::Atom(2.into())),
				els: Box::new(Formula::Atom(3.into())),
			}
			=> vec![lits![-1, 2], lits![1, 3]],
			vec![lits![-1, -2, 3], lits![-1, 2, 3], lits![1, 2, -3], lits![1, 2, 3]]
		);
		assert_enc_sol!(
			TseitinEncoder,
			4,
			&Formula::Equiv(vec![
				Formula::Atom(4.into()),
				Formula::IfThenElse{
					cond: Box::new(Formula::Atom(1.into())),
					then: Box::new(Formula::Atom(2.into())),
					els: Box::new(Formula::Atom(3.into())),
				}
			])
			=> vec![lits![-1, 2, -4], lits![1, 3, -4], lits![-1, -2, 4], lits![1, -3, 4], lits![-2, -3, 4]],
			vec![lits![-1, -2, -3, -4], lits![-1, -2, 3, 4], lits![1, -2, 3, -4], lits![1, 2, 3, 4], lits![1, 2, -3, 4], lits![1, -2, -3, -4], lits![-1, 2, 3, 4], lits![-1, 2, -3, -4]]
		);
	}
}
