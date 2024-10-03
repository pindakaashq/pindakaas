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
			Formula::Not(f) => !(f.bind(db, name.map(|lit| !lit))?),
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
					0 => {
						let name = name.unwrap_or_else(|| db.new_var().into());
						db.add_clause([!name])?;
						name
					}
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
	use itertools::Itertools;

	use crate::{
		helpers::tests::{assert_encoding, assert_solutions, expect_file},
		solver::NextVarRange,
		ClauseDatabase, Cnf, Encoder, Formula, TseitinEncoder,
	};

	#[test]
	fn encode_prop_and() {
		// Simple conjunction
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::And(vec![Formula::Atom(a), Formula::Atom(b), Formula::Atom(c)]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_and.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c],
			&expect_file!["propositional_logic/encode_prop_and.sol"],
		);

		// Reified conjunction
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vec![
					Formula::Atom(c),
					Formula::And(vec![Formula::Atom(a), Formula::Atom(b)]),
				]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_and_reif.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c],
			&expect_file!["propositional_logic/encode_prop_and_reif.sol"],
		);

		// Regression test: empty and
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vec![Formula::Atom(a), Formula::And(vec![])]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_and_empty.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a],
			&expect_file!["propositional_logic/encode_prop_and_empty.sol"],
		);
	}

	#[test]
	fn encode_prop_or() {
		// Simple disjunction
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Or(vec![Formula::Atom(a), Formula::Atom(b), Formula::Atom(c)]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_or.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c],
			&expect_file!["propositional_logic/encode_prop_or.sol"],
		);

		// Reified disjunction
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vec![
					Formula::Atom(c),
					Formula::Or(vec![Formula::Atom(a), Formula::Atom(b)]),
				]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_or_reif.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c],
			&expect_file!["propositional_logic/encode_prop_or_reif.sol"],
		);

		// Regression test: empty or
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vec![Formula::Atom(a), Formula::Or(vec![])]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_or_empty.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a],
			&expect_file!["propositional_logic/encode_prop_or_empty.sol"],
		);
	}

	#[test]
	fn encode_prop_implies() {
		// Simple implication
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Implies(Box::new(Formula::Atom(a)), Box::new(Formula::Atom(b))),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_implies.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["propositional_logic/encode_prop_implies.sol"],
		);

		// Reified implication
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vec![
					Formula::Atom(c),
					Formula::Implies(Box::new(Formula::Atom(a)), Box::new(Formula::Atom(b))),
				]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_implies_reif.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c],
			&expect_file!["propositional_logic/encode_prop_implies_reif.sol"],
		);
	}

	#[test]
	fn encode_prop_equiv() {
		// Simple equivalence
		let mut cnf = Cnf::default();
		let vars = cnf.next_var_range(4).unwrap().iter_lits().collect_vec();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vars.iter().cloned().map(Formula::Atom).collect()),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_equiv.cnf"],
		);
		assert_solutions(
			&cnf,
			vars,
			&expect_file!["propositional_logic/encode_prop_equiv.sol"],
		);

		// Reified equivalence
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vec![
					Formula::Atom(c),
					Formula::Equiv(vec![Formula::Atom(a), Formula::Atom(b)]),
				]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_equiv_reif.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c],
			&expect_file!["propositional_logic/encode_prop_equiv_reif.sol"],
		);
	}

	#[test]
	fn encode_prop_xor() {
		// Simple XOR
		let mut cnf = Cnf::default();
		let vars = cnf.next_var_range(3).unwrap().iter_lits().collect_vec();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Xor(vars.iter().cloned().map(Formula::Atom).collect()),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_xor.cnf"],
		);
		assert_solutions(
			&cnf,
			vars,
			&expect_file!["propositional_logic/encode_prop_xor.sol"],
		);

		// Reified XOR
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf
			.next_var_range(4)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vec![
					Formula::Atom(d),
					Formula::Xor(vec![Formula::Atom(a), Formula::Atom(c), Formula::Atom(d)]),
				]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_xor_reif.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c, d],
			&expect_file!["propositional_logic/encode_prop_xor_reif.sol"],
		);
		// Regression test: negated XOR (into equiv)
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Not(Box::new(Formula::Xor(vec![
					Formula::Atom(a),
					Formula::Atom(b),
				]))),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_xor_neg1.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["propositional_logic/encode_prop_xor_neg1.sol"],
		);
		// Regression test: negated XOR (negated args)
		let mut cnf = Cnf::default();
		let vars = cnf.next_var_range(3).unwrap().iter_lits().collect_vec();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Not(Box::new(Formula::Xor(
					vars.iter().cloned().map(Formula::Atom).collect(),
				))),
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["propositional_logic/encode_prop_xor_neg2.sol"],
		);
		// Regression test: negated XOR (negated binding)
		let mut cnf = Cnf::default();
		let vars = cnf.next_var_range(4).unwrap().iter_lits().collect_vec();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Not(Box::new(Formula::Xor(
					vars.iter().cloned().map(Formula::Atom).collect(),
				))),
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["propositional_logic/encode_prop_xor_neg3.sol"],
		);
	}

	#[test]
	fn encode_prop_ite() {
		// Simple if-then-else
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf
			.next_var_range(3)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::IfThenElse {
					cond: Box::new(Formula::Atom(a)),
					then: Box::new(Formula::Atom(b)),
					els: Box::new(Formula::Atom(c)),
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_ite.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c],
			&expect_file!["propositional_logic/encode_prop_ite.sol"],
		);

		// Reified if-then-else
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf
			.next_var_range(4)
			.unwrap()
			.iter_lits()
			.collect_tuple()
			.unwrap();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vec![
					Formula::Atom(d),
					Formula::IfThenElse {
						cond: Box::new(Formula::Atom(a)),
						then: Box::new(Formula::Atom(b)),
						els: Box::new(Formula::Atom(c)),
					},
				]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_ite_reif.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c, d],
			&expect_file!["propositional_logic/encode_prop_ite_reif.sol"],
		);
	}

	#[test]
	fn encode_prop_neg_equiv() {
		// Regression test
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		TseitinEncoder
			.encode(
				&mut cnf,
				&Formula::Equiv(vec![
					Formula::Atom(b),
					Formula::Not(Box::new(Formula::Xor(vec![Formula::Atom(a)]))),
				]),
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_neg_equiv.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["propositional_logic/encode_prop_neg_equiv.sol"],
		);
	}
}
