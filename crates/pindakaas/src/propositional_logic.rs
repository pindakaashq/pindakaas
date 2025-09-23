//! This module contains representations and encoding algorithms for
//! propositional logic formulas.
//!
//! These formulas can be represented using the [`Formula`] type, which
//! implementation is specialized for both [`Lit`] and [`BoolVal`]. The
//! [`TseitinEncoder`] is can be used to encode formulas into CNF.

use std::{
	fmt::{self, Display, Formatter},
	iter::once,
	ops::{BitAnd, BitOr, BitXor, Not},
};

use itertools::{Itertools, Position};
use rustc_hash::FxHashSet;

use crate::{
	AsDynClauseDatabase, BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder, Lit, Result,
	Unsatisfiable,
};

/// A propositional logic formula
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Formula<Base> {
	/// A conjunction of two or more sub-formulas
	And(Vec<Formula<Base>>),
	///A atomic formula (a literal)
	Atom(Base),
	/// The equivalence of two or more sub-formulas
	Equiv(Vec<Formula<Base>>),
	/// A choice between two sub-formulas
	IfThenElse {
		/// The expression that determines which sub-formula is chosen:
		/// - If it evaluates to `true`, the `then` branch is chosen.
		/// - If it evaluates to `false`, the `els` branch is chosen.
		cond: Box<Formula<Base>>,
		/// The expression that is chosen when `cond` evaluates to `true`.
		then: Box<Formula<Base>>,
		/// The expression that is chosen when `cond` evaluates to `false`.
		els: Box<Formula<Base>>,
	},
	/// An implication of two sub-formulas
	Implies(Box<Formula<Base>>, Box<Formula<Base>>),
	/// The negation of a sub-formula
	Not(Box<Formula<Base>>),
	/// A disjunction of two or more sub-formulas
	Or(Vec<Formula<Base>>),
	/// An exclusive or of two or more sub-formulas
	Xor(Vec<Formula<Base>>),
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
/// An encoder for propositional logic formulas, based on the standard Tseitin
/// transformations.
pub struct TseitinEncoder;

impl<Base> Formula<Base> {
	/// Simplify the formula using a given resolver function.
	///
	/// The resolver function is called for each [`Self::Atom`] in the formula.
	/// The resolver function should return `Err(true)` if the atom is known to
	/// be true and `Err(false)` if the atom is known to be false. Otherwise,
	/// the resolver function should return the value of the atom for the
	/// simplified formula.
	pub fn simplify_with<Res>(
		self,
		resolver: &mut impl FnMut(Base) -> Result<Res, bool>,
	) -> Result<Formula<Res>, bool>
	where
		Self: Clone,
	{
		match self {
			Formula::And(sub) => {
				let sub: Vec<_> = sub
					.into_iter()
					.filter_map(|f| match f.simplify_with(resolver) {
						Err(true) => None,
						Err(false) => Some(Err(false)),
						Ok(f) => Some(Ok(f)),
					})
					.try_collect()?;
				match sub.len() {
					0 => Err(true),
					1 => Ok(sub.into_iter().next().unwrap()),
					_ => Ok(Formula::And(sub)),
				}
			}
			Formula::Atom(l) => match resolver(l) {
				Err(b) => Err(b),
				Ok(l) => Ok(Formula::Atom(l)),
			},
			Formula::Equiv(sub) => {
				let mut val = None;
				let mut nsub = Vec::with_capacity(sub.len());
				for f in sub {
					match f.simplify_with(resolver) {
						Err(b) => {
							if val.is_some() && val != Some(b) {
								return Err(false);
							}
							val = Some(b);
						}
						Ok(f) => nsub.push(f),
					}
				}
				Ok(match val {
					Some(true) => Formula::And(nsub),
					Some(false) => Formula::Not(Box::new(Formula::Or(nsub))),
					None => Formula::Equiv(nsub),
				})
			}
			Formula::IfThenElse { cond, then, els } => match cond.clone().simplify_with(resolver) {
				Err(true) => then.simplify_with(resolver),
				Err(false) => els.simplify_with(resolver),
				Ok(cond_lit) => match then.simplify_with(resolver) {
					Err(true) => {
						Self::Implies(Box::new(!*cond), Box::new(!*els)).simplify_with(resolver)
					}
					Err(false) => Self::And(vec![!*cond, !*els]).simplify_with(resolver),
					Ok(then_lit) => match els.simplify_with(resolver) {
						Err(true) => Ok(Formula::Implies(Box::new(cond_lit), Box::new(then_lit))),
						Err(false) => Ok(Formula::And(vec![cond_lit, !then_lit])),
						Ok(els_lit) => Ok(Formula::IfThenElse {
							cond: Box::new(cond_lit),
							then: Box::new(then_lit),
							els: Box::new(els_lit),
						}),
					},
				},
			},
			Formula::Implies(f, g) => match f.simplify_with(resolver) {
				Err(false) => Err(true),
				Err(true) => g.simplify_with(resolver),
				Ok(f) => match g.simplify_with(resolver) {
					Err(true) => Err(true),
					Err(false) => Ok(!f),
					Ok(g) => Ok(Formula::Implies(Box::new(f), Box::new(g))),
				},
			},
			Formula::Not(sub) => match sub.simplify_with(resolver) {
				Err(b) => Err(!b),
				Ok(f) => Ok(!f),
			},
			Formula::Or(sub) => {
				let sub: Vec<_> = sub
					.into_iter()
					.filter_map(|f| match f.simplify_with(resolver) {
						Err(true) => Some(Err(true)),
						Err(false) => None,
						Ok(f) => Some(Ok(f)),
					})
					.try_collect()?;
				match sub.len() {
					0 => Err(false),
					1 => Ok(sub.into_iter().next().unwrap()),
					_ => Ok(Formula::Or(sub)),
				}
			}
			Formula::Xor(sub) => {
				let mut count = 0;
				let sub = sub
					.into_iter()
					.filter_map(|f| match f.simplify_with(resolver) {
						Err(true) => {
							count += 1;
							None
						}
						Err(false) => None,
						Ok(f) => Some(f),
					})
					.collect_vec();
				match sub.len() {
					0 => Err(count % 2 == 1),
					1 => {
						let f = sub.into_iter().next().unwrap();
						Ok(if count % 2 == 1 { !f } else { f })
					}
					_ => {
						let f = Formula::Xor(sub);
						Ok(if count % 2 == 1 { !f } else { f })
					}
				}
			}
		}
	}
}

impl<Base: Display> Formula<Base> {
	fn fmt_inner(&self, f: &mut Formatter<'_>, sub: bool) -> fmt::Result {
		if let Formula::Atom(l) = self {
			return write!(f, "{l}");
		}
		if sub {
			write!(f, "(")?;
		}
		match self {
			Formula::Not(sub) => {
				write!(f, "¬")?;
				sub.fmt_inner(f, true)?;
			}
			Formula::And(sub) => {
				for (i, x) in sub.iter().enumerate() {
					if i > 0 {
						write!(f, " ∧ ")?;
					}
					x.fmt_inner(f, true)?;
				}
			}
			Formula::Or(sub) => {
				for (i, x) in sub.iter().enumerate() {
					if i > 0 {
						write!(f, " ∨ ")?;
					}
					x.fmt_inner(f, true)?;
				}
			}
			Formula::Implies(x, y) => {
				x.fmt_inner(f, true)?;
				write!(f, " → ")?;
				y.fmt_inner(f, true)?;
			}
			Formula::Equiv(sub) => {
				for (i, x) in sub.iter().enumerate() {
					if i > 0 {
						write!(f, " ≡ ")?;
					}
					x.fmt_inner(f, true)?;
				}
			}
			Formula::Xor(sub) => {
				for (i, x) in sub.iter().enumerate() {
					if i > 0 {
						write!(f, " ⊻ ")?;
					}
					x.fmt_inner(f, true)?;
				}
			}
			Formula::IfThenElse { cond, then, els } => {
				write!(f, "if ")?;
				cond.fmt_inner(f, sub)?;
				write!(f, " then ")?;
				then.fmt_inner(f, sub)?;
				write!(f, " else ")?;
				els.fmt_inner(f, sub)?;
				write!(f, " endif")?;
			}
			Formula::Atom(_) => unreachable!(),
		}
		if sub {
			write!(f, ")")?;
		}
		Ok(())
	}
}

impl Formula<BoolVal> {
	/// Resolve the constant values in the formula.
	///
	/// If the formula is known to be unsatisfiable, then `Err(false)` is
	/// returned. If the formula is already satisfied, then `Err(true)` is
	/// returned. Otherwise, a simplified formula without any constant values is
	/// returned.
	pub fn resolve(self) -> Result<Formula<Lit>, bool> {
		self.simplify_with(&mut |l| match l {
			BoolVal::Const(b) => Err(b),
			BoolVal::Lit(l) => Ok(l),
		})
	}
	/// Simplify the formula using the given literals as proven facts.
	pub fn simplify<Iter>(self, facts: Iter) -> Result<Formula<Lit>, bool>
	where
		Iter: IntoIterator,
		Iter::Item: Into<Lit>,
	{
		let knowledge: FxHashSet<_> = facts.into_iter().map_into().collect();
		self.simplify_with(&mut |l| match l {
			BoolVal::Const(b) => Err(b),
			BoolVal::Lit(l) if knowledge.contains(&l) => Err(true),
			BoolVal::Lit(l) if knowledge.contains(&!l) => Err(false),
			BoolVal::Lit(l) => Ok(l),
		})
	}
}

impl Formula<Lit> {
	/// Helper function to bind the (sub) formula to a name (literal) for the
	/// tseitin encoding.
	fn bind<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db, name: Option<Lit>) -> Result<Lit> {
		Ok(match self {
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
						let lits: Vec<_> = sub.iter().map(|f| f.bind(db, None)).try_collect()?;
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
					1 => return sub[0].bind(db, name),
					_ => {
						let name = name.unwrap_or_else(|| db.new_var().into());
						let lits: Vec<_> = sub.iter().map(|f| f.bind(db, None)).try_collect()?;
						for &lit in &lits {
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
				for (x, y) in lits.iter().copied().tuple_windows() {
					// name -> (x <-> y)
					db.add_clause([!name, !x, y])?;
					db.add_clause([!name, x, !y])?;
				}
				db.add_clause(once(name).chain(lits.iter().map(|&l| !l)))?;
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

	/// Convert propositional logic formula to CNF
	pub fn clausify(&self) -> Result<Cnf> {
		let mut cnf = Cnf::default();
		cnf.encode(self, &TseitinEncoder)?;
		Ok(cnf)
	}

	/// Simplify the formula using the given literals as proven facts.
	pub fn simplify<Iter>(self, facts: Iter) -> Result<Formula<Lit>, bool>
	where
		Iter: IntoIterator,
		Iter::Item: Into<Lit>,
	{
		let knowledge: FxHashSet<_> = facts.into_iter().map_into().collect();
		self.simplify_with(&mut |l| {
			if knowledge.contains(&l) {
				Err(true)
			} else if knowledge.contains(&!l) {
				Err(false)
			} else {
				Ok(l)
			}
		})
	}
}

impl BitAnd<BoolVal> for Formula<BoolVal> {
	type Output = Self;

	fn bitand(self, rhs: BoolVal) -> Self {
		match rhs {
			BoolVal::Const(false) => Self::Atom(false.into()),
			BoolVal::Const(true) => self,
			BoolVal::Lit(lit) => self & Formula::Atom(BoolVal::Lit(lit)),
		}
	}
}

impl BitAnd<Lit> for Formula<BoolVal> {
	type Output = Self;

	fn bitand(self, rhs: Lit) -> Self {
		self & BoolVal::Lit(rhs)
	}
}

impl BitAnd<Lit> for Formula<Lit> {
	type Output = Self;

	fn bitand(self, rhs: Lit) -> Self {
		self & Formula::Atom(rhs)
	}
}

impl<Base> BitAnd<Self> for Formula<Base> {
	type Output = Self;

	fn bitand(self, rhs: Self) -> Self {
		match (self, rhs) {
			(Formula::And(mut sub), Formula::And(rhs)) => {
				sub.extend(rhs);
				Formula::And(sub)
			}
			(Formula::And(mut sub), x) | (x, Formula::And(mut sub)) => {
				sub.push(x);
				Formula::And(sub)
			}
			(lhs, rhs) => Formula::And(vec![lhs, rhs]),
		}
	}
}

impl BitAnd<bool> for Formula<BoolVal> {
	type Output = Self;

	fn bitand(self, rhs: bool) -> Self {
		self & BoolVal::Const(rhs)
	}
}

impl BitAnd<bool> for Formula<Lit> {
	type Output = Self;

	fn bitand(self, rhs: bool) -> Self {
		if rhs {
			self
		} else {
			Self::Or(vec![])
		}
	}
}

impl BitOr<BoolVal> for Formula<BoolVal> {
	type Output = Self;

	fn bitor(self, rhs: BoolVal) -> Self {
		match rhs {
			BoolVal::Const(true) => Self::Atom(true.into()),
			BoolVal::Const(false) => self,
			BoolVal::Lit(lit) => self | Formula::Atom(BoolVal::Lit(lit)),
		}
	}
}

impl BitOr<Lit> for Formula<BoolVal> {
	type Output = Self;

	fn bitor(self, rhs: Lit) -> Self {
		self | BoolVal::Lit(rhs)
	}
}

impl BitOr<Lit> for Formula<Lit> {
	type Output = Self;

	fn bitor(self, rhs: Lit) -> Self {
		self | Formula::Atom(rhs)
	}
}

impl<Base> BitOr<Self> for Formula<Base> {
	type Output = Self;

	fn bitor(self, rhs: Self) -> Self {
		match (self, rhs) {
			(Formula::Or(mut sub), Formula::Or(rhs)) => {
				sub.extend(rhs);
				Formula::Or(sub)
			}
			(Formula::Or(mut sub), x) | (x, Formula::Or(mut sub)) => {
				sub.push(x);
				Formula::Or(sub)
			}
			(lhs, rhs) => Formula::Or(vec![lhs, rhs]),
		}
	}
}

impl BitOr<bool> for Formula<BoolVal> {
	type Output = Self;

	fn bitor(self, rhs: bool) -> Self {
		self | BoolVal::Const(rhs)
	}
}

impl BitOr<bool> for Formula<Lit> {
	type Output = Self;

	fn bitor(self, rhs: bool) -> Self {
		if rhs {
			Self::And(vec![])
		} else {
			self
		}
	}
}

impl BitXor<BoolVal> for Formula<BoolVal> {
	type Output = Self;

	fn bitxor(self, rhs: BoolVal) -> Self {
		match rhs {
			BoolVal::Const(false) => self,
			BoolVal::Const(true) => !self,
			BoolVal::Lit(lit) => self ^ Formula::Atom(BoolVal::Lit(lit)),
		}
	}
}

impl BitXor<Lit> for Formula<BoolVal> {
	type Output = Self;

	fn bitxor(self, rhs: Lit) -> Self {
		self ^ BoolVal::Lit(rhs)
	}
}

impl BitXor<Lit> for Formula<Lit> {
	type Output = Self;

	fn bitxor(self, rhs: Lit) -> Self {
		self ^ Formula::Atom(rhs)
	}
}

impl<Base> BitXor<Self> for Formula<Base> {
	type Output = Self;

	fn bitxor(self, rhs: Self) -> Self {
		match (self, rhs) {
			(Formula::Xor(mut sub), Formula::Xor(rhs)) => {
				sub.extend(rhs);
				Formula::Xor(sub)
			}
			(Formula::Xor(mut sub), x) | (x, Formula::Xor(mut sub)) => {
				sub.push(x);
				Formula::Xor(sub)
			}
			(lhs, rhs) => Formula::Xor(vec![lhs, rhs]),
		}
	}
}

impl BitXor<bool> for Formula<BoolVal> {
	type Output = Self;

	fn bitxor(self, rhs: bool) -> Self {
		self ^ BoolVal::Const(rhs)
	}
}

impl BitXor<bool> for Formula<Lit> {
	type Output = Self;

	fn bitxor(self, rhs: bool) -> Self {
		if rhs {
			!self
		} else {
			self
		}
	}
}

impl<Base: Display> Display for Formula<Base> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		self.fmt_inner(f, false)
	}
}

impl From<Formula<Lit>> for Formula<BoolVal> {
	fn from(value: Formula<Lit>) -> Self {
		match value {
			Formula::And(sub) => Self::And(sub.into_iter().map_into().collect()),
			Formula::Atom(lit) => Self::Atom(lit.into()),
			Formula::Equiv(sub) => Self::Equiv(sub.into_iter().map_into().collect()),
			Formula::IfThenElse { cond, then, els } => Self::IfThenElse {
				cond: Box::new((*cond).into()),
				then: Box::new((*then).into()),
				els: Box::new((*els).into()),
			},
			Formula::Implies(f, g) => Self::Implies(Box::new((*f).into()), Box::new((*g).into())),
			Formula::Not(f) => {
				let f: Self = (*f).into();
				!f
			}
			Formula::Or(sub) => Self::Or(sub.into_iter().map_into().collect()),
			Formula::Xor(sub) => Self::Xor(sub.into_iter().map_into().collect()),
		}
	}
}

impl<Base> Not for Formula<Base> {
	type Output = Formula<Base>;

	fn not(self) -> Self {
		match self {
			Formula::Not(f) => *f,
			_ => Formula::Not(Box::new(self)),
		}
	}
}

impl<Db> Encoder<Db, Formula<BoolVal>> for TseitinEncoder
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
{
	fn encode(&self, db: &mut Db, con: &Formula<BoolVal>) -> Result {
		match con.clone().resolve() {
			Err(false) => Err(Unsatisfiable),
			Err(true) => Ok(()),
			Ok(con) => self.encode(db, &con),
		}
	}
}

impl<Db> Encoder<Db, Formula<Lit>> for TseitinEncoder
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
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
					let name = cond.bind(db, None)?;
					{
						let mut cdb = db.with_conditions(vec![!name]);
						let neg_then: Formula<Lit> = !*then.clone();
						self.encode(&mut cdb, &neg_then)?;
					}
					let mut cdb = db.with_conditions(vec![name]);
					let neg_els: Formula<Lit> = !*els.clone();
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
				self.encode(&mut cdb, right.as_ref())
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
				0 => Err(Unsatisfiable),
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
				{
					let mut cdb = db.with_conditions(vec![!name]);
					self.encode(&mut cdb, then.as_ref())?;
				}
				let mut cdb = db.with_conditions(vec![name]);
				self.encode(&mut cdb, els.as_ref())
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;

	use crate::{
		helpers::tests::{assert_encoding, assert_solutions, expect_file},
		propositional_logic::{Formula, TseitinEncoder},
		ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder,
	};

	#[test]
	fn encode_prop_and() {
		// Simple conjunction
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		TseitinEncoder.encode(&mut cnf, &(a & b & c)).unwrap();

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
		let (a, b, c) = cnf.new_lits();
		TseitinEncoder
			.encode(&mut cnf, &Formula::Equiv(vec![Formula::Atom(c), a & b]))
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
	fn encode_prop_equiv() {
		// Simple equivalence
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(4).iter_lits().collect_vec();
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
		let (a, b, c) = cnf.new_lits();
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
		let (a, b, c) = cnf.new_lits();
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
	fn encode_prop_ite() {
		// Simple if-then-else
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
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
		let (a, b, c, d) = cnf.new_lits();
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

	#[test]
	fn encode_prop_or() {
		// Simple disjunction
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		TseitinEncoder.encode(&mut cnf, &(a | b | c)).unwrap();

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
		let (a, b, c) = cnf.new_lits();
		TseitinEncoder
			.encode(&mut cnf, &Formula::Equiv(vec![Formula::Atom(c), a | b]))
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
	fn encode_prop_xor() {
		// Simple XOR
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		TseitinEncoder.encode(&mut cnf, &(a ^ b ^ c)).unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["propositional_logic/encode_prop_xor.cnf"],
		);
		assert_solutions(
			&cnf,
			[a, b, c],
			&expect_file!["propositional_logic/encode_prop_xor.sol"],
		);

		// Reified XOR
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		TseitinEncoder
			.encode(&mut cnf, &Formula::Equiv(vec![Formula::Atom(d), a ^ b ^ c]))
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
		let (a, b) = cnf.new_lits();
		TseitinEncoder.encode(&mut cnf, &(!(a ^ b))).unwrap();

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
		let (a, b, c) = cnf.new_lits();
		TseitinEncoder.encode(&mut cnf, &(!(a ^ b ^ c))).unwrap();

		assert_solutions(
			&cnf,
			[a, b, c],
			&expect_file!["propositional_logic/encode_prop_xor_neg2.sol"],
		);
		// Regression test: negated XOR (negated binding)
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		TseitinEncoder
			.encode(&mut cnf, &(!(a ^ b ^ c ^ d)))
			.unwrap();

		assert_solutions(
			&cnf,
			[a, b, c, d],
			&expect_file!["propositional_logic/encode_prop_xor_neg3.sol"],
		);
	}
}
