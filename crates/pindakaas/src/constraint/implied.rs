//! A constraint that holds only where a condition does, `r → C`, and the
//! building blocks its encoders share.
//!
//! An encoder of an [`Implied`] constraint adds the negated condition only to
//! the clauses that state the constraint. Clauses that define an auxiliary
//! literal, or an encoding of an [`IntVar`](crate::decision::integer::IntVar),
//! hold whatever the condition is, and are added as they are.
//!
//! [`LinearEncoder`](crate::constraint::linear::LinearEncoder) takes a
//! condition that is a [`BoolVal`], where a constant condition leaves the
//! constraint or nothing. The encoders of normalized constraints take a
//! [`Lit`].

use crate::{BoolVal, ClauseDatabase, ClauseDatabaseTools, Lit, Result, Unsatisfiable, VarRange};

/// A database that adds the negated condition to every clause, and reports a
/// contradiction for its caller to turn into the negated condition. Without a
/// condition it adds every clause as it is.
///
/// For an encoding whose every clause states the constraint or defines a
/// literal of its own. It must not see a clause that defines an encoding of
/// an [`IntVar`](crate::decision::integer::IntVar), which other constraints
/// share.
pub(crate) struct ConditionalClauses<'a, Db: ?Sized> {
	db: &'a mut Db,
	condition: Option<Lit>,
	/// The clause being added, kept to reuse its allocation.
	clause: Vec<Lit>,
}

/// A database that turns a contradiction into the negated condition, and adds
/// every other clause as it is.
pub(crate) struct ConditionalContradiction<'a, Db: ?Sized> {
	db: &'a mut Db,
	condition: Lit,
	/// Whether a contradiction has added the negated condition.
	contradicted: bool,
}

/// Which clauses of a ternary constraint take the negated condition.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Conditioned {
	/// Every clause, for a constraint whose terms someone else defines.
	All(Lit),
	/// Only a clause that rules out the last term passing its domain, for a
	/// piece of a decomposition that defines its last term: whatever the
	/// others take, the last term has a value that meets every other clause.
	Overflow(Lit),
}

/// The constraint `condition → constraint`, where the condition is a `B`: a
/// [`BoolVal`] as written, or a [`Lit`] once a constant has been settled.
///
/// # Examples
///
/// ```rust
/// use pindakaas::{
///     constraint::linear::{Comparator, LinearEncoder, Linear, TotalizerEncoder},
///     decision::integer::IntVar,
///     ClauseDatabaseTools, Cnf, Encoder,
/// };
///
/// let mut cnf = Cnf::default();
/// let r = cnf.new_lit();
/// let (x, y) = (IntVar::new(0..=3), IntVar::new(0..=3));
/// let con = Linear::new(x + y, Comparator::LessEq, 2).implied_by(r);
/// LinearEncoder::<TotalizerEncoder>::default().encode(&mut cnf, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Clone, Debug)]
pub struct Implied<C, B = BoolVal> {
	condition: B,
	constraint: C,
}

/// The literal a clause takes to hold where `condition` does not, or false
/// without a condition.
pub(crate) fn negated(condition: Option<Lit>) -> BoolVal {
	condition.map_or(BoolVal::Const(false), |r| BoolVal::Lit(!r))
}

impl<'a, Db: ?Sized> ConditionalClauses<'a, Db> {
	/// Add the negated `condition` to every clause added to `db`.
	pub(crate) fn new(db: &'a mut Db, condition: Lit) -> Self {
		Self::optional(db, Some(condition))
	}

	/// Add the negated `condition` to every clause added to `db`, if there is
	/// a condition.
	pub(crate) fn optional(db: &'a mut Db, condition: Option<Lit>) -> Self {
		Self {
			db,
			condition,
			clause: Vec::new(),
		}
	}
}

impl<Db: ClauseDatabase + ?Sized> ClauseDatabase for ConditionalClauses<'_, Db> {
	fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result {
		let Some(condition) = self.condition else {
			return self.db.add_clause_from_slice(clause);
		};
		if clause.is_empty() {
			return Err(Unsatisfiable);
		}
		self.clause.clear();
		self.clause.push(!condition);
		self.clause.extend_from_slice(clause);
		self.db.add_clause_from_slice(&self.clause)
	}

	fn new_var_range(&mut self, len: usize) -> VarRange {
		self.db.new_var_range(len)
	}
}

impl<Db: ClauseDatabase + ?Sized> ConditionalContradiction<'_, Db> {
	/// Finish an encoding run on this database, where a failure falsifies the
	/// condition.
	pub(crate) fn conclude(self, result: Result) -> Result {
		match result {
			Ok(()) => Ok(()),
			// The contradiction has already added the negated condition.
			Err(Unsatisfiable) if self.contradicted => Ok(()),
			Err(Unsatisfiable) => self.db.add_clause([!self.condition]),
		}
	}
}

impl<'a, Db: ?Sized> ConditionalContradiction<'a, Db> {
	/// Turn a contradiction added to `db` into the negated `condition`.
	pub(crate) fn new(db: &'a mut Db, condition: Lit) -> Self {
		Self {
			db,
			condition,
			contradicted: false,
		}
	}
}

impl<Db: ClauseDatabase + ?Sized> ClauseDatabase for ConditionalContradiction<'_, Db> {
	fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result {
		if clause.is_empty() {
			self.db.add_clause([!self.condition])?;
			self.contradicted = true;
			// The caller stops encoding the constraint, as after any other
			// contradiction.
			return Err(Unsatisfiable);
		}
		self.db.add_clause_from_slice(clause)
	}

	fn new_var_range(&mut self, len: usize) -> VarRange {
		self.db.new_var_range(len)
	}
}

impl Conditioned {
	/// The same condition, for a piece that defines its last term.
	pub(crate) fn defining(self) -> Self {
		Self::Overflow(self.literal())
	}

	/// The condition.
	pub(crate) fn literal(self) -> Lit {
		match self {
			Self::All(r) | Self::Overflow(r) => r,
		}
	}

	/// The literal a clause takes, given whether it `overflows`: rules out a
	/// value its last term cannot take.
	pub(crate) fn negated(condition: Option<Self>, overflows: bool) -> BoolVal {
		match condition {
			Some(Self::All(r)) => BoolVal::Lit(!r),
			Some(Self::Overflow(r)) if overflows => BoolVal::Lit(!r),
			_ => BoolVal::Const(false),
		}
	}
}

impl<C, B: Copy> Implied<C, B> {
	/// Returns the condition.
	pub fn condition(&self) -> B {
		self.condition
	}

	/// Returns the constraint that holds where the condition does.
	pub fn constraint(&self) -> &C {
		&self.constraint
	}

	/// The constraint `condition → constraint`.
	pub fn new(condition: B, constraint: C) -> Self {
		Self {
			condition,
			constraint,
		}
	}
}

impl<C> Implied<C, Lit> {
	/// Encode with `conditional`, on a database on which a contradiction
	/// falsifies the condition, as does the [`Unsatisfiable`] it returns.
	pub(crate) fn encode_with<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		conditional: impl FnOnce(&mut ConditionalContradiction<'_, Db>, &C, Lit) -> Result,
	) -> Result {
		let mut cdb = ConditionalContradiction::new(db, self.condition);
		let result = conditional(&mut cdb, &self.constraint, self.condition);
		cdb.conclude(result)
	}
}
