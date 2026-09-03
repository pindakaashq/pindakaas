//! Pindakaas translates constraints stated at a higher level — propositional
//! logic, Boolean linear (pseudo-Boolean) constraints, integer linear
//! constraints — into conjunctive normal form, for a SAT solver to solve.
//!
//! Constraints are normalised and specialised on the way down, so that an
//! at-most-one group, a cardinality constraint and a general pseudo-Boolean
//! sum each reach an encoding built for its shape rather than a generic one.
//!
//! ```bash
//! cargo add pindakaas
//! ```
//!
//! Pindakaas is also available for Python; see the [Python
//! documentation](https://pindakaas.readthedocs.io/en/latest/).
//!
//! ## CNF
//!
//! [`Cnf`] collects clauses over [`Lit`]s and displays as DIMACS.
//!
//! ```rust
//! use pindakaas::{ClauseDatabaseTools, Cnf};
//!
//! let mut f = Cnf::default();
//! let (x, y, z) = f.new_lits();
//! f.add_clause([!x, y]);
//! f.add_clause([!y, z]);
//! f.add_clause([!z, x]);
//!
//! assert_eq!(f.to_string(), "p cnf 3 3\n-1 2 0\n-2 3 0\n-3 1 0\n");
//! ```
//!
//! ## Solving
//!
//! Both [`Cnf`] and [`Solver`](solver::Solver) implement [`ClauseDatabase`],
//! so anything that can be encoded into one can be encoded straight into the
//! other. Swapping [`Cadical`](solver::cadical::Cadical) for
//! [`Kissat`](solver::kissat::Kissat) is a change of `use` statement.
//!
//! ```rust
//! # use pindakaas::{ClauseDatabaseTools, Cnf};
//! use pindakaas::{
//!     solver::{cadical::Cadical, SolveResult, Solver},
//!     Valuation,
//! };
//!
//! # let mut f = Cnf::default();
//! # let (x, y, z) = f.new_lits();
//! # f.add_clause([!x, y]);
//! # f.add_clause([!y, z]);
//! # f.add_clause([!z, x]);
//!
//! let mut slv = Cadical::from(&f);
//! let mut solns = 0;
//! while let SolveResult::Satisfied(sol) = slv.solve() {
//!     solns += 1;
//!     slv.add_clause([x,y,z].map(|l| if sol.value(l) { !l } else { l }));
//! }
//!
//! assert_eq!(solns, 2);
//! ```
//!
//! Solvers sit behind feature flags, so that a dependency is only built where
//! it is wanted:
//!
//! - `cadical` (default) — [CaDiCaL](https://github.com/arminbiere/cadical),
//!   as [`Cadical`](solver::cadical::Cadical).
//! - `intel_sat` — [Intel SAT](https://github.com/alexander-nadel/intel_sat_solver),
//!   as [`IntelSat`](solver::intel_sat::IntelSat).
//! - `kissat` — [Kissat](https://github.com/arminbiere/kissat), as
//!   [`Kissat`](solver::kissat::Kissat).
//! - `libloading` — [`solver::libloading`], for loading an IPASIR library at
//!   runtime.
//! - `splr` — the common solver traits for [SPLR](https://github.com/shnarazk/splr).
//!
//! ## Propositional logic
//!
//! A [`Formula`](constraint::propositional_logic::Formula) is built from the
//! `&`, `|` and `^` operators; the rest of its variants — implication,
//! equivalence, if-then-else — are named explicitly. Encoding one is the job
//! of an [`Encoder`], here
//! [`TseitinEncoder`](constraint::propositional_logic::TseitinEncoder).
//!
//! ```rust
//! use pindakaas::{
//!     constraint::propositional_logic::{Formula, TseitinEncoder},
//!     ClauseDatabaseTools, Cnf,
//! };
//!
//! let mut f = Cnf::default();
//! let (x, y, z) = f.new_lits();
//! let p = (x ^ y) | z;
//! let q = Formula::IfThenElse {
//!     cond: Formula::Atom(z).into(),
//!     then: Formula::Atom(x).into(),
//!     els: Formula::Atom(y).into(),
//! };
//!
//! f.encode(&p, &TseitinEncoder);
//! f.encode(&q, &TseitinEncoder);
//! assert_eq!(f.num_clauses(), 7);
//! ```
//!
//! ## Linear constraints
//!
//! A [`LinExp`](constraint::bool_linear::LinExp) is a sum of terms built with
//! `+`, `-` and `*`. A term is either a [`Lit`], worth its coefficient when it
//! holds, or an [`IntVar`](decision::integer::IntVar), worth its coefficient
//! times whichever value it takes, so `x * 3 + y * 5` reads the same whichever
//! kind each side is. [`Linear::new`](constraint::bool_linear::Linear::new)
//! compares one against a constant.
//!
//! Encoding starts by aggregating, which normalises the constraint and
//! recognises what it actually is — a
//! [`LinVariant`](constraint::linear::LinVariant). That is what makes the
//! specialised encoders reachable; [`StaticLinEncoder`](encoder::aggregate::StaticLinEncoder)
//! picks one per variant, and [`LinearEncoder`](encoder::aggregate::LinearEncoder)
//! does both steps at once.
//!
//! ```rust
//! use pindakaas::{
//!     constraint::linear::{BoolLinAggregator, LinearEncoder, StaticLinEncoder},
//!     constraint::bool_linear::{Linear, Comparator},
//!     Cnf, ClauseDatabaseTools
//! };
//!
//! let mut f = Cnf::default();
//! let (x, y, z) = f.new_lits();
//! let con = Linear::new(x * 2 + y * 3 + z * 2, Comparator::LessEq, 2);
//!
//! // Use default encoders and aggregator options
//! let lin_enc: StaticLinEncoder = StaticLinEncoder::default();
//! let enc = LinearEncoder::new(lin_enc, BoolLinAggregator::default());
//!
//! f.encode(&con, &enc);
//!
//! // `y` alone would break the bound, and `x` and `z` cannot both hold.
//! assert_eq!(f.num_vars(), 4);
//! ```
//!
//! ## Integer variables
//!
//! An [`IntVar`](decision::integer::IntVar) is created with the domain it
//! ranges over, and holds whichever Boolean encodings its constraints ask for
//! — order literals for a sequential decomposition, bits for an adder, a
//! one-hot view for an at-most-one group — channelling between them where more
//! than one is called for. Nothing is chosen in advance, and a second variable
//! is never needed to hold the other view.
//!
//! Aggregating a constraint over them gives a
//! [`NormalizedIntLinear`](constraint::int_linear::NormalizedIntLinear): a sum
//! of positive coefficients against a bound. Choosing an encoder is then
//! choosing how that sum is broken up — a decision diagram, a chain of partial
//! sums, a balanced tree — each reaching the same
//! [`IntTernaryEncoder`](constraint::int_ternary::IntTernaryEncoder) for the
//! `x + y ≷ z` steps it leaves behind.
//!
//! ```rust
//! use pindakaas::{
//!     constraint::bool_linear::{Comparator, Linear},
//!     constraint::int_linear::BddEncoder,
//!     constraint::linear::{BoolLinAggregator, LinVariant},
//!     decision::integer::IntVar,
//!     solver::{cadical::Cadical, SolveResult, Solver},
//!     Cnf, Encoder,
//! };
//!
//! let mut f = Cnf::default();
//! let x = IntVar::new(0..=5).with_label("x");
//! let y = IntVar::new(0..=5).with_label("y");
//!
//! let con = Linear::new(x.clone() * 2 + y.clone() * 3, Comparator::LessEq, 10);
//! let LinVariant::Linear(con) = BoolLinAggregator::default().aggregate(&mut f, &con).unwrap()
//! else {
//!     panic!("a sum of integer terms is a linear constraint");
//! };
//! BddEncoder::default().encode(&mut f, &con).unwrap();
//!
//! let mut slv = Cadical::from(&f);
//! let SolveResult::Satisfied(sol) = slv.solve() else {
//!     panic!("the constraint has solutions");
//! };
//! assert!(2 * x.value(&sol) + 3 * y.value(&sol) <= 10);
//! ```
//!
//! ## Citation
//!
//! If you want to cite Pindakaas please use our general software
//! citation, in addition to any citation to a specific version or paper:
//!
//! ```biblatex
//! @software{Pindakaas,
//! author = {Bierlee, Hendrik and Dekker, Jip J.},
//! license = {MPL-2.0},
//! title = {{Pindakaas}},
//! url = {https://doi.org/10.5281/zenodo.10851855},
//! doi = {10.5281/zenodo.10851855},
//! }
//! ```
//!
//! Note that you might have to use `misc` instead of `software`, if your system
//! does not support `software` as a type.
//!
//! ## Acknowledgements
//!
//! This research was partially funded by the Australian Government through the
//! Australian Research Council Industrial Transformation Training Centre in
//! Optimisation Technologies, Integrated Methodologies, and Applications
//! (OPTIMA), Project ID IC200100009.

pub mod constraint;
pub mod decision;
pub mod encoder;
pub(crate) mod helpers;
pub mod solver;
#[cfg(any(feature = "tracing", test))]
pub mod trace;

use std::{
	cmp::Ordering,
	error::Error,
	fmt::{self, Display},
	fs::File,
	io::{self, BufRead, BufReader, Write},
	iter::repeat_n,
	num::NonZeroI32,
	path::Path,
	slice,
};

use itertools::{traits::HomogeneousTuple, Itertools};
pub use rangelist::{IntervalIterator, RangeList};

use crate::solver::VarFactory;
pub use crate::{
	decision::boolean::{BoolVal, Lit, Var, VarRange},
	helpers::AsDynClauseDatabase,
};

/// Checker is a trait implemented by types that represent constraints. The
/// [`Checker::check`] methods checks whether an assignment (often referred to
/// as a model) satisfies the constraint.
pub trait Checker {
	/// Check whether the constraint represented by the object is violated.
	///
	/// - The method returns [`Result::Ok`] when the assignment satisfies the
	///   constraint,
	/// - it returns [`Unsatisfiable`] when the assignment violates the
	///   constraint
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result<(), Unsatisfiable>;
}

/// The `ClauseDatabase` trait is the common trait implemented by types that are
/// used to manage the CNF encoding of constraints and contain their output.
/// This trait can be used for all encoding methods in this library.
///
/// To satisfy the trait, the type must implement a
/// [`Self::add_clause_from_slice`] method and a [`Self::new_var_range`] method.
pub trait ClauseDatabase {
	/// Add a clause to the `ClauseDatabase`. The database is allowed to return
	/// [`Unsatisfiable`] when the collection of clauses has been *proven* to be
	/// unsatisfiable. This is used as a signal to the encoder that any
	/// subsequent encoding effort can be abandoned.
	fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result;
	/// Method to be used to receive a new Boolean variable that can be used in
	/// the encoding of a problem or constraint.
	fn new_var_range(&mut self, len: usize) -> VarRange;
}

/// A trait automatically implemented for types that implement
/// [`ClauseDatabase`] providing a variety of utility methods that make it
/// easier to write common clause encoding patterns.
pub trait ClauseDatabaseTools: ClauseDatabase {
	/// Add a clause, given as any to the `ClauseDatabase`. The database is
	/// allowed to return [`Unsatisfiable`] when the collection of clauses has
	/// been *proven* to be unsatisfiable. This is used as a signal to the
	/// encoder that any subsequent encoding effort can be abandoned.
	fn add_clause<Iter>(&mut self, clause: Iter) -> Result
	where
		Iter: IntoIterator,
		Iter::Item: Into<BoolVal>,
	{
		let result: Result<Vec<_>, ()> = clause
			.into_iter()
			.filter_map(|v| match v.into() {
				BoolVal::Const(false) => None,         // Irrelevant literal
				BoolVal::Const(true) => Some(Err(())), // Clause is already satisfied
				BoolVal::Lit(lit) => Some(Ok(lit)),    // Add literal to clause
			})
			.collect();
		match result {
			Ok(clause) => {
				let result = self.add_clause_from_slice(&clause);
				#[cfg(any(feature = "tracing", test))]
				{
					tracing::info!(clause = ?&clause, fail = result.is_err(), "emit clause");
				}
				result
			}
			// Collecting revealed the clause was already satisfied
			Err(()) => Ok(()),
		}
	}

	/// Encoder helper that signals a contradiction has been detected in the
	/// constraint being encoded.
	///
	/// This will add an empty clause to the clause database.
	fn contradiction(&mut self) -> Result {
		let err = self.add_clause_from_slice(&[]);
		debug_assert_eq!(err, Err(Unsatisfiable));
		err
	}

	/// Encode a constraint using the provided encoder.
	fn encode<C, E>(&mut self, constraint: &C, encoder: &E) -> Result
	where
		C: ?Sized,
		E: Encoder<Self, C> + ?Sized,
	{
		encoder.encode(self, constraint)
	}

	/// Encode an implied constraint of the form `conditions -> constraint`.
	///
	/// This is a thin convenience wrapper around
	/// [`Encoder::encode_implied`].
	fn encode_implied<C, E>(&mut self, conditions: &[Lit], constraint: &C, encoder: &E) -> Result
	where
		C: ?Sized,
		E: Encoder<Self, C> + ?Sized + for<'a> Encoder<dyn ClauseDatabase + 'a, C>,
	{
		encoder.encode_implied(self, conditions, constraint)
	}

	/// Create a new Boolean variable in the form of a positive literal.
	fn new_lit(&mut self) -> Lit {
		self.new_var().into()
	}

	/// Create multiple new Boolean literals and capture them in a tuple.
	///
	/// # Example
	/// ```
	/// # use pindakaas::{ClauseDatabaseTools, Cnf};
	/// # let mut db = Cnf::default();
	/// let (a, b, c) = db.new_lits();
	/// ```
	fn new_lits<T>(&mut self) -> T
	where
		T: HomogeneousTuple<Item = Lit>,
	{
		let range = self.new_var_range(T::num_items());
		range.map(Lit::from).collect_tuple().unwrap()
	}

	#[cfg(any(feature = "tracing", test))]
	#[inline]
	/// Create a new Boolean variable in the form of a positive literal. The
	/// given name is used when the variable is output by the tracer.
	fn new_named_lit(&mut self, name: &str) -> Lit {
		self.new_named_var(name).into()
	}

	#[cfg(any(feature = "tracing", test))]
	#[inline]
	/// Create a new Boolean variable that can be used in the encoding of a
	/// problem. The given name is used when the variable is output by the
	/// tracer.
	fn new_named_var(&mut self, name: &str) -> Var {
		let var = self.new_var();
		tracing::info!(var = ?i32::from(var), label = name, "new variable");
		var
	}

	/// Create a new Boolean variable that can be used in the encoding of a
	/// problem or constraint.
	fn new_var(&mut self) -> Var {
		let mut range = self.new_var_range(1);
		debug_assert_eq!(range.len(), 1);
		range.next().unwrap()
	}

	/// Create multiple new Boolean variables and capture them in a tuple.
	///
	/// # Example
	/// ```
	/// # use pindakaas::{ClauseDatabaseTools, Cnf};
	/// # let mut db = Cnf::default();
	/// let (a, b, c) = db.new_vars();
	/// ```
	fn new_vars<T>(&mut self) -> T
	where
		T: HomogeneousTuple<Item = Var>,
	{
		let range = self.new_var_range(T::num_items());
		range.collect_tuple().unwrap()
	}
}

/// A representation for Boolean formulas in conjunctive normal form.
///
/// It can be used to create formulas manually, to store the results from
/// encoders, read formulas from a file, and write them to a file
#[derive(Clone, Debug, Default)]
pub struct Cnf {
	/// The variable factory used by [`new_var`]
	nvar: VarFactory,
	/// The literals from *all* clauses
	lits: Vec<Lit>,
	/// The size *for each* clause
	size: Vec<usize>,
}

#[derive(Debug, Clone)]
/// An iterator over the clauses in a CNF formula.
struct CnfIterator<'a> {
	lits: &'a Vec<Lit>,
	size: slice::Iter<'a, usize>,
	index: usize,
}

/// Coeff is a type alias used for the number type used to represent the
/// coefficients in constraints and expression.
pub(crate) type Coeff = i64;

enum Dimacs {
	Cnf(Cnf),
	Wcnf(Wcnf),
}

/// The central trait, implemented by every encoding algorithm.
///
/// A type implements it once per constraint it can encode, so which encoders
/// apply to a constraint is what its "Implementors" list shows.
pub trait Encoder<Db: ClauseDatabase + ?Sized, Constraint: ?Sized> {
	/// Encode the constraint into the given clausal database.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] where the constraint cannot hold — because it is
	/// unsatisfiable in itself, or because it is unsatisfiable together with
	/// what `db` already holds. Clauses may already have been emitted, so a
	/// database that returns this is no longer usable for anything else.
	fn encode(&self, db: &mut Db, con: &Constraint) -> Result;

	/// Encode the implied constraint `conditions -> constraint`.
	///
	/// Clauses emitted while encoding are guarded with the condition literals.
	/// If encoding returns [`Unsatisfiable`], the conditions are forced to be
	/// false.
	fn encode_implied(&self, db: &mut Db, conditions: &[Lit], con: &Constraint) -> Result
	where
		Self: for<'a> Encoder<dyn ClauseDatabase + 'a, Constraint>,
	{
		if conditions.is_empty() {
			return self.encode(db, con);
		}

		struct ClauseBuffer<'a, Db: ClauseDatabase + ?Sized> {
			db: &'a mut Db,
			lits: Vec<Lit>,
			size: Vec<usize>,
		}

		impl<Db: ClauseDatabase + ?Sized> ClauseDatabase for ClauseBuffer<'_, Db> {
			fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result {
				let start = self.lits.len();
				self.lits.extend_from_slice(clause);
				let len = self.lits.len() - start;
				self.size.push(len);
				if len == 0 {
					Err(Unsatisfiable)
				} else {
					Ok(())
				}
			}

			fn new_var_range(&mut self, len: usize) -> VarRange {
				self.db.new_var_range(len)
			}
		}

		let (result, lits, sizes) = {
			let mut cdb = ClauseBuffer {
				db,
				lits: Vec::new(),
				size: Vec::new(),
			};
			let result = {
				let cdb_dyn: &mut (dyn ClauseDatabase + '_) = &mut cdb;
				self.encode(cdb_dyn, con)
			};
			(result, cdb.lits, cdb.size)
		};

		let conditions: Vec<_> = conditions.iter().map(|&l| !l).collect();
		let (lits, sizes) = match result {
			Ok(()) => (lits, sizes),
			Err(Unsatisfiable) => return db.add_clause_from_slice(&conditions),
		};

		let mut index = 0;
		let mut clause = Vec::with_capacity(conditions.len());
		for size in sizes {
			clause.clear();
			clause.extend_from_slice(&conditions);
			clause.extend_from_slice(&lits[index..index + size]);
			db.add_clause_from_slice(&clause)?;
			index += size;
		}
		Ok(())
	}
}

/// Result is a type alias for [`std::result::Result`] that by default returns
/// an empty value, or the [`Unsatisfiable`] error type.
type Result<T = (), E = Unsatisfiable> = std::result::Result<T, E>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
/// Unsatisfiable is an error type returned when the problem being encoded is
/// found to be inconsistent.
pub struct Unsatisfiable;

/// A trait implemented by types that can be used to represent a solution/model
pub trait Valuation {
	/// Returns the valuation/truth-value for a given literal in the
	/// current solution/model.
	fn value(&self, lit: Lit) -> bool;
}

/// A representation for a weighted CNF formula
///
/// Same as CNF, but every clause has an optional weight. Otherwise, it is a
/// hard clause.
#[derive(Clone, Debug, Default)]
pub struct Wcnf {
	/// The CNF formula
	cnf: Cnf,
	/// The weight for every clause
	weights: Vec<Option<Coeff>>,
	// TODO this can be optimised, for example by having all weighted clauses at the start/end
}

/// Internal function used to parse a file in the (weighted) DIMACS format.
///
/// This function is used by `Cnf::from_str` and `Wcnf::from_str`.
fn parse_dimacs_file<const WEIGHTED: bool>(path: &Path) -> Result<Dimacs, io::Error> {
	let file = File::open(path)?;
	let mut had_header = false;

	let mut wcnf = Wcnf::default();

	let mut cl: Vec<Lit> = Vec::new();
	let mut top: Option<Coeff> = None;

	for line in BufReader::new(file).lines() {
		match line {
			Ok(line) if line.is_empty() || line.starts_with('c') => (),
			Ok(line) if had_header => {
				for seg in line.split(' ') {
					if WEIGHTED {
						if let Ok(weight) = seg.parse::<Coeff>() {
							wcnf.weights.push(match weight.cmp(&top.unwrap()) {
								Ordering::Less => Some(weight),
								Ordering::Equal => None,
								Ordering::Greater => panic!(
								"Found weight weight {weight} greater than top {top:?} from header"
							),
							});
						} else {
							panic!("Cannot parse line {line}");
						}
					}

					if let Ok(lit) = seg.parse::<i32>() {
						if lit == 0 {
							wcnf.add_clause(cl.drain(..)).unwrap();
						} else {
							cl.push(Lit(NonZeroI32::new(lit).unwrap()));
						}
					}
				}
			}
			// parse header, expected format: "p cnf {num_var} {num_clauses}" or "p wcnf {num_var}
			// {num_clauses} {top}"
			Ok(line) => {
				let vec: Vec<&str> = line.split_whitespace().collect();
				// check "p" and "cnf" keyword
				if !WEIGHTED && (vec.len() != 4 || vec[0..2] != ["p", "cnf"]) {
					return Err(io::Error::new(
						io::ErrorKind::InvalidInput,
						"expected DIMACS CNF header formatted \"p cnf {variables} {clauses}\"",
					));
				} else if WEIGHTED && (vec.len() != 4 || vec[0..2] != ["p", "wcnf"]) {
					return Err(io::Error::new(
						io::ErrorKind::InvalidInput,
						"expected DIMACS WCNF header formatted \"p wcnf {variables} {clauses} {top}\"",
					));
				}
				// parse number of variables
				wcnf.cnf.nvar = VarFactory {
					next_var: Some(Var(vec[2].parse::<NonZeroI32>().map_err(|_| {
						io::Error::new(
							io::ErrorKind::InvalidInput,
							"unable to parse number of variables",
						)
					})?)),
				};
				// parse number of clauses
				let num_clauses: usize = vec[3].parse().map_err(|_| {
					io::Error::new(
						io::ErrorKind::InvalidInput,
						"unable to parse number of clauses",
					)
				})?;

				wcnf.cnf.lits.reserve(num_clauses);
				wcnf.cnf.size.reserve(num_clauses);

				if WEIGHTED {
					top = Some(vec[4].parse().map_err(|_| {
						io::Error::new(io::ErrorKind::InvalidInput, "unable to parse top weight")
					})?);
				}

				// parsing header complete
				had_header = true;
			}
			Err(e) => return Err(e),
		}
	}

	if WEIGHTED {
		Ok(Dimacs::Wcnf(wcnf))
	} else {
		Ok(Dimacs::Cnf(wcnf.cnf))
	}
}

impl Cnf {
	/// Read a CNF formula from a file formatted in the DIMACS CNF format
	pub fn from_file(path: &Path) -> Result<Self, io::Error> {
		match parse_dimacs_file::<false>(path)? {
			Dimacs::Cnf(cnf) => Ok(cnf),
			_ => unreachable!(),
		}
	}

	#[cfg(test)]
	/// Small helper method that gets all the created variables, used for
	/// testing.
	pub(crate) fn get_variables(&self) -> VarRange {
		let first = Var(NonZeroI32::new(1).unwrap());
		match self.nvar.next_var.and_then(|v| v.prev_var()) {
			Some(last) => VarRange::new(first, last),
			// Nothing has been created, so there is nothing to range over.
			None => VarRange::empty(),
		}
	}

	/// Returns an iterator over the clauses in the formula.
	pub fn iter(&self) -> impl ExactSizeIterator<Item = &[Lit]> + '_ {
		CnfIterator {
			lits: &self.lits,
			size: self.size.iter(),
			index: 0,
		}
	}

	/// Returns the number of literals in the formula.
	pub fn literals(&self) -> usize {
		self.size.iter().sum()
	}
	/// Returns the number of clauses in the formula.
	pub fn num_clauses(&self) -> usize {
		self.size.len()
	}

	/// Returns the number of variables in the formula.
	pub fn num_vars(&self) -> usize {
		self.nvar.num_emitted_vars()
	}

	/// Store CNF formula at given path in DIMACS format
	///
	/// File will optionally be prefaced by a given comment
	pub fn to_file(&self, path: &Path, comment: Option<&str>) -> Result<(), io::Error> {
		let mut file = File::create(path)?;
		if let Some(comment) = comment {
			for line in comment.lines() {
				writeln!(file, "c {line}")?;
			}
		}
		write!(file, "{self}")
	}

	/// Returns the range of variables emitted to be used by this formula.
	pub fn variables(&self) -> VarRange {
		self.nvar.emitted_vars()
	}
}

impl ClauseDatabase for Cnf {
	fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result {
		let size = self.lits.len();
		self.lits.extend(clause);
		let len = self.lits.len() - size;
		self.size.push(len);
		if len == 0 {
			Err(Unsatisfiable)
		} else {
			Ok(())
		}
	}

	fn new_var_range(&mut self, len: usize) -> VarRange {
		self.nvar.next_var_range(len)
	}
}

impl Display for Cnf {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let num_var = &self.num_vars();
		let num_clauses = self.size.len();
		writeln!(f, "p cnf {num_var} {num_clauses}")?;
		let mut start = 0;
		for size in self.size.iter() {
			let cl = self.lits.iter().skip(start).take(*size);
			for &lit in cl {
				write!(f, "{} ", i32::from(lit))?;
			}
			writeln!(f, "0")?;
			start += size;
		}
		Ok(())
	}
}

impl ExactSizeIterator for CnfIterator<'_> {}

impl<'a> Iterator for CnfIterator<'a> {
	type Item = &'a [Lit];

	fn count(self) -> usize {
		self.size.count()
	}

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(size) = self.size.next() {
			let start = self.index;
			self.index += size;
			Some(&self.lits[start..self.index])
		} else {
			None
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.size.size_hint()
	}
}

impl<Db: ClauseDatabase + ?Sized> ClauseDatabaseTools for Db {}

impl<F: Fn(Lit) -> bool> Valuation for F {
	fn value(&self, lit: Lit) -> bool {
		self(lit)
	}
}

impl Display for Unsatisfiable {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Problem inconsistency detected")
	}
}

impl Error for Unsatisfiable {}

impl Wcnf {
	/// Add a weighted clause to the formula.
	pub fn add_weighted_clause<I>(&mut self, clause: I, weight: Coeff) -> Result
	where
		I: IntoIterator,
		I::Item: Into<BoolVal>,
	{
		let clauses = self.cnf.num_clauses();
		self.cnf.add_clause(clause)?;
		if self.cnf.num_clauses() > clauses {
			self.weights.push(Some(weight));
		}
		Ok(())
	}

	/// Read a WCNF formula from a file formatted in the (W)DIMACS WCNF format
	pub fn from_file(path: &Path) -> Result<Self, io::Error> {
		match parse_dimacs_file::<true>(path)? {
			Dimacs::Wcnf(wcnf) => Ok(wcnf),
			_ => unreachable!(),
		}
	}

	/// Returns an iterator over the clauses and their weights.
	pub fn iter(&self) -> impl ExactSizeIterator<Item = (&[Lit], &Option<Coeff>)> {
		self.cnf.iter().zip(self.weights.iter())
	}

	/// Returns the number of literals in the formula.
	pub fn literals(&self) -> usize {
		self.cnf.literals()
	}

	/// Returns the number of clauses in the formula.
	pub fn num_clauses(&self) -> usize {
		self.cnf.num_clauses()
	}

	/// Returns the number of variables in the formula.
	pub fn num_vars(&self) -> usize {
		self.cnf.num_vars()
	}

	/// Store WCNF formula at given path in WDIMACS format
	///
	/// File will optionally be prefaced by a given comment
	pub fn to_file(&self, path: &Path, comment: Option<&str>) -> Result<(), io::Error> {
		let mut file = File::create(path)?;
		if let Some(comment) = comment {
			for line in comment.lines() {
				writeln!(file, "c {line}")?;
			}
		}
		write!(file, "{self}")
	}

	/// Returns the range of variables emitted to be used by this formula.
	pub fn variables(&self) -> VarRange {
		self.cnf.variables()
	}
}

impl ClauseDatabase for Wcnf {
	fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result {
		let clauses = self.cnf.num_clauses();
		self.cnf.add_clause_from_slice(clause)?;
		if self.cnf.num_clauses() > clauses {
			self.weights.push(None);
		}
		Ok(())
	}

	fn new_var_range(&mut self, len: usize) -> VarRange {
		self.cnf.new_var_range(len)
	}
}

impl Display for Wcnf {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let num_var = &self.cnf.nvar.num_emitted_vars();
		let num_clauses = self.cnf.size.len();
		let top = self.weights.iter().flatten().fold(1, |a, b| a + *b);
		writeln!(f, "p wcnf {num_var} {num_clauses} {top}")?;
		let mut start = 0;
		for (size, weight) in self.cnf.size.iter().zip(self.weights.iter()) {
			let cl = self.cnf.lits.iter().skip(start).take(*size);
			let weight = weight.unwrap_or(top);
			write!(f, "{weight} ")?;
			for lit in cl {
				write!(f, "{} ", lit.0)?;
			}
			writeln!(f, "0")?;
			start += size;
		}
		Ok(())
	}
}

impl From<Cnf> for Wcnf {
	fn from(cnf: Cnf) -> Self {
		let weights = repeat_n(None, cnf.num_clauses()).collect();
		Wcnf { cnf, weights }
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZeroI32;

	use crate::{solver::VarFactory, Lit, Var};

	#[test]
	fn var_range() {
		let mut factory = VarFactory::default();

		let range = factory.next_var_range(0);
		assert_eq!(range.len(), 0);
		assert_eq!(factory.next_var, Some(Var(NonZeroI32::new(1).unwrap())));

		let range = factory.next_var_range(1);
		assert_eq!(range.len(), 1);
		assert_eq!(factory.next_var, Some(Var(NonZeroI32::new(2).unwrap())));

		let range = factory.next_var_range(2);
		assert_eq!(range.len(), 2);
		assert_eq!(factory.next_var, Some(Var(NonZeroI32::new(4).unwrap())));

		let range = factory.next_var_range(100);
		assert_eq!(range.len(), 100);
		assert_eq!(factory.next_var, Some(Var(NonZeroI32::new(104).unwrap())));
	}

	impl From<i32> for Lit {
		fn from(value: i32) -> Self {
			Lit(NonZeroI32::new(value).expect("cannot create literal with value zero"))
		}
	}
}
