//! Pindakaas is an encoding library that helps translate higher abstraction
//! level constraints into conjunctive normal form (CNF), so that it can be used
//! by Boolean satisfiability (SAT) solvers. Pindakaas supports constraints such
//! as propositional logic, Boolean linear constraints (i.e. pseudo-Boolean (PB)
//! constraints), and integer linear constraint. Importantly, Pindakaas
//! normalizes and specializes the constraints to be able to use specialized
//! encoding methods to an efficient solvable encoding. For example, making the
//! distinction between “at most one”, cardinality, and general pseudo-Boolean
//! constraints.
//!
//! ## Installation
//!
//! You can add the pindakaas crate to your project using Cargo:
//!
//! ```bash
//! cargo add pindakaas
//! ```
//!
//! _Note that Pindakaas is also available for Python. For more information,
//! visit the [Python
//! documentation](https://pindakaas.readthedocs.io/en/latest/)._
//!
//! ## CNF Modelling
//!
//! Like other SAT modelling libraries, Pindakaas includes the functionality to
//! model at CNF level. For example, the following code snippet shows how to
//! create an empty CNF formula, then create three variables, and add some
//! circular clauses, and then print the formula in
//! [DIMACS](https://web.archive.org/web/20190325181937/https://www.satcompetition.org/2009/format-benchmarks2009.html)
//! format.
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
//! Note that the `!` operator is used to negate a literal.
//!
//! It is also possible to load a CNF formula for a DIMACS formatted file using
//! the [`Cnf::from_file`] method, and to write it to a DIMACS file using the
//! [`Cnf::to_file`] method.
//!
//! ## Using SAT solvers
//!
//! In the [`solver`] module, we provide access to several competitive SAT
//! solvers, such as [CaDiCaL](https://github.com/arminbiere/cadical) and
//! [Kissat](https://github.com/arminbiere/kissat). We also provide several
//! common solver traits, such as [`solver::Solver`], such that solvers can be
//! easily switched.
//!
//! To, for example, show that only two solutions exists for the formula in the
//! previous section using CaDiCaL, we can use the following fragment.
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
//! If we had wanted to use Kissat instead of CaDiCaL, we would have only had to
//! add a the `use` statement for [`solver::kissat::Kissat`], and use
//! `Kissat::from(&f)`.
//!
//! In either case, it is also not required to start from a [`Cnf`] instance.
//! Both [`Cnf`] and [`Solver`](solver::Solver) instances implement the
//! [`ClauseDatabase`] trait, and can often be used interchangeably.
//!
//! _Note that not all solvers are available by default. To minimize upstream
//! dependencies, each solver has its own feature flag. So enable any of the
//! following features if you want to enable additional solvers._
//!
//! - `cadical` (enabled by default) - enables the use of the [CaDiCaL](https://github.com/arminbiere/cadical)
//!   solver, available as [`Cadical`](solver::cadical::Cadical) in the
//!   [`solver::cadical`] module.
//! - `intel_sat` - enables the use of the [Intel SAT](https://github.com/alexander-nadel/intel_sat_solver)
//!   solver, available as [`IntelSat`](solver::intel_sat::IntelSat) in the
//!   [`solver::intel_sat`] module.
//! - `kissat` - enables the use of the [Kissat](https://github.com/arminbiere/kissat)
//!   solver, available as [`Kissat`](solver::kissat::Kissat) in the
//!   [`solver::kissat`] module.
//! - `libloading` - enables the [`solver::libloading`] module, which allows
//!   runtime loading of dynamically loaded libraries (DLLs) that implement the
//!   IPASIR interface.
//! - `splr` - enables implementation of the pindakaas common solver traits for
//!   the [SPLR](https://github.com/shnarazk/splr) solver, available in its own
//!   crate: [`splr::Solver`].
//!
//! ## Proposition Logic and [`Encoder`]s
//!
//! The first abstraction that Pindakaas provides from modelling using CNF, is
//! to allow the use of constraint based on propositional logic. This makes it
//! easy to express most logic based constraints. In Pindakaas, propositional
//! logic is represented using
//! [`Formula`](constraint::propositional_logic::Formula). An easy way to create
//! one is to use the `&`, `|`, and `^` operators, which
//! create [`And`](constraint::propositional_logic::Formula::And),
//! [`Or`](constraint::propositional_logic::Formula::Or) and
//! [`Xor`](constraint::propositional_logic::Formula::Xor) instances,
//! respectively. Other, more complex, propositional logic constructs, such as
//! [`Formula::IfThenElse`](constraint::propositional_logic::Formula::IfThenElse) and
//! [`Formula::Equiv`](constraint::propositional_logic::Formula::Equiv), must be
//! constructed explicitly.
//!
//! A [`Formula`](constraint::propositional_logic::Formula) can be used as a
//! constraint, and as such it must be encoded into a CNF formula. In Pindakaas
//! types implement the [`Encoder`] to translate constraint types into CNF
//! formulas. For [`Formula`](constraint::propositional_logic::Formula), it is
//! [`TseitinEncoder`](constraint::propositional_logic::TseitinEncoder) that
//! implements the [`Encoder`] trait. The following fragment shows how we
//! create two [`Formula`](constraint::propositional_logic::Formula) instances
//! and encode them to CNF using the
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
//! ## Boolean and Integer Linear Constraints
//!
//! The most important feature of Pindakaas is its ability to encode Boolean and
//! integer linear constraints into CNF formulas. This provides the ability to
//! model and solve a wide range of problems. To model a linear constraint, we
//! start by creating linear expressions, represented using
//! [`LinExp`](constraint::bool_linear::LinExp). We can use standard operators,
//! such as `+` and `-`, to add terms together, and `*` to multiply one by a
//! constant. A term is either a [`Lit`], worth its
//! coefficient when it holds, or an [`IntVar`](decision::integer::IntVar),
//! worth its coefficient times whichever value it takes — so `x * 3 + y * 5`
//! reads the same whichever kind each side is.
//!
//! [`LinExp`](constraint::bool_linear::LinExp) can be turned into a constraint
//! using the [`Linear::new`](constraint::bool_linear::Linear::new) method. It
//! takes the linear expression as the left hand side, then a
//! [`Comparator`](constraint::bool_linear::Comparator), and then a constant as
//! the right hand side.
//!
//! Before the constraint is encoded, it is first simplified, normalized, and
//! specialized by the
//! [`BoolLinAggregator::aggregate`](encoder::aggregate::BoolLinAggregator::aggregate).
//! The result of this is a constraint of the form
//! [`LinVariant`](constraint::linear::LinVariant). Depending on the form of
//! the specialized constraint, the constraint can be encoded using different
//! encoding methods. For example, if the constraint was found to be a “at most
//! one” constraint, then it could use the
//! [`BitwiseEncoder`](encoder::bitwise::BitwiseEncoder). However, we can
//! always
//! use general pseudo-Boolean encoders, such as the
//! [`TotalizerEncoder`](constraint::bool_linear::TotalizerEncoder). Making the
//! choice of encoding can be streamlined by using the
//! [`StaticLinEncoder`](encoder::aggregate::StaticLinEncoder), which makes a
//! choice based on the constraint's variant.
//!
//! Additionally, the [`LinearEncoder`](encoder::aggregate::LinearEncoder) is
//! help streamline the process of aggregating and encoding linear expressions.
//! The following fragment shows the creation of a linear constraint and the
//! usage of the [`LinearEncoder`](encoder::aggregate::LinearEncoder) to encode
//! it.
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
//! ## Integer Linear Constraints
//!
//! A constraint can also be stated over integer variables directly. An
//! [`IntVar`](decision::integer::IntVar) is created with the domain it ranges
//! over, and holds whichever Boolean encodings its constraints need — order
//! literals for a sequential decomposition, bits for an adder, a one-hot view
//! for an at-most-one group — channelling between them when more than one is
//! called for. Nothing has to be chosen in advance, and a second variable is
//! never needed to hold the other view.
//!
//! A linear constraint over those variables is written as a
//! [`Linear`](constraint::bool_linear::Linear) and
//! aggregated, which puts it into the one form every encoder takes: a
//! [`NormalizedIntLinear`](constraint::int_linear::NormalizedIntLinear), a sum
//! of terms with positive coefficients against a bound. Choosing an encoder is
//! then choosing how the sum is broken up — a decision diagram, a chain of
//! partial sums, or a balanced tree — each of which reaches the same
//! [`IntTernaryEncoder`](constraint::int_ternary::IntTernaryEncoder) for
//! the two-terms-against-a-third steps it produces.
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
pub use rangelist::RangeList;

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

/// Encoder is the central trait implemented for all the encoding algorithms
pub trait Encoder<Db: ClauseDatabase + ?Sized, Constraint: ?Sized> {
	/// Encode the constraint into the given clausal database.
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
