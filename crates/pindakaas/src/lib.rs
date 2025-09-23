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
//! logic is represented using [`Formula`]. An easy way to create [`Formula`]
//! instances is to use the `&`, `|`, and `^` operators, which will
//! create[`Formula::And`], [`Formula::Or`], and[`Formula::Xor`] instances,
//! respectively. Other, more complex, propositional logic constructs, such as
//! [`Formula::IfThenElse`] and [`Formula::Equiv`], must be constructed
//! explicitly.
//!
//! A [`Formula`] can be used as a constraint, and as such it must be encoded
//! into a CNF formula. In Pindakaas types implement the [`Encoder`] to
//! translate constraint types into CNF formulas. For [`Formula`], it is
//! [`TseitinEncoder`](propositional_logic::TseitinEncoder) that implements the
//! [`Encoder`] trait. The following fragment shows how we create two
//! [`Formula`] instances and encode them to CNF using the
//! [`TseitinEncoder`](propositional_logic::TseitinEncoder).
//!
//! ```rust
//! use pindakaas::{
//!     propositional_logic::{Formula, TseitinEncoder},
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
//! start by creating linear expressions, represented using [`BoolLinExp`]. We
//! can use standard operators, such as `+` and `-`, to add [`Lit`]s together,
//! or `*` to multiply them by a constant. (See the [`BoolLinExp`] documentation
//! for advanced operations on expressions.) Additionally, integer variables
//! (decided using Boolean variables) can be added to the linear expression when
//! they're represented as a [`IntEncoding`].
//!
//! [`BoolLinExp`] can be turned into a constraint using the
//! [`BoolLinear::new`](bool_linear::BoolLinear::new) method. It takes the
//! linear expression as the left hand side, then a
//! [`Comparator`](bool_linear::Comparator), and then a constant as the right
//! hand side.
//!
//! Before the constraint is encoded, it is first simplified, normalized, and
//! specialized by the
//! [`BoolLinAggregator::aggregate`](bool_linear::BoolLinAggregator::aggregate).
//! The result of this is a constraint of the form
//! [`BoolLinVariant`](bool_linear::BoolLinVariant). Depending on the form of
//! the specialized constraint, the constraint can be encoded using different
//! encoding methods. For example, if the constraint was found to be a “at most
//! one” constraint, then it could use the
//! [`BitwiseEncoder`](cardinality_one::BitwiseEncoder). However, we can always
//! use general pseudo-Boolean encoders, such as the
//! [`TotalizerEncoder`](bool_linear::TotalizerEncoder). Making the choice of
//! encoding can be streamlined by using the
//! [`StaticLinEncoder`](bool_linear::StaticLinEncoder), which makes a choice
//! based on the constraint's variant.
//!
//! Additionally, the [`LinearEncoder`](bool_linear::LinearEncoder) is meant to
//! help streamline the process of aggregating and encoding linear expressions.
//! The following fragment shows the creation of a linear constraint and the
//! usage of the [`LinearEncoder`](bool_linear::LinearEncoder) to encode it.
//!
//! ```rust
//! use pindakaas::{
//!     bool_linear::{
//!         BoolLinear, BoolLinAggregator, Comparator, LinearEncoder, StaticLinEncoder
//!     },
//!     Cnf, ClauseDatabaseTools
//! };
//!
//! let mut f = Cnf::default();
//! let (x, y, z) = f.new_lits();
//! let con = BoolLinear::new(x * 2 + y * 3 + z * 2, Comparator::LessEq, 2);
//!
//! // Use default encoders and aggregator options
//! let lin_enc: StaticLinEncoder = StaticLinEncoder::default();
//! let enc = LinearEncoder::new(lin_enc, BoolLinAggregator::default());
//!
//! f.encode(&con, &enc);
//! assert_eq!(f.num_clauses(), 2); // (!x & !z) & !y
//! ```
//!
//! ## Acknowledgements
//!
//! This research was partially funded by the Australian Government through the
//! Australian Research Council Industrial Transformation Training Centre in
//! Optimisation Technologies, Integrated Methodologies, and Applications
//! (OPTIMA), Project ID IC200100009.

pub mod bool_linear;
pub mod cardinality;
pub mod cardinality_one;
pub(crate) mod helpers;
mod integer;
pub mod propositional_logic;
pub mod solver;
mod sorted;
#[cfg(any(feature = "tracing", test))]
pub mod trace;

use std::{
	clone::Clone,
	cmp::{max, Eq, Ordering},
	error::Error,
	fmt::{self, Display},
	fs::File,
	hash::Hash,
	io::{self, BufRead, BufReader, Write},
	iter::{repeat_n, FusedIterator},
	num::NonZeroI32,
	ops::{Add, BitAnd, BitOr, BitXor, Bound, Mul, Not, RangeBounds, RangeInclusive},
	path::Path,
	slice,
};

use itertools::{traits::HomogeneousTuple, Itertools};

pub use crate::helpers::AsDynClauseDatabase;
use crate::{
	bool_linear::BoolLinExp, helpers::subscript_number, propositional_logic::Formula,
	solver::VarFactory,
};

/// A helper type used to represent a Boolean value that can be either a literal
/// for a Boolean decision variable, or a constant Boolean value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[expect(
	variant_size_differences,
	reason = "bool is 1 byte, but Lit will always require more"
)]
pub enum BoolVal {
	/// A constant Boolean value.
	Const(bool),
	/// A literal for a Boolean decision variable.
	Lit(Lit),
}

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

	/// Encode a constraint using the provided encoder.
	fn encode<C, E>(&mut self, constraint: &C, encoder: &E) -> Result
	where
		C: ?Sized,
		E: Encoder<Self, C> + ?Sized,
	{
		encoder.encode(self, constraint)
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

	/// Create a [`ClauseDatabase`] wrapper that adds the given conditions to
	/// each clause that it adds to the wrapped database.
	///
	/// Note that the wrapped database type itself implements the
	/// [`ClauseDatabase`] trait.
	fn with_conditions(&mut self, conditions: Vec<Lit>) -> impl ClauseDatabase + '_
	where
		Self: AsDynClauseDatabase,
	{
		struct ConditionalDatabase<'a> {
			db: &'a mut dyn ClauseDatabase,
			conditions: Vec<Lit>,
		}

		impl ClauseDatabase for ConditionalDatabase<'_> {
			fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result {
				let chain = self
					.conditions
					.iter()
					.copied()
					.chain(clause.iter().copied())
					.collect_vec();
				self.db.add_clause_from_slice(&chain)
			}

			fn new_var_range(&mut self, len: usize) -> VarRange {
				self.db.new_var_range(len)
			}
		}

		ConditionalDatabase {
			db: self.as_mut_dyn(),
			conditions,
		}
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
}

/// IntEncoding is a enumerated type use to represent an Boolean encoding of a
/// integer variable within this library
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IntEncoding<'a> {
	/// The Direct variant represents a integer variable encoded using domain
	/// or direct encoding of an integer variable. Each given Boolean literal
	/// represents whether the integer takes the associated value (i.e., X =
	/// (first+i) ↔ vals\[i\]).
	Direct {
		/// The offset of the value of the encoded integer variable, i.e. the
		/// value if the first literal is `true`.
		first: Coeff,
		/// The list of literals representing the each value of the integer
		/// variable.
		vals: &'a [Lit],
	},
	/// The Order variant represents a integer variable using an order
	/// encoding. Each given Boolean literal represents whether the integer
	/// is bigger than the associated value(i.e., X > (first+i) ↔ vals\[i\]).
	Order {
		/// The offset of the value of the encoded integer variable, i.e. the
		/// value if no literal is `true`.
		first: Coeff,
		/// The list of literals representing the each value of the integer
		/// variable.
		vals: &'a [Lit],
	},
	/// The Log variant represents a integer variable using a two's complement
	/// encoding. The sum of the Boolean literals multiplied by their
	/// associated power of two represents value of the integer (i.e., X = ∑
	/// 2ⁱ·bits\[i\]).
	Log {
		/// Whether the first bit is interpreted as a sign bit.
		signed: bool,
		/// The list of literals representing the each bit of the integer
		/// variable.
		bits: &'a [Lit],
	},
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Literal is type that can be use to represent Boolean decision variables and
/// their negations
pub struct Lit(NonZeroI32);

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
	///
	/// Note that the function can return None if the model/solution is
	/// independent of the given literal.
	fn value(&self, lit: Lit) -> bool;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// A canonical implementation of a Boolean decision variable, independent of
/// negation.
pub struct Var(pub(crate) NonZeroI32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// A continuous range of Boolean variables.
///
/// This is a representation that is used to represent a range of variables in a
/// more compact way.
pub struct VarRange {
	start: Var,
	end: Var,
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

impl BitAnd<BoolVal> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitand(self, rhs: BoolVal) -> Self::Output {
		match (self, rhs) {
			(BoolVal::Const(a), BoolVal::Const(b)) => Formula::Atom((a & b).into()),
			(BoolVal::Lit(a), BoolVal::Lit(b)) => (a & b).into(),
			(BoolVal::Lit(a), BoolVal::Const(b)) | (BoolVal::Const(b), BoolVal::Lit(a)) => {
				Formula::Atom(a & b)
			}
		}
	}
}

impl BitAnd<Lit> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitand(self, rhs: Lit) -> Self::Output {
		self & BoolVal::Lit(rhs)
	}
}

impl BitAnd<bool> for BoolVal {
	type Output = BoolVal;

	fn bitand(self, rhs: bool) -> Self::Output {
		match self {
			BoolVal::Const(b) => (b & rhs).into(),
			BoolVal::Lit(l) if rhs => (l).into(),
			BoolVal::Lit(_) => false.into(),
		}
	}
}

impl BitOr<BoolVal> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitor(self, rhs: BoolVal) -> Self::Output {
		match (self, rhs) {
			(BoolVal::Const(a), BoolVal::Const(b)) => Formula::Atom((a | b).into()),
			(BoolVal::Lit(a), BoolVal::Lit(b)) => (a | b).into(),
			(BoolVal::Lit(a), BoolVal::Const(b)) | (BoolVal::Const(b), BoolVal::Lit(a)) => {
				Formula::Atom(a | b)
			}
		}
	}
}

impl BitOr<Lit> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitor(self, rhs: Lit) -> Self::Output {
		self | BoolVal::Lit(rhs)
	}
}

impl BitOr<bool> for BoolVal {
	type Output = BoolVal;

	fn bitor(self, rhs: bool) -> Self::Output {
		match self {
			BoolVal::Const(b) => (b | rhs).into(),
			BoolVal::Lit(_) if rhs => true.into(),
			BoolVal::Lit(_) => self,
		}
	}
}

impl BitXor<BoolVal> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitxor(self, rhs: BoolVal) -> Self::Output {
		match (self, rhs) {
			(BoolVal::Const(a), BoolVal::Const(b)) => Formula::Atom((a ^ b).into()),
			(BoolVal::Lit(a), BoolVal::Lit(b)) => {
				Formula::Xor(vec![Formula::Atom(a.into()), Formula::Atom(b.into())])
			}
			(BoolVal::Lit(a), BoolVal::Const(b)) | (BoolVal::Const(b), BoolVal::Lit(a)) => {
				Formula::Atom((a ^ b).into())
			}
		}
	}
}

impl BitXor<Lit> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitxor(self, rhs: Lit) -> Self::Output {
		self ^ BoolVal::Lit(rhs)
	}
}

impl BitXor<bool> for BoolVal {
	type Output = BoolVal;

	fn bitxor(self, rhs: bool) -> Self::Output {
		if rhs {
			!self
		} else {
			self
		}
	}
}

impl Display for BoolVal {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			BoolVal::Const(b) => write!(f, "{b}"),
			BoolVal::Lit(l) => write!(f, "{l}"),
		}
	}
}

impl From<Lit> for BoolVal {
	fn from(value: Lit) -> Self {
		BoolVal::Lit(value)
	}
}

impl From<Var> for BoolVal {
	fn from(value: Var) -> Self {
		BoolVal::Lit(value.into())
	}
}

impl From<bool> for BoolVal {
	fn from(value: bool) -> Self {
		BoolVal::Const(value)
	}
}

impl Not for BoolVal {
	type Output = BoolVal;

	fn not(self) -> Self::Output {
		match self {
			BoolVal::Lit(l) => (!l).into(),
			BoolVal::Const(b) => (!b).into(),
		}
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
		VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			self.nvar.next_var.unwrap().prev_var().unwrap(),
		)
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

	/// Returns the number of variables in the formula.
	pub fn num_vars(&self) -> usize {
		self.nvar.num_emitted_vars()
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

impl Add<Lit> for Coeff {
	type Output = BoolLinExp;

	fn add(self, rhs: Lit) -> Self::Output {
		rhs + self
	}
}

impl Mul<Lit> for Coeff {
	type Output = BoolLinExp;

	fn mul(self, rhs: Lit) -> Self::Output {
		rhs * self
	}
}

impl<Db: ClauseDatabase + ?Sized> ClauseDatabaseTools for Db {}

impl<F: Fn(Lit) -> bool> Valuation for F {
	fn value(&self, lit: Lit) -> bool {
		self(lit)
	}
}

impl Lit {
	/// Coerce a non-zero integer into a literal.
	///
	/// ### Warning
	/// This method is only safe to use if the input integer is known to be a
	/// integer coerced from a literal part of the same formula. Otherwise, the
	/// usage of the literal may lead to undefined behavior.
	pub fn from_raw(value: NonZeroI32) -> Lit {
		Lit(value)
	}

	/// Returns whether the literal is a negation of the underlying variable.
	pub fn is_negated(&self) -> bool {
		self.0.is_negative()
	}

	/// Returns the underlying variable of the literal, whether negated or not.
	pub fn var(&self) -> Var {
		Var(self.0.abs())
	}
}

impl Add for Lit {
	type Output = BoolLinExp;

	fn add(self, rhs: Self) -> Self::Output {
		BoolLinExp::from_terms(&[(self, 1), (rhs, 1)])
	}
}

impl Add<Coeff> for Lit {
	type Output = BoolLinExp;

	fn add(self, rhs: Coeff) -> Self::Output {
		BoolLinExp::from_terms(&[(self, 1)]) + rhs
	}
}

impl BitAnd<BoolVal> for Lit {
	type Output = Formula<BoolVal>;

	fn bitand(self, rhs: BoolVal) -> Self::Output {
		rhs & self
	}
}

impl BitAnd<Lit> for Lit {
	type Output = Formula<Lit>;

	fn bitand(self, rhs: Lit) -> Self::Output {
		Formula::And(vec![Formula::Atom(self), Formula::Atom(rhs)])
	}
}

impl BitAnd<bool> for Lit {
	type Output = BoolVal;

	fn bitand(self, rhs: bool) -> Self::Output {
		if rhs {
			self.into()
		} else {
			false.into()
		}
	}
}

impl BitOr<BoolVal> for Lit {
	type Output = Formula<BoolVal>;

	fn bitor(self, rhs: BoolVal) -> Self::Output {
		rhs | self
	}
}

impl BitOr<Lit> for Lit {
	type Output = Formula<Lit>;

	fn bitor(self, rhs: Lit) -> Self::Output {
		Formula::Or(vec![Formula::Atom(self), Formula::Atom(rhs)])
	}
}

impl BitOr<bool> for Lit {
	type Output = BoolVal;

	fn bitor(self, rhs: bool) -> Self::Output {
		if rhs {
			true.into()
		} else {
			self.into()
		}
	}
}

impl BitXor<BoolVal> for Lit {
	type Output = Formula<BoolVal>;

	fn bitxor(self, rhs: BoolVal) -> Self::Output {
		rhs ^ self
	}
}

impl BitXor<Lit> for Lit {
	type Output = Formula<Lit>;

	fn bitxor(self, rhs: Lit) -> Self::Output {
		Formula::Xor(vec![Formula::Atom(self), Formula::Atom(rhs)])
	}
}

impl BitXor<bool> for Lit {
	type Output = Lit;

	fn bitxor(self, rhs: bool) -> Self::Output {
		if rhs {
			!self
		} else {
			self
		}
	}
}

impl Display for Lit {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{}{}",
			if self.is_negated() { "¬" } else { "" },
			self.var()
		)
	}
}

impl From<Var> for Lit {
	fn from(value: Var) -> Self {
		Lit(value.0)
	}
}

impl Mul<Coeff> for Lit {
	type Output = BoolLinExp;

	fn mul(self, rhs: Coeff) -> Self::Output {
		BoolLinExp::from_terms(&[(self, rhs)])
	}
}

impl Not for Lit {
	type Output = Lit;

	fn not(self) -> Self::Output {
		Lit(-self.0)
	}
}

impl Ord for Lit {
	fn cmp(&self, other: &Self) -> Ordering {
		match self.var().cmp(&other.var()) {
			Ordering::Equal => (self.is_negated()).cmp(&other.is_negated()),
			r => r,
		}
	}
}

impl PartialOrd for Lit {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl From<Lit> for NonZeroI32 {
	fn from(val: Lit) -> Self {
		val.0
	}
}

impl From<Var> for NonZeroI32 {
	fn from(val: Var) -> Self {
		val.0
	}
}

impl Display for Unsatisfiable {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Problem inconsistency detected")
	}
}

impl Error for Unsatisfiable {}

impl Var {
	const MAX_VARS: usize = NonZeroI32::MAX.get() as usize;

	fn checked_add(&self, b: NonZeroI32) -> Option<Var> {
		self.0
			.get()
			.checked_add(b.get())
			.map(|v| Var(NonZeroI32::new(v).unwrap()))
	}

	fn next_var(&self) -> Option<Var> {
		const ONE: NonZeroI32 = NonZeroI32::new(1).unwrap();
		self.checked_add(ONE)
	}

	fn prev_var(&self) -> Option<Var> {
		let prev = self.0.get() - 1;
		if prev > 0 {
			Some(Var(NonZeroI32::new(prev).unwrap()))
		} else {
			None
		}
	}
}

impl Display for Var {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "x{}", subscript_number(self.0.get() as usize).format(""))
	}
}

impl Not for Var {
	type Output = Lit;

	fn not(self) -> Self::Output {
		!Lit::from(self)
	}
}

impl VarRange {
	/// Create an empty variable range
	pub fn empty() -> Self {
		Self {
			start: Var(NonZeroI32::new(2).unwrap()),
			end: Var(NonZeroI32::new(1).unwrap()),
		}
	}

	/// Returns the upper bound of the variable range (inclusive).
	///
	/// Note: the value returned by this method is unspecified after the range
	/// has been iterated to exhaustion.
	pub fn end(&self) -> Var {
		self.end
	}

	/// Find the index of a variable within the range
	pub fn find(&self, var: Var) -> Option<usize> {
		if !self.contains(&var) {
			None
		} else {
			let offset = (var.0.get() - self.start.0.get()) as usize;
			debug_assert!(offset <= self.len());
			Some(offset)
		}
	}

	/// Performs the indexing operation into the variable range
	pub fn index(&self, index: usize) -> Var {
		if index >= self.len() {
			panic!("out of bounds access");
		}
		if index == 0 {
			self.start
		} else {
			let index = NonZeroI32::new(index as i32).unwrap();
			self.start.checked_add(index).unwrap()
		}
	}

	/// Returns `true` if the range contains no items.
	///
	/// # Examples
	///
	/// ```
	/// # use pindakaas::VarRange;
	/// assert!(VarRange::empty().is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.start > self.end
	}

	/// Returns an iterator of the Boolean variables in the range represented as
	/// [`Lit`]s.
	pub fn iter_lits(&mut self) -> impl Iterator<Item = Lit> + '_ {
		self.map(Lit::from)
	}

	/// Create a range starting from `start` and ending at `end` (inclusive)
	pub fn new(start: Var, end: Var) -> Self {
		Self { start, end }
	}

	/// Returns the lower bound of the variable range (inclusive).
	///
	/// Note: the value returned by this method is unspecified after the range
	/// has been iterated to exhaustion.
	pub fn start(&self) -> Var {
		self.start
	}
}

impl DoubleEndedIterator for VarRange {
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.start <= self.end {
			let item = self.end;
			if let Some(prev) = self.end.prev_var() {
				self.end = prev;
			} else {
				*self = VarRange::empty();
			}
			Some(item)
		} else {
			None
		}
	}
}

impl ExactSizeIterator for VarRange {
	fn len(&self) -> usize {
		let (lower, upper) = self.size_hint();
		debug_assert_eq!(upper, Some(lower));
		lower
	}
}

impl From<RangeInclusive<Var>> for VarRange {
	fn from(value: RangeInclusive<Var>) -> Self {
		VarRange::new(*value.start(), *value.end())
	}
}

impl FusedIterator for VarRange {}

impl Iterator for VarRange {
	type Item = Var;

	fn count(self) -> usize {
		let (lower, upper) = self.size_hint();
		debug_assert_eq!(upper, Some(lower));
		lower
	}

	fn next(&mut self) -> Option<Self::Item> {
		if self.start <= self.end {
			let item = self.start;
			self.start = self.start.next_var().unwrap();
			Some(item)
		} else {
			None
		}
	}
	fn size_hint(&self) -> (usize, Option<usize>) {
		let size = max(self.end.0.get() - self.start.0.get() + 1, 0) as usize;
		(size, Some(size))
	}
}

impl RangeBounds<Var> for VarRange {
	fn end_bound(&self) -> Bound<&Var> {
		Bound::Included(&self.end)
	}
	fn start_bound(&self) -> Bound<&Var> {
		Bound::Included(&self.start)
	}
}

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

	/// Returns the number of clauses in the formula.
	pub fn num_clauses(&self) -> usize {
		self.cnf.num_clauses()
	}

	/// Returns the number of variables in the formula.
	pub fn num_vars(&self) -> usize {
		self.cnf.num_vars()
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

impl From<Lit> for i32 {
	fn from(val: Lit) -> Self {
		val.0.get()
	}
}

impl From<Var> for i32 {
	fn from(val: Var) -> Self {
		val.0.get()
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
