//! Encoding propositional, pseudo-Boolean, and integer constraints into CNF.
//!
//! Pindakaas lets a model use the representation that matches the problem and
//! lets each encoder choose the Boolean representation that matches its
//! algorithm. Constraints are normalised and specialised before encoding, so
//! an at-most-one group, a cardinality constraint, and a weighted sum do not
//! all pay for the same general-purpose encoding.
//!
//! Encoders write to [`ClauseDatabase`]. [`Cnf`] stores clauses for inspection
//! or DIMACS output; enabled SAT solvers accept them directly. The
//! [`ClauseDatabaseTools`] extension allocates variables, folds constant
//! Boolean values out of clauses, and dispatches encoders.
//!
//! # Clauses and solving
//!
//! A formula can be built directly as clauses, then passed to a solver:
//!
//! ```rust
//! use pindakaas::{solver::{cadical::Cadical, SolveResult, Solver},
//!     ClauseDatabaseTools, Cnf, Valuation};
//!
//! let mut cnf = Cnf::default();
//! let (x, y, z) = cnf.new_lits();
//! cnf.add_clause([!x, y])?;
//! cnf.add_clause([!y, z])?;
//! cnf.add_clause([!z, x])?;
//! let mut solver = Cadical::from(&cnf);
//! let SolveResult::Satisfied(model) = solver.solve() else {
//!     unreachable!("the implications have a model");
//! };
//! assert_eq!(model.value(x), model.value(y));
//! assert_eq!(model.value(y), model.value(z));
//! # Ok::<(), pindakaas::Unsatisfiable>(())
//! ```
//!
//! Solver backends are feature-gated. CaDiCaL is enabled by default; Kissat,
//! Intel SAT, SPLR, and runtime-loaded IPASIR libraries are available through
//! their corresponding features.
//!
//! # Propositional formulas
//!
//! [`Formula`](constraint::propositional_logic::Formula) supports conjunction,
//! disjunction, exclusive-or, implication, equivalence, negation, and
//! if-then-else. [`TseitinEncoder`](encoder::tseitin::TseitinEncoder) gives
//! compound sub-formulas representative literals instead of distributing them
//! into exponentially many clauses.
//!
//! ```rust
//! use pindakaas::{constraint::propositional_logic::{Formula, TseitinEncoder},
//!     ClauseDatabaseTools, Cnf};
//! let mut cnf = Cnf::default();
//! let (x, y, z) = cnf.new_lits();
//! cnf.encode(&((x ^ y) | z), &TseitinEncoder)?;
//! let choose = Formula::IfThenElse { cond: Box::new(Formula::Atom(x)),
//!     then: Box::new(Formula::Atom(y)), els: Box::new(Formula::Atom(z)) };
//! cnf.encode(&choose, &TseitinEncoder)?;
//! # Ok::<(), pindakaas::Unsatisfiable>(())
//! ```
//!
//! [`Linear`](constraint::linear::Linear) expressions are normalised and
//! specialised by [`LinearEncoder`](encoder::aggregate::LinearEncoder) before
//! encoding. The usual arithmetic operators build weighted sums. At-most-one
//! groups must be supplied by the caller; aggregation does not discover them.
//!
//! ```rust
//! use pindakaas::{constraint::{cardinality_one::BitwiseEncoder,
//!     linear::{AdderEncoder, Comparator, Linear, LinearEncoder, StaticLinEncoder}},
//!     encoder::sorting_network::SortingNetworkEncoder,
//!     ClauseDatabaseTools, Cnf};
//! let mut cnf = Cnf::default();
//! let (x, y, z) = cnf.new_lits();
//! let budget = Linear::new(2 * x + 3 * y + 2 * z, Comparator::LessEq, 4);
//! let encoder = LinearEncoder::<StaticLinEncoder<AdderEncoder, AdderEncoder,
//!     AdderEncoder, BitwiseEncoder, SortingNetworkEncoder>>::default();
//! cnf.encode(&budget, &encoder)?;
//! # Ok::<(), pindakaas::Unsatisfiable>(())
//! ```
//!
//! [`IntVar`](decision::integer::IntVar) creates order, direct, and binary
//! views on demand and channels them to the same value. Mixing views costs
//! clauses proportional to the domain size.
//!
//! ```rust
//! use pindakaas::{constraint::linear::{Comparator, Linear},
//!     decision::integer::IntVar, ClauseDatabaseTools, Cnf};
//! let mut cnf = Cnf::default();
//! let x = IntVar::new(0..=8).with_label("x");
//! let y = IntVar::new(0..=7).with_label("y");
//! let budget = Linear::new(x.clone() * 3 + y.clone() * 2, Comparator::LessEq, 20);
//! cnf.encode(
//!     &budget,
//!     &pindakaas::encoder::aggregate::LinearEncoder::<
//!         pindakaas::encoder::aggregate::StaticLinEncoder,
//!     >::default(),
//! )?;
//! let x_at_least_four = x.lit_at_least(&mut cnf, 4)?;
//! cnf.add_clause([x_at_least_four])?;
//! # Ok::<(), pindakaas::Unsatisfiable>(())
//! ```
//!
//! # Choosing an encoder
//!
//! Aggregation turns a constraint into a specialised form before encoding.
//! `int` means
//! [`NormalizedIntLinear`](constraint::int_linear::NormalizedIntLinear), `bool`
//! means [`NormalizedBoolLinear`](constraint::bool_linear::NormalizedBoolLinear),
//! `card` means [`Cardinality`](constraint::cardinality::Cardinality), `amo`
//! means [`CardinalityOne`](constraint::cardinality_one::CardinalityOne), and
//! `count` means [`Count`](constraint::count::Count). A supplied at-most-one
//! group is represented by an integer term, which is how the generalised
//! encodings below become available.
//!
//! The table uses **GAC** for domain consistency (unit propagation removes
//! every value that cannot occur in a solution) and **CC** for consistency
//! checking (unit propagation detects assignments that cannot be extended).
//! These are the default strengths; a cutoff may trade propagation for a
//! smaller encoding.
//!
//! | Encoder | Takes | Also known as; references | Default strength |
//! |---|---|---|---|
//! | [`AdderEncoder`](encoder::adder::AdderEncoder) | int, bool, card, amo, count | Adder network [^warners][^een] | neither GAC nor CC |
//! | [`DecisionDiagramEncoder`](encoder::decision_diagram::DecisionDiagramEncoder) | int, bool, card, amo, count | MDD/BDD [^abio2012][^abio2011] | GAC |
//! | [`TotalizerEncoder`](encoder::totalizer::TotalizerEncoder) | int, bool, card, amo, count | Totalizer, GTE, GGT [^bailleux2003][^joshi][^bofill] | GAC |
//! | [`SequentialCounterEncoder`](encoder::sequential_counter::SequentialCounterEncoder) | int, bool, card, amo, count | Sequential counter, SWC, GSWC [^sinz][^holldobler][^bofill] | GAC |
//! | [`MixedRadixEncoder`](encoder::mixed_radix::MixedRadixEncoder) | int, bool, card, amo, count | MTO, GMTO [^ogawa][^zha][^bofill] | neither GAC nor CC |
//! | [`WatchdogEncoder`](encoder::watchdog::WatchdogEncoder) | int, bool, card, amo, count | GPW/GGPW (global), LPW/GLPW (local) [^bailleux2009][^bofill] | CC / GAC |
//! | [`SortingNetworkEncoder`](encoder::sorting_network::SortingNetworkEncoder) | card, amo, count | Cardinality network [^asin][^batcher] | GAC |
//! | [`PairwiseEncoder`](encoder::pairwise::PairwiseEncoder) | amo | Pairwise/binomial | GAC |
//! | [`BitwiseEncoder`](encoder::bitwise::BitwiseEncoder) | amo | Bitwise/binary [^frisch] | weak propagation |
//! | [`LadderEncoder`](encoder::ladder::LadderEncoder) | amo | Ladder/regular [^gent][^ansotegui] | not classified |
//! | [`ProductEncoder`](encoder::product::ProductEncoder) | amo | Product [^chen] | not classified |
//! | [`TseitinEncoder`](encoder::tseitin::TseitinEncoder) | formulas | Tseitin transformation [^tseitin] | — |
//!
//! The linear and cardinality encoders are domain consistent at their default
//! configuration where documented. Setting `with_cutoff(Some(..))` selects
//! binary intermediate views and ripple-carry arithmetic, which can weaken
//! propagation while preserving the same solutions. `with_local(true)` is
//! the watchdog's domain-consistent form. `with_base` records the deliberate
//! radix choices for mixed-radix encoding.
//!
//! The [`encoder`] modules document algorithm choices and configuration. Their
//! item docs contain usage examples. CaDiCaL is enabled by default; other
//! solver backends are feature-gated.
//!
//! [^abio2011]: I. Abío, R. Nieuwenhuis, A. Oliveras, E. Rodríguez-Carbonell,
//! "BDDs for Pseudo-Boolean Constraints — Revisited", SAT 2011, LNCS 6695,
//! 61–75.
//!
//! [^abio2012]: I. Abío, R. Nieuwenhuis, A. Oliveras, E. Rodríguez-Carbonell,
//! V. Mayer-Eichberger, "A New Look at BDDs for Pseudo-Boolean Constraints",
//! Journal of Artificial Intelligence Research 45 (2012) 443–480.
//!
//! [^ansotegui]: C. Ansótegui, F. Manyà, "Mapping Problems with Finite-Domain
//! Variables into Problems with Boolean Variables", SAT 2004, LNCS 3542, 1–15.
//!
//! [^asin]: R. Asín, R. Nieuwenhuis, A. Oliveras, E. Rodríguez-Carbonell,
//! "Cardinality Networks: a theoretical and empirical study", Constraints
//! 16(2) (2011) 195–221.
//!
//! [^bailleux2003]: O. Bailleux, Y. Boufkhad, "Efficient CNF Encoding of
//! Boolean Cardinality Constraints", CP 2003, LNCS 2833, 108–122.
//!
//! [^bailleux2009]: O. Bailleux, Y. Boufkhad, O. Roussel, "New Encodings of
//! Pseudo-Boolean Constraints into CNF", SAT 2009, LNCS 5584, 181–194.
//!
//! [^batcher]: K. E. Batcher, "Sorting networks and their applications", AFIPS
//! Spring Joint Computing Conference 1968, 307–314.
//!
//! [^bofill]: M. Bofill, J. Coll, P. Nightingale, J. Suy, F. Ulrich-Oltean, M.
//! Villaret, "SAT encodings for pseudo-Boolean constraints together with
//! at-most-one constraints", Artificial Intelligence 302 (2022) 103604.
//!
//! [^chen]: J. Chen, "A New SAT Encoding of the At-Most-One Constraint",
//! ModRef 2010.
//!
//! [^een]: N. Eén, N. Sörensson, "Translating Pseudo-Boolean Constraints into
//! SAT", Journal on Satisfiability, Boolean Modeling and Computation 2 (2006)
//! 1–26.
//!
//! [^frisch]: A. M. Frisch, T. J. Peugniez, A. J. Doggett, P. W. Nightingale,
//! "Solving Non-Boolean Satisfiability Problems with Stochastic Local Search",
//! Journal of Automated Reasoning 35 (2005) 143–179.
//!
//! [^gent]: I. P. Gent, P. Nightingale, "A New Encoding of AllDifferent into
//! SAT", ModRef 2004.
//!
//! [^holldobler]: S. Hölldobler, N. Manthey, P. Steinke, "A Compact Encoding
//! of Pseudo-Boolean Constraints into SAT", KI 2012, LNCS 7526, 107–118.
//!
//! [^joshi]: S. Joshi, R. Martins, V. Manquinho, "Generalized Totalizer
//! Encoding for Pseudo-Boolean Constraints", CP 2015, LNCS 9255, 200–209.
//!
//! [^ogawa]: T. Ogawa, Y. Liu, R. Hasegawa, M. Koshimura, H. Fujita, "Modulo
//! Based CNF Encoding of Cardinality Constraints and Its Application to MaxSAT
//! Solvers", ICTAI 2013, 9–17.
//!
//! [^sinz]: C. Sinz, "Towards an Optimal CNF Encoding of Boolean Cardinality
//! Constraints", CP 2005, LNCS 3709, 827–832.
//!
//! [^tseitin]: G. S. Tseitin, "On the complexity of derivation in propositional
//! calculus", Studies in Constructive Mathematics and Mathematical Logic II
//! (1968) 115–125.
//!
//! [^warners]: J. P. Warners, "A linear-time transformation of linear
//! inequalities into conjunctive normal form", Information Processing Letters
//! 68 (1998) 63–69.
//!
//! [^zha]: A. Zha, M. Koshimura, H. Fujita, "N-level modulo-based CNF encodings
//! of cardinality constraints", ICTAI 2014, 428–435.
//!
//! The Python bindings expose the same modelling concepts through
//! [pyndakaas](https://pindakaas.readthedocs.io/en/latest/).
//!
//! Software citation:
//! [doi:10.5281/zenodo.10851855](https://doi.org/10.5281/zenodo.10851855).
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
	cell::RefCell,
	cmp::Ordering,
	error::Error,
	fmt::{self, Display},
	fs::File,
	io::{self, BufRead, BufReader, Write},
	iter::repeat_n,
	num::NonZeroI32,
	ops::{Deref, DerefMut},
	path::Path,
	slice,
};

// The benchmarks are the only target that uses it, and the lint is per-target.
#[cfg(test)]
use divan as _;
use itertools::{traits::HomogeneousTuple, Itertools};
pub use rangelist::{IntervalIterator, RangeList};

use crate::solver::VarFactory;
pub use crate::{
	decision::boolean::{BoolVal, Lit, Var, VarRange},
	helpers::AsDynClauseDatabase,
};

/// Testing a constraint against a complete assignment.
pub trait Checker {
	/// Checks whether the assignment satisfies the constraint.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the assignment violates the constraint.
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result<(), Unsatisfiable>;
}

/// Destination for clauses and fresh variables emitted by an encoder.
pub trait ClauseDatabase {
	/// Adds one clause, including the empty clause.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when adding the clause proves the database
	/// inconsistent.
	fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result;

	/// Allocates a contiguous range unused by every earlier call.
	fn new_var_range(&mut self, len: usize) -> VarRange;
}

thread_local! {
	/// Scratch space for the literals of one clause.
	static CLAUSE: RefCell<Vec<Lit>> = const { RefCell::new(Vec::new()) };
}

/// Borrow the scratch space for one clause, empty.
///
/// Taken out of the thread-local rather than borrowed from it, so that a
/// database whose [`ClauseDatabase::add_clause_from_slice`] emits a clause of
/// its own does not find the buffer already in use; that nested call allocates
/// a buffer of its own instead.
fn clause_buffer() -> impl DerefMut<Target = Vec<Lit>> {
	/// The buffer, put back where it came from once the clause is written.
	struct Borrowed(Vec<Lit>);
	impl Deref for Borrowed {
		type Target = Vec<Lit>;
		fn deref(&self) -> &Vec<Lit> {
			&self.0
		}
	}
	impl DerefMut for Borrowed {
		fn deref_mut(&mut self) -> &mut Vec<Lit> {
			&mut self.0
		}
	}
	impl Drop for Borrowed {
		fn drop(&mut self) {
			let mut buffer = std::mem::take(&mut self.0);
			buffer.clear();
			CLAUSE.with(|c| {
				if let Ok(mut slot) = c.try_borrow_mut() {
					*slot = buffer;
				}
			});
		}
	}
	Borrowed(CLAUSE.with(|c| {
		c.try_borrow_mut()
			.map(|mut slot| std::mem::take(&mut *slot))
			.unwrap_or_default()
	}))
}

/// Clause and variable conveniences available to every [`ClauseDatabase`].
pub trait ClauseDatabaseTools: ClauseDatabase {
	/// Adds a clause after folding away constant Boolean values.
	///
	/// A true value satisfies the clause without changing the database; false
	/// values are omitted.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the reduced clause proves the database
	/// inconsistent.
	fn add_clause<Iter>(&mut self, clause: Iter) -> Result
	where
		Iter: IntoIterator,
		Iter::Item: Into<BoolVal>,
	{
		// Every clause an encoder emits passes through here, so the space the
		// literals are gathered in is borrowed rather than allocated afresh.
		let mut buffer = clause_buffer();
		let mut satisfied = false;
		for v in clause {
			match v.into() {
				BoolVal::Const(false) => {}
				BoolVal::Const(true) => {
					satisfied = true;
					break;
				}
				BoolVal::Lit(lit) => buffer.push(lit),
			}
		}
		if satisfied {
			return Ok(());
		}
		let result = self.add_clause_from_slice(&buffer);
		#[cfg(any(feature = "tracing", test))]
		{
			tracing::info!(clause = ?&*buffer, fail = result.is_err(), "emit clause");
		}
		result
	}

	/// Records an already-detected contradiction as an empty clause.
	///
	/// # Errors
	///
	/// Always returns [`Unsatisfiable`] after offering the empty clause to the
	/// database.
	fn contradiction(&mut self) -> Result {
		let err = self.add_clause_from_slice(&[]);
		debug_assert_eq!(err, Err(Unsatisfiable));
		err
	}

	/// Encodes a constraint into this database with the selected encoder.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] under the conditions documented by
	/// [`Encoder::encode`].
	fn encode<C, E>(&mut self, constraint: &C, encoder: &E) -> Result
	where
		C: ?Sized,
		E: Encoder<Self, C> + ?Sized,
	{
		encoder.encode(self, constraint)
	}

	/// Encodes `conditions -> constraint` by guarding every emitted clause.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the guarded clauses make the database
	/// inconsistent.
	fn encode_implied<C, E>(&mut self, conditions: &[Lit], constraint: &C, encoder: &E) -> Result
	where
		C: ?Sized,
		E: Encoder<Self, C> + ?Sized + for<'a> Encoder<dyn ClauseDatabase + 'a, C>,
	{
		encoder.encode_implied(self, conditions, constraint)
	}

	/// Allocates a fresh Boolean variable as a positive literal.
	fn new_lit(&mut self) -> Lit {
		self.new_var().into()
	}

	/// Allocates fresh Boolean literals and returns them in a tuple.
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
	/// Allocates a fresh Boolean variable as a positive literal. The
	/// given name is used when the variable is output by the tracer.
	fn new_named_lit(&mut self, name: &str) -> Lit {
		self.new_named_var(name).into()
	}

	#[cfg(any(feature = "tracing", test))]
	#[inline]
	/// Allocates a fresh Boolean variable that can be used in the encoding of a
	/// problem. The given name is used when the variable is output by the
	/// tracer.
	fn new_named_var(&mut self, name: &str) -> Var {
		let var = self.new_var();
		tracing::info!(var = ?i32::from(var), label = name, "new variable");
		var
	}

	/// Allocates a fresh Boolean variable that can be used in the encoding of a
	/// problem or constraint.
	fn new_var(&mut self) -> Var {
		let mut range = self.new_var_range(1);
		debug_assert_eq!(range.len(), 1);
		range.next().unwrap()
	}

	/// Allocates fresh Boolean variables and returns them in a tuple.
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

/// In-memory conjunctive normal form with DIMACS input and output.
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

/// Coefficient representation shared by constraints and expressions.
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

/// Encoding result with [`Unsatisfiable`] as its default error.
type Result<T = (), E = Unsatisfiable> = std::result::Result<T, E>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
/// Claim that the clauses or constraint cannot be satisfied.
pub struct Unsatisfiable;

/// Truth values supplied by a complete solver model.
pub trait Valuation {
	/// Returns the literal's truth value.
	fn value(&self, lit: Lit) -> bool;
}

/// Weighted CNF whose unweighted clauses are hard.
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
				wcnf.cnf.nvar = VarFactory {
					next_var: Some(Var(vec[2].parse::<NonZeroI32>().map_err(|_| {
						io::Error::new(
							io::ErrorKind::InvalidInput,
							"unable to parse number of variables",
						)
					})?)),
				};
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
	/// Parses a CNF formula from DIMACS input.
	///
	/// # Errors
	///
	/// An I/O error for unreadable input or a malformed header.
	///
	/// # Panics
	///
	/// Malformed clause data may currently panic instead of returning an error.
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
			None => VarRange::empty(),
		}
	}

	/// Iterates over the clauses in insertion order.
	pub fn iter(&self) -> impl ExactSizeIterator<Item = &[Lit]> + '_ {
		CnfIterator {
			lits: &self.lits,
			size: self.size.iter(),
			index: 0,
		}
	}

	/// Counts the literals in the formula.
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

	/// Writes the formula to `path` in DIMACS format.
	///
	/// Each line of `comment` is prefixed with the DIMACS comment marker.
	///
	/// # Errors
	///
	/// An I/O error when the file cannot be created or fully written.
	pub fn to_file(&self, path: &Path, comment: Option<&str>) -> Result<(), io::Error> {
		let mut file = File::create(path)?;
		if let Some(comment) = comment {
			for line in comment.lines() {
				writeln!(file, "c {line}")?;
			}
		}
		write!(file, "{self}")
	}

	/// Returns the range of variables emitted for this formula.
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
	/// Adds a weighted clause to the formula.
	///
	/// Constant values are folded as for [`ClauseDatabaseTools::add_clause`].
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the reduced clause is empty.
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

	/// Parses a weighted CNF formula from WCNF input.
	///
	/// # Errors
	///
	/// An I/O error for unreadable input or a malformed header.
	///
	/// # Panics
	///
	/// WCNF header and clause parsing currently contain unchecked assumptions;
	/// syntactically plausible input can panic.
	pub fn from_file(path: &Path) -> Result<Self, io::Error> {
		match parse_dimacs_file::<true>(path)? {
			Dimacs::Wcnf(wcnf) => Ok(wcnf),
			_ => unreachable!(),
		}
	}

	/// Iterates over clauses and their weights in insertion order.
	pub fn iter(&self) -> impl ExactSizeIterator<Item = (&[Lit], &Option<Coeff>)> {
		self.cnf.iter().zip(self.weights.iter())
	}

	/// Counts the literals in the formula.
	pub fn literals(&self) -> usize {
		self.cnf.literals()
	}

	/// Counts the clauses in the formula.
	pub fn num_clauses(&self) -> usize {
		self.cnf.num_clauses()
	}

	/// Counts the variables in the formula.
	pub fn num_vars(&self) -> usize {
		self.cnf.num_vars()
	}

	/// Writes the formula to `path` in WCNF format.
	///
	/// Each line of `comment` is prefixed with the DIMACS comment marker.
	///
	/// # Errors
	///
	/// An I/O error when the file cannot be created or fully written.
	pub fn to_file(&self, path: &Path, comment: Option<&str>) -> Result<(), io::Error> {
		let mut file = File::create(path)?;
		if let Some(comment) = comment {
			for line in comment.lines() {
				writeln!(file, "c {line}")?;
			}
		}
		write!(file, "{self}")
	}

	/// Returns the range of variables emitted for this formula.
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
