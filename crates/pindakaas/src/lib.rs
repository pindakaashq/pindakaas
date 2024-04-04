//! `pindakaas` is a collection of encoders to transform integer and
//! pseudo-Boolean (PB) constraints into conjunctive normal form (CNF). It
//! currently considers mostly linear constraints, which are in the form ∑
//! aᵢ·xᵢ ≷ k, where the aᵢ's and k are constant, xᵢ's are integer variables
//! or boolean literals, and ≷ can be the relationship ≤, =, or ≥. Two forms
//! of PB constraints are seen as special forms of PB constraints: ensuring a
//! set of booleans is *At Most One (AMO)* or *At Most K (AMK)*. Specialised
//! encodings are used when these cases are detected.

use std::{
	clone::Clone,
	cmp::{Eq, Ordering},
	error::Error,
	fmt::{self, Display},
	fs::File,
	hash::Hash,
	io::{self, BufRead, BufReader, Write},
	num::NonZeroI32,
	ops::Not,
	path::Path,
};

use helpers::VarRange;
use itertools::{Itertools, Position};
use solver::{NextVarRange, VarFactory};

mod cardinality;
mod cardinality_one;
pub(crate) mod helpers;
mod int;
mod linear;
pub mod solver;
mod sorted;
pub mod trace;

use crate::trace::subscript_number;
pub use crate::{
	cardinality::{Cardinality, SortingNetworkEncoder},
	cardinality_one::{BitwiseEncoder, CardinalityOne, LadderEncoder, PairwiseEncoder},
	linear::{
		AdderEncoder, BddEncoder, Comparator, LimitComp, LinExp, LinVariant, Linear,
		LinearAggregator, LinearConstraint, LinearEncoder, SwcEncoder, TotalizerEncoder,
	},
	sorted::{SortedEncoder, SortedStrategy},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub(crate) NonZeroI32);

impl Var {
	fn next_var(&self) -> Option<Var> {
		const ONE: NonZeroI32 = unsafe { NonZeroI32::new_unchecked(1) };
		self.checked_add(ONE)
	}

	fn prev_var(&self) -> Option<Var> {
		let prev = self.0.get() - 1;
		if prev >= 0 {
			Some(Var(NonZeroI32::new(prev).unwrap()))
		} else {
			None
		}
	}

	fn checked_add(&self, b: NonZeroI32) -> Option<Var> {
		self.0
			.get()
			.checked_add(b.get())
			.map(|v| Var(NonZeroI32::new(v).unwrap()))
	}
}

impl Not for Var {
	type Output = Lit;
	fn not(self) -> Self::Output {
		!Lit::from(self)
	}
}
impl Not for &Var {
	type Output = Lit;
	fn not(self) -> Self::Output {
		!*self
	}
}

impl Display for Var {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "x{}", subscript_number(self.0.get() as usize).format(""))
	}
}

impl From<Var> for NonZeroI32 {
	fn from(val: Var) -> Self {
		val.0
	}
}
impl From<Var> for i32 {
	fn from(val: Var) -> Self {
		val.0.get()
	}
}

/// Literal is type that can be use to represent Boolean decision variables and
/// their negations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lit(NonZeroI32);

impl Lit {
	pub fn var(&self) -> Var {
		Var(self.0.abs())
	}
	pub fn is_negated(&self) -> bool {
		self.0.is_negative()
	}
}

impl Not for Lit {
	type Output = Lit;
	fn not(self) -> Self::Output {
		Lit(-self.0)
	}
}
impl Not for &Lit {
	type Output = Lit;
	fn not(self) -> Self::Output {
		!(*self)
	}
}

impl PartialOrd for Lit {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}
impl Ord for Lit {
	fn cmp(&self, other: &Self) -> Ordering {
		match self.var().cmp(&other.var()) {
			std::cmp::Ordering::Equal => (self.is_negated()).cmp(&other.is_negated()),
			r => r,
		}
	}
}

impl From<Var> for Lit {
	fn from(value: Var) -> Self {
		Lit(value.0)
	}
}
impl From<Lit> for NonZeroI32 {
	fn from(val: Lit) -> Self {
		val.0
	}
}
impl From<Lit> for i32 {
	fn from(val: Lit) -> Self {
		val.0.get()
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

/// Unsatisfiable is an error type returned when the problem being encoded is
/// found to be inconsistent.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
pub struct Unsatisfiable;
impl Error for Unsatisfiable {}
impl fmt::Display for Unsatisfiable {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Problem inconsistency detected")
	}
}

/// Result is a type alias for [`std::result::Result`] that by default returns
/// an empty value, or the [`Unsatisfiable`] error type.
pub type Result<T = (), E = Unsatisfiable> = std::result::Result<T, E>;

/// A function that gives the valuation/truth-value for a given literal in the
/// current solution/model.
///
/// Note that the function can return None if the model/solution is independent
/// of the given literal.
pub trait Valuation: Fn(Lit) -> Option<bool> {}
impl<F: Fn(Lit) -> Option<bool>> Valuation for F {}

/// Encoder is the central trait implemented for all the encoding algorithms
pub trait Encoder<DB: ClauseDatabase, Constraint> {
	fn encode(&self, db: &mut DB, con: &Constraint) -> Result;
}

/// Checker is a trait implemented by types that represent constraints. The
/// [`Checker::check`] methods checks whether an assignment (often referred to
/// as a model) satisfies the constraint.
pub trait Checker {
	/// Check whether the constraint represented by the object is violated.
	///
	/// - The method returns [`Result::Ok`] when the assignment satisfies
	///   the constraint,
	/// - it returns [`Unsatisfiable`] when the assignment violates the
	///   constraint
	fn check<F: Valuation>(&self, value: F) -> Result<(), CheckError>;
}

/// Incomplete is a error type returned by a [`Checker`] type when the
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
pub struct Incomplete {
	missing: Box<[Lit]>,
}
impl Error for Incomplete {}
impl fmt::Display for Incomplete {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self.missing.len() {
			0 => write!(f, "Unknown literal is unasssigned"),
			1 => write!(f, "Literal {:?} is unasssigned", self.missing[0]),
			_ => {
				write!(f, "Literals")?;
				for (pos, lit) in self.missing.iter().with_position() {
					match pos {
						Position::First => write!(f, " {:?}", lit)?,
						Position::Middle => write!(f, ", {:?}", lit)?,
						Position::Last => write!(f, ", and {:?}", lit)?,
						_ => unreachable!(),
					}
				}
				write!(f, " are unasssigned")
			}
		}
	}
}

/// Enumerated type of
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
pub enum CheckError {
	Unsatisfiable(Unsatisfiable),
	Fail(String),
}
impl Error for CheckError {}
impl fmt::Display for CheckError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			CheckError::Fail(err) => err.fmt(f),
			CheckError::Unsatisfiable(err) => err.fmt(f),
		}
	}
}
impl From<Unsatisfiable> for CheckError {
	fn from(value: Unsatisfiable) -> Self {
		Self::Unsatisfiable(value)
	}
}

/// Coeff is a type alias used for the number type used to represent the
/// coefficients in pseudo-Boolean constraints and expression.
pub type Coeff = i64;

/// IntEncoding is a enumerated type use to represent Boolean encodings of
/// integer variables within this library
pub enum IntEncoding<'a> {
	/// The Direct variant represents a integer variable encoded using domain
	/// or direct encoding of an integer variable. Each given Boolean literal
	/// represents whether the integer takes the associated value (i.e., X =
	/// (first+i) ↔ vals\[i\]).
	Direct { first: Coeff, vals: &'a [Lit] },
	/// The Order variant represents a integer variable using an order
	/// encoding. Each given Boolean literal represents whether the integer
	/// is bigger than the associated value(i.e., X > (first+i) ↔ vals\[i\]).
	Order { first: Coeff, vals: &'a [Lit] },
	/// The Log variant represents a integer variable using a two's complement
	/// encoding. The sum of the Boolean literals multiplied by their
	/// associated power of two represents value of the integer (i.e., X = ∑
	/// 2ⁱ·bits\[i\]).
	Log { signed: bool, bits: &'a [Lit] },
}

/// The `ClauseDatabase` trait is the common trait implemented by types that are
/// used to manage the encoding of PB constraints and contain their output. This
/// trait can be used for all encoding methods in this library.
///
/// To satisfy the trait, the type must implement a [`Self::add_clause`] method
/// and a [`Self::new_var`] method.
pub trait ClauseDatabase {
	/// Method to be used to receive a new Boolean variable that can be used in
	/// the encoding of a problem or constriant.
	fn new_var(&mut self) -> Var;

	/// Add a clause to the `ClauseDatabase`. The databae is allowed to return
	/// [`Unsatisfiable`] when the collection of clauses has been *proven* to be
	/// unsatisfiable. This is used as a signal to the encoder that any subsequent
	/// encoding effort can be abandoned.
	///
	/// Clauses added this way cannot be removed. The addition of removable
	/// clauses can be simulated using activation literals and solving the problem
	/// under assumptions.
	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> Result;

	fn encode<C, E: Encoder<Self, C>>(&mut self, constraint: &C, encoder: &E) -> Result
	where
		Self: Sized,
	{
		encoder.encode(self, constraint)
	}
}

// TODO: Add usage and think about interface
pub struct ConditionalDatabase<'a, DB: ClauseDatabase> {
	db: &'a mut DB,
	conditions: &'a [Lit],
}
impl<'a, DB: ClauseDatabase> ConditionalDatabase<'a, DB> {
	pub fn new(db: &'a mut DB, conditions: &'a [Lit]) -> Self {
		Self { db, conditions }
	}
}
impl<'a, DB: ClauseDatabase> ClauseDatabase for ConditionalDatabase<'a, DB> {
	fn new_var(&mut self) -> Var {
		self.db.new_var()
	}

	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> Result {
		let chain = self.conditions.iter().copied().chain(cl);
		self.db.add_clause(chain)
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

/// A representation for a weighted CNF formula
///
/// Same as CNF, but every clause has an optional weight. Otherwise, it is a hard clause.
#[derive(Clone, Debug, Default)]
pub struct Wcnf {
	/// The CNF formula
	cnf: Cnf,
	/// The weight for every clause
	weights: Vec<Option<Coeff>>,
	// TODO this can be optimised, for example by having all weighted clauses at the start/end
}

// TODO not sure how to handle converting num_var for vars()
impl Cnf {
	/// Store CNF formula at given path in DIMACS format
	///
	/// File will optionally be prefaced by a given comment
	pub fn to_file(&self, path: &Path, comment: Option<&str>) -> Result<(), io::Error> {
		let mut file = File::create(path)?;
		if let Some(comment) = comment {
			for line in comment.lines() {
				writeln!(file, "c {line}")?
			}
		}
		write!(file, "{self}")
	}

	pub fn variables(&self) -> usize {
		self.nvar.emited_vars()
	}

	pub fn clauses(&self) -> usize {
		self.size.len()
	}

	pub fn literals(&self) -> usize {
		self.size.iter().sum()
	}
}

impl NextVarRange for Cnf {
	fn next_var_range(&mut self, size: usize) -> Option<VarRange> {
		self.nvar.next_var_range(size)
	}
}

impl From<Cnf> for Wcnf {
	fn from(cnf: Cnf) -> Self {
		let weights = std::iter::repeat(None).take(cnf.clauses()).collect();
		Wcnf { cnf, weights }
	}
}
impl From<Wcnf> for Cnf {
	// TODO implement iter for Cnf
	fn from(wcnf: Wcnf) -> Self {
		let mut start = 0;
		let lits_size = wcnf
			.cnf
			.size
			.iter()
			.zip(wcnf.weights.iter())
			.filter_map(|(size, weight)| {
				if weight.is_none() {
					let ret = (
						wcnf.cnf
							.lits
							.iter()
							.skip(start)
							.take(*size)
							.cloned()
							.collect_vec(),
						size,
					);
					start += size;
					Some(ret)
				} else {
					start += size;
					None
				}
			})
			.collect_vec();
		let lits = lits_size
			.iter()
			.flat_map(|lit_size| lit_size.0.clone())
			.collect();
		let size = lits_size.iter().map(|lit_size| *lit_size.1).collect_vec();
		Self {
			nvar: wcnf.cnf.nvar,
			lits,
			size,
		}
	}
}

impl Display for Wcnf {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let num_var = &self.cnf.nvar.emited_vars();
		let num_clauses = self.cnf.size.len();
		let top = self.weights.iter().flatten().fold(1, |a, b| a + *b);
		writeln!(f, "p wcnf {num_var} {num_clauses} {top}")?;
		let mut start = 0;
		for (size, weight) in self.cnf.size.iter().zip(self.weights.iter()) {
			let cl = self.cnf.lits.iter().skip(start).take(*size);
			let weight = weight.unwrap_or(top);
			write!(f, "{weight} ")?;
			for lit in cl {
				write!(f, "{lit} ")?;
			}
			writeln!(f, "0")?;
			start += size;
		}
		Ok(())
	}
}

impl Wcnf {
	/// Store WCNF formula at given path in WDIMACS format
	///
	/// File will optionally be prefaced by a given comment
	pub fn to_file(&self, path: &Path, comment: Option<&str>) -> Result<(), io::Error> {
		let mut file = File::create(path)?;
		if let Some(comment) = comment {
			for line in comment.lines() {
				writeln!(file, "c {line}")?
			}
		}
		write!(file, "{self}")
	}

	pub fn variables(&self) -> usize {
		self.cnf.variables()
	}

	pub fn clauses(&self) -> usize {
		self.cnf.clauses()
	}

	pub fn literals(&self) -> usize {
		self.cnf.literals()
	}
}

impl Display for Cnf {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let num_var = &self.variables();
		let num_clauses = self.size.len();
		writeln!(f, "p cnf {num_var} {num_clauses}")?;
		let mut start = 0;
		for size in self.size.iter() {
			let cl = self.lits.iter().skip(start).take(*size);
			for lit in cl {
				write!(f, "{lit} ")?
			}
			writeln!(f, "0")?;
			start += size;
		}
		Ok(())
	}
}

enum Dimacs {
	Cnf(Cnf),
	Wcnf(Wcnf),
}

fn parse_dimacs_file(path: &Path, expect_wcnf: bool) -> Result<Dimacs, io::Error> {
	let file = File::open(path)?;
	let mut had_header = false;

	let mut wcnf = Wcnf::default();

	let mut cl: Vec<Lit> = Vec::new();
	let mut top: Option<Coeff> = None;
	let weight: Option<Coeff> = None;

	for line in BufReader::new(file).lines() {
		match line {
			Ok(line) if line.is_empty() || line.starts_with('c') => (),
			Ok(line) if had_header => {
				for seg in line.split(' ') {
					if expect_wcnf {
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
							wcnf.add_weighted_clause(cl.drain(..), weight)
								.expect("CNF::add_clause does not return Unsatisfiable");
						} else {
							cl.push(Lit(NonZeroI32::new(lit).unwrap()));
						}
					}
				}
			}
			// parse header, expected format: "p cnf {num_var} {num_clauses}" or "p wcnf {num_var} {num_clauses} {top}"
			Ok(line) => {
				let vec: Vec<&str> = line.split_whitespace().collect();
				// check "p" and "cnf" keyword
				if !expect_wcnf && (vec.len() != 4 || vec[0..2] != ["p", "cnf"]) {
					return Err(io::Error::new(
						io::ErrorKind::InvalidInput,
						"expected DIMACS CNF header formatted \"p cnf {variables} {clauses}\"",
					));
				} else if expect_wcnf && (vec.len() != 4 || vec[0..2] != ["p", "wcnf"]) {
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

				if expect_wcnf {
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

	if expect_wcnf {
		Ok(Dimacs::Wcnf(wcnf))
	} else {
		Ok(Dimacs::Cnf(Cnf::from(wcnf)))
	}
}

impl Cnf {
	/// Read a CNF formula from a file formatted in the DIMACS CNF format
	pub fn from_file(path: &Path) -> Result<Self, io::Error> {
		match parse_dimacs_file(path, false)? {
			Dimacs::Cnf(cnf) => Ok(cnf),
			_ => unreachable!(),
		}
	}
}

impl Wcnf {
	/// Read a WCNF formula from a file formatted in the (W)DIMACS WCNF format
	pub fn from_file(path: &Path) -> Result<Self, io::Error> {
		match parse_dimacs_file(path, true)? {
			Dimacs::Wcnf(wcnf) => Ok(wcnf),
			_ => unreachable!(),
		}
	}
}

impl ClauseDatabase for Cnf {
	fn new_var(&mut self) -> Var {
		self.nvar.next().expect("exhausted variable pool")
	}

	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> Result {
		let size = self.lits.len();
		self.lits.extend(cl);
		let len = self.lits.len() - size;
		if len > 0 {
			self.size.push(len);
		}
		Ok(())
	}
}

impl Wcnf {
	pub fn add_weighted_clause<I: IntoIterator<Item = Lit>>(
		&mut self,
		cl: I,
		weight: Option<Coeff>,
	) -> Result {
		let clauses = self.cnf.clauses();
		self.cnf.add_clause(cl)?;
		if self.cnf.clauses() > clauses {
			self.weights.push(weight);
		}
		Ok(())
	}

	pub fn iter(&self) -> impl Iterator<Item = (&[Lit], &Option<Coeff>)> {
		self.cnf.iter().zip(self.weights.iter())
	}
}

impl ClauseDatabase for Wcnf {
	fn new_var(&mut self) -> Var {
		self.cnf.new_var()
	}
	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> Result {
		self.add_weighted_clause(cl, None)
	}
}

impl NextVarRange for Wcnf {
	fn next_var_range(&mut self, size: usize) -> Option<VarRange> {
		self.cnf.next_var_range(size)
	}
}

impl Cnf {
	pub fn iter(&self) -> CnfIterator<'_> {
		CnfIterator {
			lits: &self.lits,
			size: self.size.iter(),
			index: 0,
		}
	}
}
pub struct CnfIterator<'a> {
	lits: &'a Vec<Lit>,
	size: std::slice::Iter<'a, usize>,
	index: usize,
}
impl<'a> Iterator for CnfIterator<'a> {
	type Item = &'a [Lit];

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
	fn count(self) -> usize {
		self.size.count()
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZeroI32;

	use crate::Lit;

	impl From<i32> for Lit {
		fn from(value: i32) -> Self {
			Lit(NonZeroI32::new(value).expect("cannot create literal with value zero"))
		}
	}
}
