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
	cmp::Eq,
	error::Error,
	fmt::{self, Display},
	fs::File,
	hash::Hash,
	io::{self, BufRead, BufReader, Write},
	ops::Neg,
	path::Path,
	str::FromStr,
};

use itertools::{Itertools, Position};
use num::{
	traits::{NumAssignOps, NumOps},
	Integer, One, PrimInt, Signed, Zero,
};

mod cardinality;
mod cardinality_one;
pub(crate) mod helpers;
pub(crate) mod int;
mod linear;
pub mod solvers;
mod sorted;
pub mod trace;

pub use cardinality::Cardinality;
pub use cardinality_one::{CardinalityOne, LadderEncoder, PairwiseEncoder};
pub use linear::{
	AdderEncoder, BddEncoder, Comparator, LinExp, LinVariant, Linear, LinearAggregator,
	LinearConstraint, LinearEncoder, PosCoeff, SwcEncoder, TotalizerEncoder,
};

/// Literal is the super-trait for types that can be used to represent boolean
/// literals in this library.
///
/// Literals need to implement the following trait to be used as literals:
///
///  - [`std::clone::Clone`] to allow creating a new copy of the literal to
///    create clauses.
///
///  - [`std::cmp::Eq`] and [`std::hash::Hash`] to allow PB constraints to be
///    simplified
pub trait Literal: fmt::Debug + Clone + Eq + Hash {
	/// Returns the negation of the literal in its current form
	fn negate(&self) -> Self;
	/// Returns `true` when the literal a negated boolean variable.
	fn is_negated(&self) -> bool;
	/// Returns a non-negated version of the literal
	fn var(&self) -> Self {
		if self.is_negated() {
			self.negate()
		} else {
			self.clone()
		}
	}
}
impl<T: Signed + fmt::Debug + Clone + Eq + Hash + Neg<Output = Self> + LitMarker> Literal for T {
	fn is_negated(&self) -> bool {
		self.is_negative()
	}
	fn negate(&self) -> Self {
		-(self.clone())
	}
	fn var(&self) -> Self {
		self.abs()
	}
}
pub(crate) trait LitMarker {}
impl LitMarker for i8 {}
impl LitMarker for i16 {}
impl LitMarker for i32 {}
impl LitMarker for i64 {}
impl LitMarker for i128 {}

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

/// Encoder is the central trait implemented for all the encoding algorithms
pub trait Encoder<DB: ClauseDatabase, Constraint> {
	fn encode(&mut self, db: &mut DB, con: &Constraint) -> Result;
}

/// Checker is a trait implemented by types that represent constraints. The
/// [`Checker::check`] methods checks whether an assignment (often referred to
/// as a model) satisfies the constraint.
pub trait Checker {
	type Lit: Literal;

	/// Check whether the constraint represented by the object is violated.
	///
	/// - The method returns [`Result::Ok`] when the assignment satisfies
	///   the constraint,
	/// - it returns [`Unsatisfiable`] when the assignment violates the
	///   constraint,
	/// - and it return [`Incomplete`] when not all the literals used in the
	///   constraint have been assigned.
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>>;

	/// Returns assignment of `lit` in `solution`
	fn assign<'a>(lit: &'a Self::Lit, solution: &'a [Self::Lit]) -> &'a Self::Lit {
		solution.iter().find(|x| x.var() == lit.var()).unwrap_or_else(|| panic!("Could not find lit {lit:?} in solution {solution:?}; perhaps this variable did not occur in any clause"))
	}
}

/// Incomplete is a error type returned by a [`Checker`] type when the
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
pub struct Incomplete<Lit: Literal> {
	missing: Box<[Lit]>,
}
impl<Lit: Literal> Error for Incomplete<Lit> {}
impl<Lit: Literal> fmt::Display for Incomplete<Lit> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self.missing.len() {
			0 => write!(f, "Unknown literal is unasssigned"),
			1 => write!(f, "Literal {:?} is unasssigned", self.missing[0]),
			_ => {
				write!(f, "Literals")?;
				for pos in self.missing.iter().with_position() {
					match pos {
						Position::First(lit) => write!(f, " {:?}", lit)?,
						Position::Middle(lit) => write!(f, ", {:?}", lit)?,
						Position::Last(lit) => write!(f, ", and {:?}", lit)?,
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
pub enum CheckError<Lit: Literal> {
	Unsatisfiable(Unsatisfiable),
	Incomplete(Incomplete<Lit>),
}
impl<Lit: Literal> Error for CheckError<Lit> {}
impl<Lit: Literal> fmt::Display for CheckError<Lit> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			CheckError::Unsatisfiable(err) => err.fmt(f),
			CheckError::Incomplete(err) => err.fmt(f),
		}
	}
}

/// Coefficient in PB constraints are represented by types that implement the
/// `Coefficient` constraint.
pub trait Coefficient:
	Signed + Integer + PrimInt + NumAssignOps + NumOps + Hash + Default + fmt::Debug + fmt::Display
{
}
impl<
		T: Signed
			+ PrimInt
			+ Integer
			+ NumAssignOps
			+ NumOps
			+ Hash
			+ Default
			+ fmt::Debug
			+ fmt::Display,
	> Coefficient for T
{
}

/// IntEncoding is a enumerated type use to represent Boolean encodings of
/// integer variables within this library
pub enum IntEncoding<'a, Lit: Literal, C: Coefficient> {
	/// The Direct variant represents a integer variable encoded using domain
	/// or direct encoding of an integer variable. Each given Boolean literal
	/// represents whether the integer takes the associated value (i.e., X =
	/// (first+i) ↔ vals\[i\]).
	Direct { first: C, vals: &'a [Lit] },
	/// The Order variant represents a integer variable using an order
	/// encoding. Each given Boolean literal represents whether the integer
	/// is bigger than the associated value(i.e., X > (first+i) ↔ vals\[i\]).
	Order { first: C, vals: &'a [Lit] },
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
	/// Type used to represent a Boolean literal in the constraint input and
	/// generated clauses.
	type Lit: Literal;
	/// Method to be used to receive a new Boolean variable that can be used in
	/// the encoding of a constraint.
	fn new_var(&mut self) -> Self::Lit;

	/// Add a clause to the `ClauseDatabase`. The sink is allowed to return
	/// [`Unsatisfiable`] when the collection of clauses has been *proven* to
	/// be unsatisfiable. This is used as a signal to the encoder that any
	/// subsequent encoding effort can be abandoned.
	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result;
}

// TODO: Add usage and think about interface
pub struct ConditionalDatabase<'a, DB: ClauseDatabase> {
	db: &'a mut DB,
	conditions: &'a [DB::Lit],
}
impl<'a, DB: ClauseDatabase> ConditionalDatabase<'a, DB> {
	pub fn new(db: &'a mut DB, conditions: &'a [DB::Lit]) -> Self {
		Self { db, conditions }
	}
}
impl<'a, DB: ClauseDatabase> ClauseDatabase for ConditionalDatabase<'a, DB> {
	type Lit = DB::Lit;
	fn new_var(&mut self) -> Self::Lit {
		self.db.new_var()
	}
	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
		self.db.add_clause(&Vec::from_iter(
			self.conditions.iter().chain(cl.iter()).cloned(),
		))
	}
}

/// A representation for Boolean formulas in conjunctive normal form.
///
/// It can be used to create formulas manually, to store the results from
/// encoders, read formulas from a file, and write them to a file
#[derive(Clone, Debug)]
pub struct Cnf<Lit: Literal + Zero + One = i32> {
	/// The last variable created by [`new_var`]
	last_var: Lit,
	/// The literals from *all* clauses
	lits: Vec<Lit>,
	/// The size *for each* clause
	size: Vec<usize>,
}

/// A representation for a weighted CNF formula
///
/// Same as CNF, but every clause has an optional weight. Otherwise, it is a hard clause.
#[derive(Clone, Debug, Default)]
pub struct Wcnf<Lit: Literal + Zero + One = i32, C: Coefficient = i32> {
	/// The CNF formula
	cnf: Cnf<Lit>,
	/// The weight for every clause
	weights: Vec<Option<C>>,
	// TODO this can be optimised, for example by having all weighted clauses at the start/end
}

// TODO not sure how to handle converting num_var for vars()
impl<Lit: Literal + Zero + One + Display> Cnf<Lit> {
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

	pub fn variables(&self) -> Lit {
		self.last_var.clone()
	}

	pub fn clauses(&self) -> usize {
		self.size.len()
	}

	pub fn literals(&self) -> usize {
		self.size.iter().sum()
	}
}

impl<Lit: Literal + Zero + One + Display, C: Coefficient> Display for Wcnf<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let num_var = &self.cnf.last_var;
		let num_clauses = self.cnf.size.len();
		let top = *self
			.weights
			.iter()
			.flatten()
			.max()
			.expect("No soft clauses in Wcnf formula")
			+ C::one();
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

impl<Lit: Literal + Zero + One + Display, C: Coefficient> Wcnf<Lit, C> {
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

	pub fn variables(&self) -> Lit {
		self.cnf.variables()
	}

	pub fn clauses(&self) -> usize {
		self.cnf.clauses()
	}

	pub fn literals(&self) -> usize {
		self.cnf.literals()
	}
}

impl<Lit: Literal + Zero + One + Display> Display for Cnf<Lit> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let num_var = &self.last_var;
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

impl<Lit: Literal + Zero + One + FromStr> Cnf<Lit> {
	/// Read a CNF formula from a file formatted in the DIMACS CNF format
	pub fn from_file(path: &Path) -> Result<Self, io::Error> {
		let file = File::open(path)?;
		let mut had_header = false;
		let mut cnf = Cnf::<Lit>::default();
		let mut cl: Vec<Lit> = Vec::new();
		for line in BufReader::new(file).lines() {
			match line {
				Ok(line) if line.is_empty() || line.starts_with('c') => (),
				Ok(line) if had_header => {
					for seg in line.split(' ') {
						if let Ok(l) = seg.parse::<Lit>() {
							if l == Lit::zero() {
								cnf.add_clause(&cl)
									.expect("CNF::add_clause does not return Unsatisfiable");
								cl.clear();
							} else {
								cl.push(l);
							}
						}
					}
				}
				// parse header, expected format: "p cnf {num_var} {num_clauses}"
				Ok(line) => {
					let vec: Vec<&str> = line.split_whitespace().collect();
					// check "p" and "cnf" keyword
					if vec.len() != 4 || vec[0..2] != ["p", "cnf"] {
						return Err(io::Error::new(
							io::ErrorKind::InvalidInput,
							"expected DIMACS CNF header formatted \"p cnf {variables} {clauses}\"",
						));
					}
					// parse number of variables
					cnf.last_var = vec[2].parse().map_err(|_| {
						io::Error::new(
							io::ErrorKind::InvalidInput,
							"unable to parse number of variables",
						)
					})?;
					// parse number of clauses
					let num_clauses: usize = vec[3].parse().map_err(|_| {
						io::Error::new(
							io::ErrorKind::InvalidInput,
							"unable to parse number of clauses",
						)
					})?;
					cnf.lits.reserve(num_clauses);
					cnf.size.reserve(num_clauses);
					// parsing header complete
					had_header = true;
				}
				Err(e) => return Err(e),
			}
		}
		Ok(cnf)
	}
}

impl<Lit: Literal + Zero + One> Default for Cnf<Lit> {
	fn default() -> Self {
		Self {
			last_var: Lit::zero(),
			lits: Vec::new(),
			size: Vec::new(),
		}
	}
}
impl<Lit: Literal + Zero + One> ClauseDatabase for Cnf<Lit> {
	type Lit = Lit;
	fn new_var(&mut self) -> Self::Lit {
		self.last_var = self.last_var.clone() + Lit::one();
		self.last_var.clone()
	}

	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
		self.lits.reserve(cl.len());
		self.lits.extend_from_slice(cl);
		self.size.push(cl.len());
		Ok(())
	}
}

impl<Lit: Literal + Zero + One, C: Coefficient> Wcnf<Lit, C> {
	pub fn add_weighted_clause(&mut self, cl: &[Lit], weight: Option<C>) -> Result {
		self.cnf.add_clause(cl)?;
		self.weights.push(weight);
		Ok(())
	}
}

impl<Lit: Literal + Zero + One> ClauseDatabase for Wcnf<Lit> {
	type Lit = Lit;
	fn new_var(&mut self) -> Self::Lit {
		self.cnf.new_var()
	}

	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
		self.cnf.add_clause(cl)
	}
}

impl<Lit: Literal + Zero + One> Cnf<Lit> {
	pub fn iter(&self) -> CnfIterator<Lit> {
		CnfIterator {
			lits: &self.lits,
			size: self.size.iter(),
			index: 0,
		}
	}
}
pub struct CnfIterator<'a, Lit: Literal + Zero + One> {
	lits: &'a Vec<Lit>,
	size: std::slice::Iter<'a, usize>,
	index: usize,
}
impl<'a, Lit: Literal + Zero + One> Iterator for CnfIterator<'a, Lit> {
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
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;

	#[test]
	fn test_int_literals() {
		assert!(is_lit(1i8));
		assert!(is_lit(1i16));
		assert!(is_lit(1i32));
		assert!(is_lit(1i64));
		assert!(is_lit(1i128));
	}
	fn is_lit<T: Literal>(_: T) -> bool {
		true
	}

	#[test]
	fn test_coefficients() {
		assert!(is_coeff(1i8));
		assert!(is_coeff(1i16));
		assert!(is_coeff(1i32));
		assert!(is_coeff(1i64));
		assert!(is_coeff(1i128));
	}
	fn is_coeff<T: Coefficient>(_: T) -> bool {
		true
	}

	#[test]
	fn test_positive_coefficients() {
		assert!(is_poscoeff(1i8));
		assert!(is_poscoeff(1i16));
		assert!(is_poscoeff(1i32));
		assert!(is_poscoeff(1i64));
		assert!(is_poscoeff(1i128));
	}
	fn is_poscoeff<T: Coefficient>(c: T) -> bool {
		let _ = PosCoeff::from(c);
		true
	}
}
