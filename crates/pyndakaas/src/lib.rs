#![allow(
	unused_qualifications,
	reason = "pyo3 macro will generate unused qualified types"
)]

use itertools::Itertools;
use std::{fmt::Display, num::NonZeroI32, path::PathBuf};

use ::pindakaas::{self as base, solver::Solver, ClauseDatabaseTools, MapSol, Valuation};
use base::{
	bool_linear::{BoolLinExp, BoolLinear, LinearEncoder},
	Encoder,
};
use pyo3::{exceptions::PyException, prelude::*};

type Clause = Vec<Lit>;

#[pyclass]
struct Cnf(base::Cnf);

#[pyclass]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Lit(base::Lit);

#[pyclass]
#[derive(Clone)]
struct VarRange(base::VarRange);

#[pyclass]
struct VarRangeIter(std::vec::IntoIter<Lit>);

#[pymethods]
impl VarRangeIter {
	fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
		slf
	}

	fn __next__(mut slf: PyRefMut<'_, Self>) -> Option<Lit> {
		slf.0.next()
	}
}

#[pymethods]
impl VarRange {
	// TODO check lifetime
	fn __iter__(&mut self) -> VarRangeIter {
		VarRangeIter(self.0.iter_lits().map(Lit).collect_vec().into_iter())
		// VarRangeIter(self.0.iter_lits().map(|l| Lit(l)))
	}
}

#[pyclass(extends = PyException)]
struct Unsatisfiable;

type Result<T = (), E = Unsatisfiable> = std::result::Result<T, E>;

#[pymethods]
impl Unsatisfiable {
	#[new]
	fn new() -> Self {
		Self
	}
	fn __str__(&self) -> String {
		"Unsatisfiable".to_owned()
	}
}

impl From<base::Unsatisfiable> for Unsatisfiable {
	fn from(_: base::Unsatisfiable) -> Self {
		Self
	}
}

impl From<Unsatisfiable> for PyErr {
	fn from(_: Unsatisfiable) -> PyErr {
		PyErr::new::<Unsatisfiable, _>(())
	}
}

impl From<Lit> for base::Lit {
	fn from(val: Lit) -> Self {
		val.0
	}
}

// #[pyclass]
// #[derive(Clone)]
// struct Comparator(base::bool_linear::Comparator);

#[pyclass(eq, eq_int)]
#[derive(Clone, PartialEq, Default)]
enum Comparator {
	LessEq,
	Equal,
	#[default]
	GreaterEq,
}

// TODO way to avoid duplication?
impl From<Comparator> for base::bool_linear::Comparator {
	fn from(val: Comparator) -> Self {
		match val {
			Comparator::LessEq => base::bool_linear::Comparator::LessEq,
			Comparator::Equal => base::bool_linear::Comparator::Equal,
			Comparator::GreaterEq => base::bool_linear::Comparator::GreaterEq,
		}
	}
}

// TODO why not excport Coeff from lib?
type Coeff = i64;

#[pymodule]
fn pindakaas(m: &Bound<'_, PyModule>) -> PyResult<()> {
	m.add_class::<Cnf>()?;
	m.add_class::<CadicalSolver>()?;
	m.add_class::<Unsatisfiable>()?;
	m.add_class::<Comparator>()?;
	Ok(())
}

#[pyclass]
struct ClauseIter(std::vec::IntoIter<Clause>);

#[pymethods]
impl ClauseIter {
	fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
		slf
	}

	fn __next__(mut slf: PyRefMut<'_, Self>) -> Option<Clause> {
		slf.0.next()
	}
}

#[pymethods]
impl Cnf {
	#[new]
	#[pyo3(signature = (vars=None))]
	fn new(vars: Option<usize>) -> Self {
		Self(base::Cnf::new(vars))
	}

	///
	/// Encode a linear constraint over Boolean literals
	/// The default arguments encode a clause: all coefficients are one, comparator is >=, and k = 1.
	/// Currently, the encoding is fixed as `adder` for PB and Cardinality constraints, and `PairWise` for AMOs/ALOs
	#[pyo3(signature=(literals, /, coefficients = None, comparator = Some(Comparator::GreaterEq), k = Some(1)))]
	fn add_linear(
		&mut self,
		literals: Vec<Lit>,
		coefficients: Option<Vec<Coeff>>,
		// TODO I'm not sure if adding Option is the best way to allow None to return default
		comparator: Option<Comparator>,
		k: Option<Coeff>,
	) -> Result {
		let coefficients = coefficients.unwrap_or(literals.iter().map(|_| 1).collect());
		assert_eq!(
			coefficients.len(),
			literals.len(),
			"Literals and coefficients should have the same length"
		);
		let enc: LinearEncoder = LinearEncoder::default();
		Ok(enc.encode(
			&mut self.0,
			&BoolLinear::new(
				BoolLinExp::from_slices(
					&coefficients,
					&literals.into_iter().map(|l| l.0).collect_vec(),
				),
				comparator.unwrap_or_default().into(),
				k.unwrap_or(1),
			),
		)?)
	}

	fn __iter__(&self) -> ClauseIter {
		// FIXME: It would be great if this could be made lazily instead of copying everything when creating the iterator
		ClauseIter(
			Vec::from_iter(
				self.0
					.iter()
					.map(|clause| clause.iter().map(|l| Lit(*l)).collect_vec()),
			)
			.into_iter(),
		)
	}

	fn __str__(&self) -> String {
		format!("{}", self.0)
	}

	fn add_clause(&mut self, cl: Vec<Lit>) -> Result {
		self.0
			.add_clause(cl.into_iter().map(|l| l.0))
			.map_err(|_| Unsatisfiable)
	}

	fn add_variable(&mut self) -> Lit {
		Lit(self.0.new_var().into())
	}

	fn add_variables(&mut self, len: usize) -> VarRange {
		VarRange(base::ClauseDatabase::new_var_range(&mut self.0, len))
	}

	#[staticmethod]
	fn from_file(path: PathBuf) -> Result<Self, std::io::Error> {
		Ok(Self(base::Cnf::from_file(&path)?))
	}
}

#[pymethods]
impl Lit {
	// TODO probably don't add this one
	// #[new]
	// fn new(value: NonZeroI32) -> Self {
	// 	Self(base::Lit::from_raw(value))
	// }

	/// Returns whether the literal is a negation of the underlying variable.
	fn is_negated(&self) -> bool {
		self.0.is_negated()
	}

	fn __invert__(&self) -> Self {
		Self(!self.0)
	}

	/// Returns the underlying variable of the literal, whether negated or not.
	/// TODO not sure whether to also add this, especially if it's not in the rust interface
	fn __abs__(&self) -> Self {
		self.var()
	}

	/// Returns the underlying variable of the literal, whether negated or not.
	fn var(&self) -> Self {
		Self(self.0.var().into())
	}

	fn __str__(&self) -> String {
		format!("{}", self.0)
	}

	// TODO Bit* operations
}

impl Display for Lit {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		self.0.fmt(f)
	}
}

// SOLVING
//

#[pyclass(unsendable)]
#[derive(Default)]
struct CadicalSolver {
	solver: base::solver::cadical::Cadical,
	vars: Option<base::Var>, // TODO currently hard to remove using MapSol
	solution: Option<base::MapSol>,
}

// solution: Solution,
// solve_result: base::solver::SolveResult<
// 	base::solver::cadical::CadicalSol<'a>,
// 	base::solver::cadical::CadicalFailed<'a>,
// >,

#[pyclass]
struct SolveResult(base::solver::SolveResult<MapSol>);

#[pymethods]
impl SolveResult {
	// #[new]
	// fn new() -> Self {
	// 	Self(base::solver::SolveResult::default())
	// }

	fn __str__(&self) -> String {
		match &self.0 {
			::pindakaas::solver::SolveResult::Satisfied(sol) => format!("{}", sol),
			::pindakaas::solver::SolveResult::Unsatisfiable(_) => {
				format!("{}", base::Unsatisfiable)
			}
			::pindakaas::solver::SolveResult::Unknown => "UNKNOWN".to_owned(),
		}
	}
}

// #[pyclass]
// struct Solution(base::solver::cadical::CadicalSol); // TODO can't because of lifetime
// struct Solution(M);

#[pymethods]
impl CadicalSolver {
	#[new]
	fn new() -> Self {
		Self::default()
	}

	/// Number of variables
	fn variables(&self) -> Option<NonZeroI32> {
		self.vars.map(|v| v.into())
	}

	// TODO: since trait exposure doesn't quite work how we want, and because it is slow, and
	// because ABC's are not supported by pyo3, we have code duplication. Perhaps adding
	// a derive proc macro would be the answer.
	fn add_clause(&mut self, cl: Vec<Lit>) -> Result {
		self.solver
			.add_clause(cl.into_iter().map(|l| l.0))
			.map_err(|_| Unsatisfiable)
	}

	fn add_variable(&mut self) -> Lit {
		self.vars = Some(self.solver.new_var());
		Lit(self.vars.unwrap().into())
	}

	fn solve(&mut self) -> Option<bool> {
		match self.solver.solve() {
			::pindakaas::solver::SolveResult::Satisfied(sol) => {
				self.solution = Some(
					self.vars
						.map(|v| MapSol::new(base::VarRange::until(v), &sol))
						.unwrap_or_default(),
				);
				Some(true)
			}
			::pindakaas::solver::SolveResult::Unsatisfiable(_) => Some(false),
			::pindakaas::solver::SolveResult::Unknown => None,
		}
	}

	fn value(&self, lit: Lit) -> Option<bool> {
		self.solution.as_ref().map(|sol| sol.value(lit.into()))
	}
}

#[cfg(test)]
mod tests {

	use std::ffi::CString;

	use super::*;
	use pyo3::{ffi::c_str, Python};

	#[pyclass]
	struct LoggingStdout;
	#[pymethods]
	impl LoggingStdout {
		fn write(&self, data: &str) {
			print!("{}", data);
		}
	}

	#[test]
	fn test_interface() {
		pyo3::append_to_inittab!(pindakaas);
		pyo3::prepare_freethreaded_python();
		Python::with_gil(|py| {
			let sys = py.import("sys").unwrap();
			_ = sys.setattr("stdout", LoggingStdout.into_pyobject(py).unwrap());
			_ = PyModule::from_code(
				py,
				CString::new(include_str!("../example.py"))
					.unwrap()
					.as_c_str(),
				c_str!("example.py"),
				c_str!("__main__"),
			)
			.unwrap_or_else(|e| panic!("{e}"));
		});
	}
}
