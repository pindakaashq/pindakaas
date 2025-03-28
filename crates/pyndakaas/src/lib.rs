#![allow(
	unused_qualifications,
	reason = "pyo3 macro will generate unused qualified types"
)]

// TODO features -> extra installs via pip (e.g. pip install pindakaas[cadical,kissat])
// TODO better type checking and errors (e.g. adding non-list to add_clause currently gives `TypeError: argument 'clause': 'Lit' object cannot be converted to 'Sequence'`)
use itertools::Itertools;
use pindakaas_derive::{PythonClauseDatabase, PythonClauseDatabaseTools, PythonSolver};
use std::fmt::Display;

use ::pindakaas::{self as base, solver::Solver, MapSol, Valuation};
use base::{
	bool_linear::{BoolLinExp, BoolLinear, LinearEncoder},
	Encoder,
};
use pyo3::{exceptions::PyException, prelude::*};

type Clause = Vec<Lit>;

#[pyclass(subclass)]
struct ClauseDatabase();

#[pymethods]
impl ClauseDatabase {
	#[new]
	fn new() -> Self {
		Self()
	}

	#[allow(unused_variables, reason = "Pseudo-abstract method")]
	fn add_clause_from_slice(&mut self, clause: Vec<Lit>) -> Result {
		unimplemented!("ABSTRACT")
	}

	#[allow(unused_variables, reason = "Pseudo-abstract method")]
	fn new_var_range(&mut self, len: usize) -> VarRange {
		unimplemented!("ABSTRACT")
	}
}

#[pyclass]
#[derive(Clone)]
struct VarRange(base::VarRange);

#[pyclass]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Lit(base::Lit);

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
	fn __iter__(&mut self) -> VarRangeIter {
		VarRangeIter(self.0.iter_lits().map(Lit).collect_vec().into_iter())
		// TODO Non-collect version WIP, might require unsupported lifetimes: VarRangeIter(self.0.iter_lits().map(|l| Lit(l)))
	}
}

// TODO use create_exception! ?
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

// TODO [?] How to avoid this duplication?
#[pyclass(eq, eq_int)]
#[derive(Clone, PartialEq, Default)]
enum Comparator {
	LessEq,
	Equal,
	#[default]
	GreaterEq,
}

impl From<Comparator> for base::bool_linear::Comparator {
	fn from(val: Comparator) -> Self {
		match val {
			Comparator::LessEq => base::bool_linear::Comparator::LessEq,
			Comparator::Equal => base::bool_linear::Comparator::Equal,
			Comparator::GreaterEq => base::bool_linear::Comparator::GreaterEq,
		}
	}
}

// TODO [?] why not export Coeff from lib?
type Coeff = i64;

#[pymodule]
fn pindakaas(m: &Bound<'_, PyModule>) -> PyResult<()> {
	m.add_class::<Cnf>()?;
	m.add_class::<Wcnf>()?;
	m.add_class::<Cadical>()?;
	m.add_class::<Kissat>()?;
	m.add_class::<Unsatisfiable>()?;
	m.add_class::<Comparator>()?;
	Ok(())
}

#[pyclass(extends=ClauseDatabase)]
#[derive(PythonClauseDatabase, PythonClauseDatabaseTools)]
struct Cnf(base::Cnf);

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
	fn new() -> (Self, ClauseDatabase) {
		(Self(base::Cnf::default()), ClauseDatabase::new())
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

	// TODO [?] Shouldn't we make reading from_file part of ClauseDatabaseTools?
	// TODO [?] Doesn't compile, seems like a PyO3 bug
	// #[staticmethod]
	// fn from_file(path: PathBuf) -> std::result::Result<Cnf, std::io::Error> {
	// 	Ok(Self(base::Cnf::from_file(&path)?))
	// }
}

#[pyclass(extends=ClauseDatabase)]
#[derive(PythonClauseDatabase, PythonClauseDatabaseTools)]
struct Wcnf(base::Wcnf);

#[pymethods]
impl Wcnf {
	#[new]
	fn new() -> (Self, ClauseDatabase) {
		(Self(base::Wcnf::default()), ClauseDatabase::new())
	}
}

#[pymethods]
impl Lit {
	/// Returns whether the literal is a negation of the underlying variable.
	fn is_negated(&self) -> bool {
		self.0.is_negated()
	}

	fn __invert__(&self) -> Self {
		Self(!self.0)
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
#[derive(Default, PythonClauseDatabase, PythonClauseDatabaseTools, PythonSolver)]
// TODO can we derive PythonClauseDatabase by PythonSolver?
#[python_clause_database(db = solver)]
#[python_clause_database_tools(db = solver)]
#[python_solver(slv = solver)]
struct Cadical {
	solver: base::solver::cadical::Cadical,
	solution: Option<base::MapSol>,
}

#[pyclass(unsendable)]
#[derive(Default, PythonClauseDatabase, PythonClauseDatabaseTools, PythonSolver)]
#[python_clause_database(db = solver)]
#[python_clause_database_tools(db = solver)]
#[python_solver(slv = solver)]
struct Kissat {
	solver: base::solver::kissat::Kissat,
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
// 													// struct Solution(M);

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
