#![allow(
	unused_qualifications,
	reason = "pyo3 macro will generate unused qualified types"
)]

use ::pindakaas::{self as base};
use ::pindakaas_derive::py_new_type;
use pyo3::prelude::*;

#[py_new_type]
struct Cnf(base::Cnf);

#[py_new_type]
struct Wcnf(base::Wcnf);

#[py_new_type(solver, assumptions, term_callback)]
struct Cadical(base::solver::cadical::Cadical);

#[py_new_type(solver)]
struct Kissat(base::solver::kissat::Kissat);

#[py_new_type(solver, assumptions, term_callback)]
struct IntelSat(base::solver::intel_sat::IntelSat);

// py_new_type!(base::solver::cadical::Cadical);
// py_new_type!(base::Wcnf);
// #[pyndakaas(solver)]
// py_new_type!(base::solver::cadical::Cadical);
// py_new_type!(base::solver::kissat::Kissat);
// py_new_type!(base::solver::intel_sat::IntelSat);

// #[pyclass(unsendable, extends = ClauseDatabase)]
// #[derive(#(#derives),*)]
// #[pyndakaas(tools)]
// struct #ident(#path);

//
// #[cfg(feature = "cadical")]
// #[cfg(feature = "kissat")]
// #[cfg(feature = "intel-sat")]

// use super::*;

// mod nt {
// 	use super::*;
// 	use ::pindakaas_derive::py_new_type;
// 	py_new_type!(Cnf);
// }

// #[pymodule_export]
// use Cnf;

// use base::PyCnf;
// #[pymodule_export]
// use base::PyWcnf;

/// Return ``pindakaas`` version
#[pyfunction]
fn version() -> String {
	env!("CARGO_PKG_VERSION").to_owned()
}

use std::fmt::Display;

use itertools::Itertools;
// use pindakaas_derive::PythonClauseDatabase;
use pyo3::exceptions::PyException;

type Clause = Vec<Lit>;

/// :meta private:
#[pyclass(subclass)]
struct ClauseDatabase();

/// :meta private:
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

/// A range of Boolean variables
#[pyclass]
#[derive(Clone)]
struct VarRange(base::VarRange);

/// A Boolean literal
#[pyclass]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Lit(base::Lit);

/// :meta private:
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
	fn __getitem__(&self, i: usize) -> Lit {
		Lit(self.0.index(i).into())
	}

	fn __iter__(&mut self) -> VarRangeIter {
		VarRangeIter(self.0.iter_lits().map(Lit).collect_vec().into_iter())
		// TODO Non-collect version WIP, might require unsupported lifetimes: VarRangeIter(self.0.iter_lits().map(|l| Lit(l)))
	}
}

/// Raised if Unsatisfiable is derived during encoding
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

#[pyclass]
/// :meta private:
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

// Using a mod pymodule { .. } runs into a bug where the new typed is not added to the python
// module (something about the order macro execution?)
#[pymodule]
fn pindakaas(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
	m.add_class::<Unsatisfiable>()?;
	m.add_class::<Comparator>()?;
	m.add_class::<ClauseDatabase>()?;
	m.add_class::<Cnf>()?;
	m.add_class::<Wcnf>()?;
	let solvers = PyModule::new(py, "solvers")?;
	solvers.add_class::<Cadical>()?;
	solvers.add_class::<Kissat>()?;
	solvers.add_class::<IntelSat>()?;
	m.add_submodule(&solvers)?;
	Ok(())
}

#[cfg(test)]
mod tests {

	use std::ffi::CString;

	use pyo3::{ffi::c_str, Python};

	use super::*;

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
			.unwrap_or_else(|e| {
				e.display(py);
				panic!();
			});
		});
	}
}
