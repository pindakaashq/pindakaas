#![allow(
	unused_qualifications,
	reason = "pyo3 macro will generate unused qualified types"
)]

use pyo3::prelude::*;

#[pymodule]
pub(crate) mod pindakaas {

	#[pymodule_export]
	use crate::PyCnf;
	#[pymodule_export]
	use crate::PyWcnf;

	/// Return ``pindakaas`` version
	#[pyfunction]
	fn version() -> String {
		env!("CARGO_PKG_VERSION").to_owned()
	}

	use std::fmt::Display;

	use itertools::Itertools;
	// use pindakaas_derive::PythonClauseDatabase;
	use pyo3::exceptions::PyException;

	use super::*;

	type Clause = Vec<Lit>;

	/// :meta private:
	#[pyclass(subclass)]
	pub(crate) struct ClauseDatabase();

	/// :meta private:
	#[pymethods]
	impl ClauseDatabase {
		#[new]
		pub(crate) fn new() -> Self {
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
	pub(crate) struct VarRange(pub(crate) crate::VarRange);

	/// A Boolean literal
	#[pyclass]
	#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
	pub(crate) struct Lit(pub(crate) crate::Lit);

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
	pub(crate) struct Unsatisfiable;

	pub(crate) type Result<T = (), E = Unsatisfiable> = std::result::Result<T, E>;

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

	impl From<crate::Unsatisfiable> for Unsatisfiable {
		fn from(_: crate::Unsatisfiable) -> Self {
			Self
		}
	}

	impl From<Unsatisfiable> for PyErr {
		fn from(_: Unsatisfiable) -> PyErr {
			PyErr::new::<Unsatisfiable, _>(())
		}
	}

	impl From<Lit> for crate::Lit {
		fn from(val: Lit) -> Self {
			val.0
		}
	}

	// TODO [?] How to avoid this duplication?
	#[pyclass(eq, eq_int)]
	#[derive(Clone, PartialEq, Default)]
	pub(crate) enum Comparator {
		LessEq,
		Equal,
		#[default]
		GreaterEq,
	}

	impl From<Comparator> for crate::bool_linear::Comparator {
		fn from(val: Comparator) -> Self {
			match val {
				Comparator::LessEq => crate::bool_linear::Comparator::LessEq,
				Comparator::Equal => crate::bool_linear::Comparator::Equal,
				Comparator::GreaterEq => crate::bool_linear::Comparator::GreaterEq,
			}
		}
	}

	// TODO [?] why not export Coeff from lib?
	pub(crate) type Coeff = i64;

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
	impl PyCnf {
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
		// 	Ok(Self(crate::Cnf::from_file(&path)?))
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

	#[pymodule]
	mod solvers {
		#[cfg(feature = "cadical")]
		#[pymodule_export]
		use crate::solver::cadical::PyCadical;
		#[cfg(feature = "intel-sat")]
		#[pymodule_export]
		use crate::solver::intel_sat::PyIntelSat;
		#[cfg(feature = "kissat")]
		#[pymodule_export]
		use crate::solver::kissat::PyKissat;
	}
}

/*
/// All solvers inherit functionality from Cnf
#[pymodule]
mod solvers {
	// use pindakaas_derive::add_time_limit_field;

	use super::*;

	// #[pyclass(unsendable)]
	// #[derive(Default)]
	// // #[python_clause_database(solver = true, assumptions = true)]
	// // #[add_time_limit_field]
	// struct Cadical(crate::solver::cadical::Cadical);
	//
	// #[pyclass(unsendable)]
	// #[derive(Default)]
	// // #[python_clause_database(solver = true, time_limit = false)]
	// struct Kissat(crate::solver::kissat::Kissat);
	//
	// #[pyclass(unsendable)]
	// #[derive(Default)]
	// // #[python_clause_database(solver = true, assumptions = true)]
	// struct IntelSat(crate::solver::intel_sat::IntelSat);
}
	*/

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
