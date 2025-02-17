#![allow(
	unused_qualifications,
	reason = "pyo3 macro will generate unused qualified types"
)]

use itertools::Itertools;
use std::{fmt::Display, ops::DerefMut, path::PathBuf};

use ::pindakaas as base;
use base::{
	bool_linear::{BoolLinExp, BoolLinear, LinearEncoder},
	ClauseDatabaseTools, Encoder,
};
use pyo3::{exceptions::PyException, prelude::*};

type Clause = Vec<Lit>;

#[pyclass]
struct Cnf(base::Cnf);

#[pyclass]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(base::Lit);

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
#[derive(Clone, PartialEq)]
enum Comparator {
	LessEq,
	Equal,
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

///
/// Encode a linear constraint over Boolean literals
/// The default arguments encode a clause: all coefficients are one, comparator is >=, and k = 1.
/// Currently, the encoding is fixed as `adder` for PB and Cardinality constraints, and `PairWise` for AMOs/ALOs
#[pyfunction(signature=(db, literals, /, coefficients = None, comparator = Comparator::GreaterEq, k = 1))]
fn encode(
	mut db: PyRefMut<'_, Cnf>,
	literals: Vec<Lit>,
	coefficients: Option<Vec<Coeff>>,
	comparator: Comparator,
	k: Coeff,
) -> Result {
	let pref = db.deref_mut();
	let db = &mut pref.0;
	let coefficients = coefficients.unwrap_or(literals.iter().map(|_| 1).collect());
	assert_eq!(
		coefficients.len(),
		literals.len(),
		"Literals and coefficients should have the same length"
	);
	let enc: LinearEncoder = LinearEncoder::default();
	Ok(enc.encode(
		db,
		&BoolLinear::new(
			BoolLinExp::from_slices(
				&coefficients,
				&literals.into_iter().map(|l| l.0).collect_vec(),
			),
			comparator.into(),
			k,
		),
	)?)
}

#[pymodule]
fn pindakaas(m: &Bound<'_, PyModule>) -> PyResult<()> {
	m.add_class::<Cnf>()?;
	m.add_class::<Unsatisfiable>()?;
	m.add_class::<Comparator>()?;
	m.add_function(wrap_pyfunction!(encode, m)?)?;
	Ok(())
}

// #[pymethods]
// impl ClauseIter {
// 	fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
// 		slf
// 	}
// 	fn __next__(mut slf: PyRefMut<'_, Self>) -> Option<Clause> {
// 		slf.inner.next()
// 	}
// }

#[pyclass]
struct ClauseIter {
	inner: std::vec::IntoIter<Clause>,
}

#[pymethods]
impl ClauseIter {
	fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
		slf
	}

	fn __next__(mut slf: PyRefMut<'_, Self>) -> Option<Clause> {
		slf.inner.next()
	}
}

#[pymethods]
impl Cnf {
	//  fn __iter__(&self) -> PyResult<Py<ClauseIter>> {
	//      Py::new(self.py(), ClauseIter {
	// inner: Vec::from_iter(self.0.iter().map(Vec::from)).into_iter()
	//          // inner: slf.0.iter().cloned().collect_vec().into_iter(),
	//      })
	//  }

	fn __iter__(&self) -> ClauseIter {
		// FIXME: It would be great if this could be made lazily instead of copying everything when creating the iterator
		ClauseIter {
			inner: Vec::from_iter(
				self.0
					.iter()
					.map(|clause| clause.iter().map(|l| Lit(*l)).collect_vec()),
			)
			.into_iter(),
		}
	}

	fn __str__(&self) -> String {
		format!("{}", self.0)
	}

	fn add_clause(&mut self, cl: Vec<Lit>) -> Result {
		self.0
			.add_clause(cl.into_iter().map(|l| l.0))
			.map_err(|_| Unsatisfiable)
	}

	fn new_var(&mut self) -> Lit {
		Lit(self.0.new_var().into())
	}

	#[staticmethod]
	fn from_file(path: PathBuf) -> Result<Self, std::io::Error> {
		Ok(Self(base::Cnf::from_file(&path)?))
	}
	#[new]
	fn new() -> Self {
		Self(base::Cnf::default())
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
	pub fn is_negated(&self) -> bool {
		self.0.is_negated()
	}

	pub fn __invert__(&self) -> Self {
		Self(!self.0)
	}

	/// Returns the underlying variable of the literal, whether negated or not.
	/// TODO not sure whether to also add this, especially if it's not in the rust interface
	pub fn __abs__(&self) -> Self {
		self.var()
	}

	/// Returns the underlying variable of the literal, whether negated or not.
	pub fn var(&self) -> Self {
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
				c_str!("example"),
			)
			.unwrap();
		});
	}
}
