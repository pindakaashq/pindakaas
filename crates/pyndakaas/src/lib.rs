#![allow(
	unused_qualifications,
	reason = "pyo3 macro will generate unused qualified types"
)]

use std::{fmt::Display, ops::DerefMut, path::PathBuf};

use ::pindakaas as base;
use base::{
	bool_linear::{BoolLinExp, BoolLinear, Comparator, LinearEncoder},
	ClauseDatabaseTools, Encoder,
};
use pyo3::{exceptions::PyException, prelude::*};

type Clause = Vec<Lit>;

#[pyclass]
struct ClauseIter {
	inner: std::vec::IntoIter<Clause>,
}

#[pyclass(name = "Cnf")]
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

#[pyfunction]
fn adder_encode(mut db: PyRefMut<'_, Cnf>) -> Result {
	let pref = db.deref_mut();
	let db = &mut pref.0;
	let x = BoolLinExp::from_slices(
		&[1, 2, 3],
		&[
			db.new_var().into(),
			db.new_var().into(),
			db.new_var().into(),
		],
	);
	let con = BoolLinear::new(x, Comparator::Equal, 2);
	let enc: LinearEncoder = LinearEncoder::default();
	Ok(enc.encode(db, &con)?)
}

#[pymodule]
fn pindakaas(m: &Bound<'_, PyModule>) -> PyResult<()> {
	m.add_class::<Cnf>()?;
	m.add_class::<Unsatisfiable>()?;
	m.add_function(wrap_pyfunction!(adder_encode, m)?)?;
	Ok(())
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
	fn __iter__(&self) -> ClauseIter {
		// FIXME: It would be great if this could be made lazily instead of copying everything when creating the iterator
		// ClauseIter {
		// 	inner: Vec::from_iter(self.0.iter().map(Vec::from)).into_iter(),
		// }
		todo!()
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
		let code = c_str!(
			r#"
import pindakaas
cnf = pindakaas.Cnf()
a = cnf.new_var()
b = cnf.new_var()
c = cnf.new_var()
cnf.add_clause([~a,b])
cnf.add_clause([abs(~b),c])
print(f"A literal: {a}")
print(f"A negated literal: {~a}")
print(f"The variable of a negated literal: {abs(~a)} or {(~a).var()}")
print(f"{cnf}")
try:
    cnf.add_clause([])
except pindakaas.Unsatisfiable as e:
    print(f"Caught Unsatisfiable exception: {e} of type {type(e)}")
pindakaas.adder_encode(cnf)
print(f"Encode adder: {cnf}")
                "#
		);
		pyo3::append_to_inittab!(pindakaas);
		pyo3::prepare_freethreaded_python();
		Python::with_gil(|py| {
			let sys = py.import("sys").unwrap();
			sys.setattr("stdout", LoggingStdout.into_pyobject(py).unwrap())
				.unwrap();
			py.run(code, None, None).unwrap();
		});
	}
}
