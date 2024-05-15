use std::{fmt::Display, ops::DerefMut, path::PathBuf};

use base::{ClauseDatabase, Encoder, LinExp, LinearConstraint, LinearEncoder};
use pindakaas as base;
use pyo3::{exceptions::PyArithmeticError, prelude::*};

#[pyclass]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(base::Lit);
impl Lit {
	pub fn is_negated(&self) -> bool {
		self.0.is_negated()
	}
	pub fn var(&self) -> Self {
		Self(self.0.var().into()) // TODO
	}
}
impl Display for Lit {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		self.0.fmt(f)
	}
}

type Clause = Vec<Lit>;

#[pymodule]
#[pyo3(name = "pindakaas")]
fn module(_py: Python, m: &PyModule) -> PyResult<()> {
	m.add_class::<Cnf>()?;
	m.add_function(wrap_pyfunction!(adder_encode, m)?)?;
	Ok(())
}

#[pyfunction]
fn adder_encode(mut db: PyRefMut<'_, Cnf>) -> Result<(), PyErr> {
	let pref = db.deref_mut();
	let db = &mut pref.0;
	let x = LinExp::from_slices(
		&[1, 2, 3],
		&[
			db.new_var().into(),
			db.new_var().into(),
			db.new_var().into(),
		],
	);
	let con = LinearConstraint::new(x, base::Comparator::Equal, 2);
	let enc: LinearEncoder = LinearEncoder::default();
	enc.encode(db, &con)
		.map_err(|_e| PyArithmeticError::new_err("Unsatisfiable"))
}

#[pyclass(name = "CNF")]
struct Cnf(base::Cnf);

#[pymethods]
impl Cnf {
	#[new]
	fn new() -> Self {
		Self(base::Cnf::default())
	}
	#[staticmethod]
	fn from_file(path: PathBuf) -> Result<Self, std::io::Error> {
		Ok(Self(base::Cnf::from_file(&path)?))
	}

	fn __str__(&self) -> String {
		self.0.to_string()
	}

	fn __iter__(&self) -> ClauseIter {
		// FIXME: It would be great if this could be made lazily instead of copying everything when creating the iterator
		// ClauseIter {
		// 	inner: Vec::from_iter(self.0.iter().map(Vec::from)).into_iter(),
		// }
		todo!()
	}
}

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

#[cfg(test)]
mod tests {
	#[test]
	fn it_works() {
		let result = 2 + 2;
		assert_eq!(result, 4);
	}
}
