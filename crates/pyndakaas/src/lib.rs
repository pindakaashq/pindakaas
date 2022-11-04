use std::{
	fmt::Display,
	num::ParseIntError,
	ops::{Add, DerefMut, Mul},
	path::PathBuf,
	str::FromStr,
};

use base::{Encoder, LinExp, LinearConstraint, LinearEncoder, Literal};
use num::{One, Zero};
use pindakaas as base;
use pyo3::{exceptions::PyArithmeticError, prelude::*};

#[cfg(feature = "label")]
unimplemented!("The feature `label` is not implemented for pyndakaas crate");

#[pyclass]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(i32);
impl Literal for Lit {
	fn negate(&self) -> Self {
		Lit(-self.0)
	}
	fn is_negated(&self) -> bool {
		self.0.is_negated()
	}
	fn var(&self) -> Self {
		Lit(self.0.abs())
	}
}
impl Display for Lit {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		self.0.fmt(f)
	}
}
impl FromStr for Lit {
	type Err = ParseIntError;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(Lit(i32::from_str(s)?))
	}
}
impl Zero for Lit {
	fn zero() -> Self {
		Lit(0)
	}
	fn is_zero(&self) -> bool {
		self.0 == 0
	}
}
impl One for Lit {
	fn one() -> Self {
		Lit(1)
	}
}
impl Add for Lit {
	type Output = Lit;
	fn add(self, rhs: Self) -> Self::Output {
		Lit(self.0 + rhs.0)
	}
}
impl Mul for Lit {
	type Output = Lit;
	fn mul(self, rhs: Self) -> Self::Output {
		Lit(self.0 * rhs.0)
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
	let x = LinExp::from_slices(&[1, 2, 3], &[Lit(1), Lit(2), Lit(3)]);
	let con = LinearConstraint::new(x, base::Comparator::Equal, 2);
	let mut enc: LinearEncoder = LinearEncoder::default();
	enc.encode(db, &con)
		.map_err(|_e| PyArithmeticError::new_err("Unsatisfiable"))
}

#[pyclass(name = "CNF")]
struct Cnf(base::Cnf<Lit>);

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
		ClauseIter {
			inner: Vec::from_iter(self.0.iter().map(Vec::from)).into_iter(),
		}
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
