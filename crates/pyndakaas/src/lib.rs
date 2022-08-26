use pindakaas::{ClauseDatabase, ClauseSink, Result};
use pyo3::{exceptions::PyTypeError, prelude::*};

/// The type used to represent Literals in the Python Pindakaas library
pub type Lit = i32;
/// The type used to represent Coefficients in the Python Pindakaas library
pub type Coeff = i32;
pub type PosCoeff = u32;

#[pymodule]
#[pyo3(name = "pindakaas")]
fn module(_py: Python, m: &PyModule) -> PyResult<()> {
	m.add_class::<Comparator>()?;
	m.add_function(wrap_pyfunction!(encode_bool_lin, m)?)?;
	Ok(())
}

#[pyfunction(new_var = "None")]
fn encode_bool_lin(
	coeff: Vec<Coeff>,
	lits: Vec<Lit>,
	cmp: Comparator,
	k: Coeff,
	new_var: Option<NewVarFn>,
) -> PyResult<(bool, Vec<Vec<Lit>>)> {
	let mut db = PyClauseDatabase {
		clause_vec: Vec::new(),
		new_var_fn: match new_var {
			Some(func) => func,
			None => NewVarFn::SeqFrom(lits.iter().max().unwrap_or(&0) + 1),
		},
	};
	let cmp = match cmp {
		Comparator::LessEq => pindakaas::Comparator::LessEq,
		Comparator::Equal => pindakaas::Comparator::Equal,
		Comparator::GreaterEq => pindakaas::Comparator::GreaterEq,
	};
	let res = db.encode_bool_lin::<Coeff, PosCoeff>(&coeff, &lits, cmp, k, &[]);
	Ok((res.is_ok(), db.clause_vec))
}

#[pyclass]
#[derive(Debug, Eq, PartialEq, Clone)]
enum Comparator {
	LessEq,
	Equal,
	GreaterEq,
}

struct PyClauseDatabase<'a> {
	clause_vec: Vec<Vec<Lit>>,
	new_var_fn: NewVarFn<'a>,
}

impl<'a> ClauseSink for PyClauseDatabase<'a> {
	type Lit = Lit;

	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
		self.clause_vec.push(Vec::from_iter(cl.iter().copied()));
		Ok(())
	}
}

impl<'a> ClauseDatabase for PyClauseDatabase<'a> {
	fn new_var(&mut self) -> Self::Lit {
		self.new_var_fn.new_var()
	}
}

#[derive(Debug, Clone)]
enum NewVarFn<'a> {
	SeqFrom(i32),
	Call(&'a PyAny),
}

impl<'source> FromPyObject<'source> for NewVarFn<'source> {
	fn extract(obj: &'source PyAny) -> PyResult<Self> {
		if obj.is_callable() {
			return Ok(NewVarFn::Call(obj));
		}
		if let Ok(x) = obj.extract::<i32>() {
			return Ok(NewVarFn::SeqFrom(x));
		}
		Err(PyTypeError::new_err(
			"Expected function or int to give the next new literal",
		))
	}
}

impl<'a> NewVarFn<'a> {
	fn new_var(&mut self) -> i32 {
		match self {
			NewVarFn::SeqFrom(next) => {
				let y = *next;
				*next += 1;
				y
			}
			NewVarFn::Call(fun) => match fun.call0() {
				Ok(obj) => match obj.extract() {
					Ok(next) => next,
					Err(err) => panic!("New literal function did not return an int: {}", err),
				},
				Err(err) => panic!(
					"New literal function could not be called correctly: {}",
					err
				),
			},
		}
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
