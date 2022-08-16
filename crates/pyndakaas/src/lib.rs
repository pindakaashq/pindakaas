use pyo3::{exceptions::PyTypeError, prelude::*};

#[derive(Debug, Clone)]
enum NewLitFn<'a> {
	SeqFrom(i32),
	Call(&'a PyAny),
}

impl<'source> FromPyObject<'source> for NewLitFn<'source> {
	fn extract(obj: &'source PyAny) -> PyResult<Self> {
		if obj.is_callable() {
			return Ok(NewLitFn::Call(obj));
		}
		if let Ok(x) = obj.extract::<i32>() {
			return Ok(NewLitFn::SeqFrom(x));
		}
		Err(PyTypeError::new_err(
			"Expected function or int to give the next new literal",
		))
	}
}

impl<'a> NewLitFn<'a> {
	fn next_lit(&mut self) -> i32 {
		match self {
			NewLitFn::SeqFrom(next) => {
				let y = next.clone();
				*next += 1;
				y
			}
			NewLitFn::Call(fun) => match fun.call0() {
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

#[pymodule]
#[pyo3(name = "pindakaas")]
fn module(_py: Python, _m: &PyModule) -> PyResult<()> {
	Ok(())
}

#[cfg(test)]
mod tests {
	#[test]
	fn it_works() {
		let result = 2 + 2;
		assert_eq!(result, 4);
	}
}
