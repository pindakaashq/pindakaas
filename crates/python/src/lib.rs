use pyo3::prelude::*;

#[pyfunction]
fn double(x: usize) -> usize {
	x * 2
}

#[pymodule]
#[pyo3(name = "pindakaas")]
fn module(_py: Python, m: &PyModule) -> PyResult<()> {
	m.add_function(wrap_pyfunction!(double, m)?)?;
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
