use crate::{ClauseSink, Literal, Result};

/// Encode the constraint lits[0] ⊕ ... ⊕ lits[n].
/// # Warning
/// Currently only defined for n ≤ 3.
///
/// # Example
///
/// ```ignore
/// // private module function
/// let mut v = vec![];
/// encode_xor(&mut v, &[1,2]);
/// assert_eq!(v, vec![vec![1,2], vec![-1,-2]])
/// ```
///
pub(crate) fn encode_xor<Lit: Literal, DB: ClauseSink<Lit = Lit> + ?Sized>(
	db: &mut DB,
	lits: &[Lit],
) -> Result {
	match lits {
		[a] => db.add_clause(&[a.clone()]),
		[a, b] => {
			db.add_clause(&[a.clone(), b.clone()])?;
			db.add_clause(&[a.negate(), b.negate()])
		}
		[a, b, c] => {
			db.add_clause(&[a.clone(), b.clone(), c.clone()])?;
			db.add_clause(&[a.clone(), b.negate(), c.negate()])?;
			db.add_clause(&[a.negate(), b.clone(), c.negate()])?;
			db.add_clause(&[a.negate(), b.negate(), c.clone()])
		}
		_ => panic!("Unexpected usage of XOR with more that three arguments"),
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	#[test]
	fn test_xor() {
		let mut v = vec![];
		assert!(encode_xor(&mut v, &[1, 2]).is_ok());
		assert_eq!(v, vec![vec![1, 2], vec![-1, -2]]);
	}
}
