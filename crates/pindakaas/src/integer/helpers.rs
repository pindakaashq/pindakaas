use itertools::Itertools;

use crate::{integer::Dom, Lit};

/// Number of required bits for unsigned Binary encoding with range 0..(ub-lb)
pub(crate) fn required_lits(dom: &Dom) -> usize {
	let cardinality = dom.ub() - dom.lb();
	if cardinality == 0 {
		0
	} else {
		(cardinality.ilog2() + 1) as usize
	}
}

pub(crate) fn display_cnf(cnf: &[Vec<Lit>]) -> String {
	cnf.iter()
		.map(|c| c.iter().join(", "))
		.join("\n")
		.to_owned()
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::Coeff;

	// TODO to be used in future with Binary encoding
	fn nearest_power_of_two(k: Coeff, up: bool) -> Coeff {
		// find next power of one if up (or previous if going down)
		if k == 0 {
			0
		} else {
			Coeff::from(1).rotate_right(if up {
				(k - 1).leading_zeros() // rotate one less to get next power of two
			} else {
				k.leading_zeros() + 1 // rotate one more to get previous power of two
			})
		}
	}

	#[test]
	fn test_required_lits() {
		assert_eq!(required_lits(&Dom::from_bounds(0, 6)), 3);
		assert_eq!(required_lits(&Dom::from_bounds(2, 8)), 3);
		assert_eq!(required_lits(&Dom::from_bounds(0, 0)), 0);
		assert_eq!(required_lits(&Dom::from_bounds(0, 0)), 0);
	}

	#[test]
	fn test_nearest_power_of_two() {
		assert_eq!(nearest_power_of_two(0, true), 0);
		assert_eq!(nearest_power_of_two(1, true), 1);
		assert_eq!(nearest_power_of_two(2, true), 2);
		assert_eq!(nearest_power_of_two(3, true), 4);
		assert_eq!(nearest_power_of_two(4, true), 4);
		assert_eq!(nearest_power_of_two(5, true), 8);
		assert_eq!(nearest_power_of_two(6, true), 8);

		assert_eq!(nearest_power_of_two(0, false), 0);
		assert_eq!(nearest_power_of_two(1, false), 1);
		assert_eq!(nearest_power_of_two(2, false), 2);
		assert_eq!(nearest_power_of_two(3, false), 2);
		assert_eq!(nearest_power_of_two(4, false), 4);
		assert_eq!(nearest_power_of_two(5, false), 4);
		assert_eq!(nearest_power_of_two(6, false), 4);
		assert_eq!(nearest_power_of_two(8, false), 8);
		assert_eq!(nearest_power_of_two(9, false), 8);
	}
}
