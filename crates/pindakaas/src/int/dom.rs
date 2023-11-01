use num::iter::RangeInclusive;

use crate::Coefficient;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dom<C: Coefficient> {
	pub(crate) ranges: Vec<(C, C)>,
}

impl<C: Coefficient> Dom<C> {
	pub fn from_slice(ds: &[C]) -> Self {
		let mut ds = ds.into_iter();
		let k = ds.next().unwrap().clone();
		let mut k = (k, k);
		let mut ranges = ds
			.into_iter()
			.flat_map(|&d| {
				if d - k.1 == C::one() {
					k.1 = d;
					None
				} else {
					let res = k.clone();
					k = (d, d);
					Some(res)
				}
			})
			.collect::<Vec<_>>();
		ranges.push(k);

		Self { ranges }
	}

	pub fn from_bounds(lb: C, ub: C) -> Self {
		Self {
			ranges: vec![(lb, ub)],
		}
	}

	// TODO return result
	pub fn lb(&self) -> C {
		self.ranges.first().unwrap().0
	}

	pub fn ub(&self) -> C {
		self.ranges.last().unwrap().1
	}

	pub fn iter(&self) -> DomIterator<C> {
		// pub fn values(&self) -> Vec<C> {
		// self.ranges
		// 	.iter()
		// 	.flat_map(|(lb, ub)| num::range_inclusive(*lb, *ub))
		// 	.collect()
		let mut ranges = self.ranges.iter();
		let r = ranges.next().unwrap();
		let r = num::iter::range_inclusive(r.0, r.1);
		DomIterator { ranges, range: r }
		// DomIterator {
		// 	ranges: self.ranges.iter(),
		// 	i: 0,
		// 	j: self.ranges[0].0,
		// 	k: self.ranges[0].1,
		// }
	}

	// TODO binary search
	pub fn contains(&self, d: C) -> bool {
		self.range(d)
			.map(|r| self.ranges[r].0 <= d)
			.unwrap_or_default() // no range found; does not contain d
	}

	// 0, 8 : [1..2, 4..7] => None
	// 6 : [1..2, 4..7] => 1
	// 3 : [1..2, 4..7] => 1
	/// Finds first range where d <= range.u
	fn range(&self, d: C) -> Option<usize> {
		self.ranges.iter().position(|r| d <= r.1)
	}

	pub fn ge(&mut self, d: C) {
		if let Some(r) = self.range(d) {
			self.ranges = self.ranges[r..].into_iter().cloned().collect();
			if self.ranges[0].0 < d {
				self.ranges[0].0 = d;
			}
		}
	}

	pub fn le(&mut self, d: C) {
		if let Some(r) = self.ranges.iter().position(|r| d <= r.1) {
			self.ranges = self.ranges[..=r].into_iter().cloned().collect();
			let n = self.ranges.len() - 1;
			if self.ranges[n].1 > d {
				self.ranges[n].1 = d;
			}
		}
	}

	pub fn size(&self) -> C {
		self.ranges
			.iter()
			.map(|(l, u)| *u - *l + C::one())
			.fold(C::zero(), C::add)
	}

	pub(crate) fn add(self, rhs: C) -> Self {
		Dom {
			ranges: self
				.ranges
				.into_iter()
				.map(|(lb, ub)| ((lb + rhs), ub + rhs))
				.collect(),
		}
	}
}

#[derive(Clone)]
pub struct DomIterator<'a, C: Coefficient> {
	ranges: std::slice::Iter<'a, (C, C)>,
	range: RangeInclusive<C>,
}

impl<'a, C: Coefficient> Iterator for DomIterator<'a, C> {
	type Item = C;

	fn next(&mut self) -> Option<Self::Item> {
		// Return next value of current range
		self.range.next().or_else(|| {
			// Or else of the next range
			self.ranges.next().map(|(l, u)| {
				self.range = num::iter::range_inclusive(*l, *u);
				self.range.next().expect("No empty ranges expected")
			})
		})
	}

	// TODO
	// fn size_hint(&self) -> (usize, Option<usize>) {
	// 	self.size.size_hint()
	// }
	// fn count(self) -> usize {
	// 	self.size.count()
	// }
}

#[cfg(test)]
mod tests {
	type C = i32;

	use super::*;

	#[test]
	fn dom_test() {
		let ds: Vec<C> = vec![1, 2, 3, 7, 8, 9, 11];
		let dom = Dom::from_slice(&ds);
		assert_eq!(dom.size() as usize, ds.len());
		assert_eq!(
			dom,
			Dom {
				ranges: vec![(1, 3), (7, 9), (11, 11)],
			}
		);

		let mut dom_ge_8 = dom.clone();
		dom_ge_8.ge(8);
		assert_eq!(
			dom_ge_8,
			Dom {
				ranges: vec![(8, 9), (11, 11)],
			}
		);

		let mut dom_le_8 = dom.clone();
		dom_le_8.le(8);
		assert_eq!(
			dom_le_8,
			Dom {
				ranges: vec![(1, 3), (7, 8)],
			}
		);

		assert!(!dom.contains(0));
		assert!(dom.contains(8));
		assert!(!dom.contains(10));
		assert!(!dom.contains(12));

		assert_eq!(dom.iter().collect::<Vec<_>>(), ds);

		assert_eq!(
			dom.add(3),
			Dom {
				ranges: vec![(4, 6), (10, 12), (14, 14)],
			}
		);
	}
}
