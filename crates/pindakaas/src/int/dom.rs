#![allow(dead_code)]
use std::{collections::HashSet, ops::RangeInclusive};

use itertools::{FoldWhile, Itertools};

use crate::Coeff;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Dom {
	pub(crate) ranges: Vec<(Coeff, Coeff)>, // TODO [?] better to use RangeInclusive rather than tuple?
}

impl Dom {
	pub fn empty() -> Self {
		Self::default()
	}

	pub fn constant(d: Coeff) -> Self {
		Self::from_slice(&[d])
	}
	pub fn is_constant(&self) -> bool {
		self.size() == 1
	}
	pub fn from_slice(ds: &[Coeff]) -> Self {
		let mut ds = ds.iter();
		if let Some(&k) = ds.next() {
			let mut k = (k, k);
			let mut ranges = ds
				.flat_map(|&d| {
					if d - k.1 == 1 {
						k.1 = d;
						None
					} else {
						let res = k;
						k = (d, d);
						Some(res)
					}
				})
				.collect::<Vec<_>>();
			ranges.push(k);

			let self_ = Self { ranges };
			debug_assert!(self_.invariant(), "{self_:?}");
			self_
		} else {
			Self::default()
		}
	}

	pub fn from_bounds(lb: Coeff, ub: Coeff) -> Self {
		if ub < lb {
			Self { ranges: vec![] }
		} else {
			Self {
				ranges: vec![(lb, ub)],
			}
		}
	}

	/// Get i'th domain value
	pub fn d(&self, i: usize) -> Option<Coeff> {
		let i = Coeff::try_from(i).unwrap(); // TODO
		match self.ranges.iter().fold_while(i, |acc, (l, r)| {
			let size = *r - *l + 1;
			if acc < size {
				FoldWhile::Done(*l + acc)
			} else {
				FoldWhile::Continue(acc - size)
			}
		}) {
			FoldWhile::Done(d) => Some(d),
			FoldWhile::Continue(_) => None,
		}
	}

	// TODO return result
	pub fn lb(&self) -> Coeff {
		self.ranges.first().unwrap().0
	}

	pub fn ub(&self) -> Coeff {
		self.ranges.last().unwrap().1
	}

	pub fn iter(&self) -> DomIterator {
		let mut ranges = self.ranges.iter();
		let empty = (1, 0); // TODO [?] nicer way to do this (using iter::empty?)
		let r = ranges.next().unwrap_or(&empty);
		let r = r.0..=r.1;
		DomIterator { ranges, range: r }
	}

	pub fn is_empty(&self) -> bool {
		self.ranges.is_empty()
	}

	// TODO binary search
	pub fn contains(&self, d: Coeff) -> bool {
		self.range(d)
			.map(|r| self.ranges[r].0 <= d)
			.unwrap_or_default() // no range found; does not contain d
	}

	/// Finds first range where d <= range.u
	/// # Examples (TODO non-code since internal)
	///
	/// 0, 8 : [1..2, 4..7] => None
	/// 6 : [1..2, 4..7] => 1
	/// 3 : [1..2, 4..7] => 1
	fn range(&self, d: Coeff) -> Option<usize> {
		self.ranges.iter().position(|r| d <= r.1)
	}

	/// Find position and value of first domain value >= k/c
	/// Returns Some(0) if first (and all) domain values satisfy the predicate, or None if no domain value satisfy the predicate
	pub(crate) fn geq(&self, k: Coeff) -> Option<(usize, Coeff)> {
		// naive: self.iter().position(|d| d >= k)
		match self.ranges.iter().fold_while((0, None), |(p, _), (a, b)| {
			if k <= *b {
				let k = std::cmp::max(*a, k);
				let v = k - *a;
				FoldWhile::Done((p + v, Some(*a + v)))
			} else {
				FoldWhile::Continue((p + *b - *a + 1, None))
			}
		}) {
			FoldWhile::Done((p, v)) => Some(((usize::try_from(p).unwrap()), v.unwrap())),
			FoldWhile::Continue(_) => None,
		}
	}

	pub fn ge(&mut self, d: Coeff) {
		if let Some(r) = self.range(d) {
			if self.ranges[r].1 < d {
				self.ranges = self.ranges[(r + 1)..].to_vec();
			} else {
				self.ranges = self.ranges[r..].to_vec();
				if self.ranges[0].0 < d {
					self.ranges[0].0 = d;
				}
			}
		}
		debug_assert!(self.invariant(), "{self:?}");
	}

	pub fn le(&mut self, d: Coeff) {
		if let Some(r) = self.range(d) {
			if self.ranges[r].0 > d {
				self.ranges = self.ranges[..r].to_vec();
			} else {
				self.ranges = self.ranges[..=r].to_vec();
				let n = self.ranges.len() - 1;
				if self.ranges[n].1 > d {
					self.ranges[n].1 = d;
				}
			}
		}
		debug_assert!(self.invariant(), "{self:?}");
	}

	pub fn size(&self) -> Coeff {
		self.ranges.iter().map(|(l, u)| *u - *l + 1).sum()
	}

	pub(crate) fn add(self, rhs: Coeff) -> Self {
		Dom {
			ranges: self
				.ranges
				.into_iter()
				.map(|(lb, ub)| ((lb + rhs), ub + rhs))
				.collect(),
		}
	}

	pub(crate) fn sumset_size(self, rhs: Dom) -> Coeff {
		self.sumset(rhs).size()
	}
	pub(crate) fn sumset(self, rhs: Dom) -> Self {
		Dom::from_slice(
			&self
				.iter()
				.cartesian_product(rhs.iter())
				.map(|(a, b)| a + b)
				.sorted()
				.dedup()
				.collect_vec(),
		)
	}

	pub(crate) fn mul(self, rhs: Coeff) -> Self {
		assert!(!rhs.is_negative());
		if rhs == 0 {
			Dom::constant(0)
		} else if rhs == 1 {
			self
		} else {
			Dom::from_slice(&self.iter().map(|d| d * rhs).collect_vec())
		}
	}

	// TODO optimize
	pub(crate) fn union(self, rhs: Dom) -> Self {
		Dom::from_slice(
			&[self.iter().collect_vec(), rhs.iter().collect_vec()]
				.concat()
				.into_iter()
				.sorted()
				.dedup()
				.collect_vec(),
		)
	}

	// TODO optimize
	pub(crate) fn intersect(self, rhs: Dom) -> Self {
		Dom::from_slice(
			&self
				.iter()
				.collect::<HashSet<_>>()
				.intersection(&rhs.iter().collect::<HashSet<_>>())
				.map(|i| *i)
				.sorted()
				.dedup() // redundant
				.collect_vec(),
		)
	}

	// TODO check no overlap
	fn invariant(&self) -> bool {
		is_sorted(
			&self
				.ranges
				.iter()
				.flat_map(|r| [r.0, r.1])
				.collect::<Vec<_>>(),
		)
	}

	pub(crate) fn density(&self) -> f64 {
		(self.size() as f64) / ((self.ub() - self.lb() + 1) as f64)
	}
}
#[derive(Debug, Clone)]
pub struct DomIterator<'a> {
	ranges: std::slice::Iter<'a, (Coeff, Coeff)>,
	range: RangeInclusive<Coeff>,
}

impl<'a> Iterator for DomIterator<'a> {
	type Item = Coeff;

	fn next(&mut self) -> Option<Self::Item> {
		// Return next value of current range
		self.range.next().or_else(|| {
			// Or else of the next range
			self.ranges.next().map(|(l, u)| {
				self.range = *l..=*u;
				self.range.next().expect("No empty ranges expected")
			})
		})
	}

	// TODO size_hint/count
	// fn size_hint(&self) -> (usize, Option<usize>) {
	// 	self.size.size_hint()
	// }
	// fn count(self) -> usize {
	// 	self.size.count()
	// }
}

pub(crate) fn is_sorted<T: Ord>(xs: &[T]) -> bool {
	xs.windows(2).all(|x| x[0] <= x[1])
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn union_test() {
		let a: Vec<Coeff> = vec![1, 2, 3, 7, 8, 9, 11];
		let b: Vec<Coeff> = vec![4, 6, 8];
		let dom = Dom::from_slice(&a).union(Dom::from_slice(&b));
		let exp = Dom::from_slice(&[a, b].concat().into_iter().sorted().dedup().collect_vec());
		assert_eq!(dom, exp);
	}

	#[test]
	fn dom_test() {
		let ds = vec![1, 2, 3, 7, 8, 9, 11];
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

	#[test]
	fn test_d_index() {
		let dom = Dom::from_slice(&[0, 2, 5, 6]);
		assert_eq!(dom.d(0), Some(0));
		assert_eq!(dom.d(1), Some(2));
		assert_eq!(dom.d(2), Some(5));
		assert_eq!(dom.d(3), Some(6));
		assert_eq!(dom.d(4), None);
	}

	#[test]
	fn test_ineq() {
		let dom = Dom::from_slice(&[0, 1]);
		assert_eq!(dom.geq(-1), Some((0, 0)));
		assert_eq!(dom.geq(0), Some((0, 0)));
		assert_eq!(dom.geq(1), Some((1, 1)));
		assert_eq!(dom.geq(2), None);
		assert_eq!(dom.geq(3), None);
	}

	#[test]
	fn test_ineq_holey() {
		let dom = Dom::from_slice(&[0, 2, 5, 6]);
		assert_eq!(dom.geq(0), Some((0, 0)));
		assert_eq!(dom.geq(1), Some((1, 2)));
		assert_eq!(dom.geq(2), Some((1, 2)));
		assert_eq!(dom.geq(3), Some((2, 5)));
		assert_eq!(dom.geq(5), Some((2, 5)));
		assert_eq!(dom.geq(6), Some((3, 6)));
		assert_eq!(dom.geq(7), None);
	}
}
