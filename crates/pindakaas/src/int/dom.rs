#![allow(dead_code)]
use std::fmt::Display;

use itertools::FoldWhile;
use itertools::Itertools;
use num::iter::RangeInclusive;

use crate::{helpers::is_sorted, Coefficient};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dom<C: Coefficient> {
	pub(crate) ranges: Vec<(C, C)>,
}

impl<C: Coefficient> Dom<C> {
	pub fn constant(d: C) -> Self {
		Self::from_slice(&[d])
	}
	pub fn from_slice(ds: &[C]) -> Self {
		debug_assert!(is_sorted(ds), "{ds:?}");
		let mut ds = ds.iter();
		let k = *ds.next().unwrap();
		let mut k = (k, k);
		let mut ranges = ds
			.flat_map(|&d| {
				if d - k.1 == C::one() {
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
	}

	pub fn from_bounds(lb: C, ub: C) -> Self {
		// debug_assert!(lb <= ub, "Tried to instantiate empty domain {lb}..{ub}");
		if ub < lb {
			Self { ranges: vec![] }
		} else {
			Self {
				ranges: vec![(lb, ub)],
			}
		}
	}

	/// Get i'th domain value
	pub fn d(&self, i: usize) -> Option<C> {
		match self
			.ranges
			.iter()
			.fold_while(C::from(i).unwrap(), |acc, (l, r)| {
				let size = *r - *l + C::one();
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
	pub fn lb(&self) -> C {
		self.ranges.first().unwrap().0
	}

	pub fn ub(&self) -> C {
		self.ranges.last().unwrap().1
	}

	pub fn iter(&self) -> DomIterator<C> {
		let mut ranges = self.ranges.iter();
		let empty = (C::one(), C::zero()); // TODO nicer way to do this (using iter::empty?)
		let r = ranges.next().unwrap_or(&empty);
		let r = num::iter::range_inclusive(r.0, r.1);
		DomIterator { ranges, range: r }
	}

	pub fn is_empty(&self) -> bool {
		self.ranges.is_empty()
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

	// TODO use RangeInclusive
	/// Find position of first domain value >= k/c
	/// Returns Some(0) if first (and all) domain values satisfy the predicate, or None if no domain value satisfy the predicate
	pub(crate) fn geq(&self, k: C) -> Option<usize> {
		// let k = if up { k } else { self.size() - k - C::one() };
		self.iter().position(|d| d >= k)
	}

	pub fn ge(&mut self, d: C) {
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

	pub fn le(&mut self, d: C) {
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

	pub(crate) fn mul(self, rhs: C) -> Self {
		assert!(!rhs.is_negative());
		Dom {
			ranges: self
				.ranges
				.into_iter()
				.map(|(lb, ub)| ((lb * rhs), ub * rhs))
				.collect(),
		}
	}

	// TODO optimize
	pub(crate) fn union(self, rhs: Dom<C>) -> Self {
		Dom::from_slice(
			&[self.iter().collect_vec(), rhs.iter().collect_vec()]
				.concat()
				.into_iter()
				.sorted()
				.dedup()
				.collect_vec(),
		)
	}

	fn invariant(&self) -> bool {
		is_sorted(
			&self
				.ranges
				.iter()
				.flat_map(|r| [r.0, r.1])
				.collect::<Vec<_>>(),
		)
	}
}

#[derive(Clone)]
pub struct DomIterator<'a, C: Coefficient> {
	ranges: std::slice::Iter<'a, (C, C)>,
	range: RangeInclusive<C>,
}

impl<C: Coefficient> Display for Dom<C> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		// TODO replaced {..} for |..| since logger interprets {/} wrong
		let dom = self.iter().collect::<Vec<_>>();
		const ELIPSIZE: usize = 8;
		if dom.is_empty() {
			return writeln!(f, "||");
		}
		let (lb, ub) = (*dom.first().unwrap(), *dom.last().unwrap());
		if dom.len() > 1 && C::from(dom.len()).unwrap() == ub - lb + C::one() {
			write!(f, "|{}..{}|", dom.first().unwrap(), dom.last().unwrap())
		} else if dom.len() > ELIPSIZE {
			write!(
				f,
				"|{},..,{ub}| |{}|",
				dom.iter().take(ELIPSIZE).join(","),
				dom.len()
			)
		} else {
			write!(f, "|{}|", dom.iter().join(","))
		}
	}
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

	// #[test]
	// fn union_test() {
	// 	let a: Vec<C> = vec![1, 2, 3, 7, 8, 9, 11];
	// 	let b: Vec<C> = vec![4, 6, 8];
	// 	let dom = Dom::from_slice(&[1, 2, 3, 7, 8, 9, 11]).union(Dom::from_slice(&[2, 3, 5, 15]));
	// 	// assert_eq!(dom, Dom::from_slice([a, b].concat().sorted().dedup()));
	// }

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

	// TODO stupid issue (could be resolved by moving this to intvar)
	// 	#[test]
	// 	fn test_ineq() {
	// 		let dom = Dom::from_slice(&[2, 5, 6, 7, 9]);

	// 		for (c, k, cmp, expected_dom_pos) in [
	// 			(1, 0, Comparator::GreaterEq, Some(0)),
	// 			(1, 2, Comparator::GreaterEq, Some(0)),
	// 			(1, 3, Comparator::GreaterEq, Some(1)),
	// 			(1, 4, Comparator::GreaterEq, Some(1)),
	// 			(1, 5, Comparator::GreaterEq, Some(1)),
	// 			(1, 6, Comparator::GreaterEq, Some(2)),
	// 			(1, 7, Comparator::GreaterEq, Some(3)),
	// 			(1, 8, Comparator::GreaterEq, Some(4)),
	// 			(1, 9, Comparator::GreaterEq, Some(4)),
	// 			(1, 10, Comparator::GreaterEq, None),
	// 			(1, 11, Comparator::GreaterEq, None),
	// 			(1, 0, Comparator::LessEq, None),
	// 			(1, 2, Comparator::LessEq, Some(1)),
	// 			(1, 3, Comparator::LessEq, Some(1)),
	// 			(1, 4, Comparator::LessEq, Some(1)),
	// 			(1, 5, Comparator::LessEq, Some(2)),
	// 			(1, 6, Comparator::LessEq, Some(3)),
	// 			(1, 7, Comparator::LessEq, Some(4)),
	// 			(1, 8, Comparator::LessEq, Some(4)),
	// 			(1, 9, Comparator::LessEq, Some(0)),
	// 			(1, 10, Comparator::LessEq, Some(0)),
	// 			(1, 11, Comparator::LessEq, Some(0)),
	// 			// 2
	// 			(2, 0, Comparator::GreaterEq, Some(0)),
	// 			(2, 1, Comparator::GreaterEq, Some(0)),
	// 			(2, 2, Comparator::GreaterEq, Some(0)),
	// 			(2, 3, Comparator::GreaterEq, Some(0)),
	// 			(2, 4, Comparator::GreaterEq, Some(0)),
	// 			(2, 5, Comparator::GreaterEq, Some(1)),
	// 			(2, 6, Comparator::GreaterEq, Some(1)),
	// 			(2, 7, Comparator::GreaterEq, Some(1)),
	// 			(2, 18, Comparator::GreaterEq, Some(4)),
	// 			(2, 19, Comparator::GreaterEq, None),
	// 			(2, 0, Comparator::LessEq, None),
	// 			(2, 1, Comparator::LessEq, None),
	// 			(2, 2, Comparator::LessEq, None),
	// 			(2, 3, Comparator::LessEq, None),
	// 			(2, 10, Comparator::LessEq, Some(2)),
	// 			(2, 11, Comparator::LessEq, Some(2)),
	// 			(2, 18, Comparator::LessEq, Some(0)),
	// 			(2, 19, Comparator::LessEq, Some(0)),
	// 			(2, 20, Comparator::LessEq, Some(0)),
	// 		] {
	// 			// TODO remove functionality from unit test
	// 			let c = i32::try_from(c).unwrap();
	// 			let k = i32::try_from(k).unwrap();

	// 			let up = (cmp == Comparator::GreaterEq) == c.is_positive();
	// 			let k = if up { ceil(k / c) } else { k.div_floor(c) };
	// 			assert_eq!(
	// 					dom.ineq(k, cmp == Comparator::GreaterEq),
	// 					expected_dom_pos,
	// 					"Expected {dom} {cmp} {c}/{k} to return position {expected_dom_pos:?}, but returned:"
	// 				);
	// 		}
	// 	}

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
		assert_eq!(dom.geq(-1), Some(0));
		assert_eq!(dom.geq(0), Some(0));
		assert_eq!(dom.geq(1), Some(1));
		assert_eq!(dom.geq(2), None);
		assert_eq!(dom.geq(3), None);

		// assert_eq!(dom.geq(-2, false), None);
		// assert_eq!(dom.geq(-1, false), None);
		// assert_eq!(dom.geq(0, false), Some(1));
		// assert_eq!(dom.geq(1, false), Some(0));
		// assert_eq!(dom.geq(2, false), Some(0));
	}

	#[test]
	fn test_ineq_holey() {
		let dom = Dom::from_slice(&[0, 2, 5]);
		assert_eq!(dom.geq(0), Some(0));
		assert_eq!(dom.geq(1), Some(1));
		assert_eq!(dom.geq(2), Some(1));
		assert_eq!(dom.geq(3), Some(2));
		assert_eq!(dom.geq(5), Some(2));
		assert_eq!(dom.geq(6), None);
	}
}
