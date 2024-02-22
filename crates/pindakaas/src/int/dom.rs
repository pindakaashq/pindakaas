#![allow(dead_code)]
use std::fmt::Display;

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
		debug_assert!(lb <= ub);
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
		let mut ranges = self.ranges.iter();
		let r = ranges.next().unwrap();
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
	/// Find position of first domain value >= k/c (or <= k/c)
	/// Returns Some(0) if first (and all) domain values satisfy the predicate, or None if no domain value satisfy the predicate (respectively, true and false)
	pub(crate) fn ineq(&self, k: C, c: C, up: bool) -> Option<usize> {
		// let up = (cmp == &Comparator::GreaterEq) == self.c.is_positive();
		let k = if up {
			k.div_ceil(&c)
		} else {
			// c.div_floor(&self.c) + C::one()
			k.div_floor(&c)
		};
		let ds = self.iter().collect::<Vec<_>>();
		let n = ds.len();
		let ds = if up {
			ds.iter().collect::<Vec<_>>()
		} else {
			ds.iter().rev().collect::<Vec<_>>()
		};
		ds.into_iter()
			.copied()
			.position(|d| if up { d >= k } else { d <= k })
			.map(|pos| {
				if up {
					pos
				} else if pos == 0 {
					// transform Some(n) into Some(0)
					0
				} else {
					n - pos
				}
			})

		// TODO faster method, to test
		// self.ranges.iter().fold_while(0, |r, acc| {
		// 	let r_card = r.1 - r.0 + 1; // cardinality of range
		// 	if c <= r.1 {
		// 		itertools::FoldWhile::Done(acc + r_card)
		// 	} else {
		// 		itertools::FoldWhile::Continue(acc + std::cmp::min(1, (c - r.0)))
		// 	}
		// })
		// self.[self.x.borrow().dom.iter().position(|d| d == c).unwrap() - 1]
	}

	// fn position(&self, d: C) -> Option<usize> {}

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
		let dom = self.iter().collect::<Vec<_>>();
		const ELIPSIZE: usize = 8;
		if dom.is_empty() {
			return writeln!(f, "{{}}");
		}
		let (lb, ub) = (*dom.first().unwrap(), *dom.last().unwrap());
		if dom.len() > ELIPSIZE && C::from(dom.len()).unwrap() == ub - lb + C::one() {
			write!(f, "{}..{}", dom.first().unwrap(), dom.last().unwrap())
		} else if dom.len() > ELIPSIZE {
			write!(
				f,
				"{{{},..,{ub}}} |{}|",
				dom.iter().take(ELIPSIZE).join(","),
				dom.len()
			)
		} else {
			write!(f, "{{{}}}", dom.iter().join(","))
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

	use crate::Comparator;

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

	#[test]
	fn test_ineq() {
		let dom = Dom::from_slice(&[2, 5, 6, 7, 9]);

		for (c, k, cmp, expected_dom_pos) in [
			(1, 0, Comparator::GreaterEq, Some(0)),
			(1, 2, Comparator::GreaterEq, Some(0)),
			(1, 3, Comparator::GreaterEq, Some(1)),
			(1, 4, Comparator::GreaterEq, Some(1)),
			(1, 5, Comparator::GreaterEq, Some(1)),
			(1, 6, Comparator::GreaterEq, Some(2)),
			(1, 7, Comparator::GreaterEq, Some(3)),
			(1, 8, Comparator::GreaterEq, Some(4)),
			(1, 9, Comparator::GreaterEq, Some(4)),
			(1, 10, Comparator::GreaterEq, None),
			(1, 11, Comparator::GreaterEq, None),
			(1, 0, Comparator::LessEq, None),
			(1, 2, Comparator::LessEq, Some(1)),
			(1, 3, Comparator::LessEq, Some(1)),
			(1, 4, Comparator::LessEq, Some(1)),
			(1, 5, Comparator::LessEq, Some(2)),
			(1, 6, Comparator::LessEq, Some(3)),
			(1, 7, Comparator::LessEq, Some(4)),
			(1, 8, Comparator::LessEq, Some(4)),
			(1, 9, Comparator::LessEq, Some(0)),
			(1, 10, Comparator::LessEq, Some(0)),
			(1, 11, Comparator::LessEq, Some(0)),
			// 2
			(2, 0, Comparator::GreaterEq, Some(0)),
			(2, 1, Comparator::GreaterEq, Some(0)),
			(2, 2, Comparator::GreaterEq, Some(0)),
			(2, 3, Comparator::GreaterEq, Some(0)),
			(2, 4, Comparator::GreaterEq, Some(0)),
			(2, 5, Comparator::GreaterEq, Some(1)),
			(2, 6, Comparator::GreaterEq, Some(1)),
			(2, 7, Comparator::GreaterEq, Some(1)),
			(2, 18, Comparator::GreaterEq, Some(4)),
			(2, 19, Comparator::GreaterEq, None),
			(2, 0, Comparator::LessEq, None),
			(2, 1, Comparator::LessEq, None),
			(2, 2, Comparator::LessEq, None),
			(2, 3, Comparator::LessEq, None),
			(2, 10, Comparator::LessEq, Some(2)),
			(2, 11, Comparator::LessEq, Some(2)),
			(2, 18, Comparator::LessEq, Some(0)),
			(2, 19, Comparator::LessEq, Some(0)),
			(2, 20, Comparator::LessEq, Some(0)),
		] {
			assert_eq!(
				dom.ineq(k, c, cmp == Comparator::GreaterEq),
				expected_dom_pos,
				"Expected {dom} {cmp} {c}/{k} to return position {expected_dom_pos:?}, but returned:"
			);
		}
	}
}
