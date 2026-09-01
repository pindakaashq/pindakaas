//! Dynamic-programming based planning for single-constant multiplication.
//!
//! The implementation in this module follows the decomposition rules from the
//! paper "Dynamic Programming and Tabled Logic Programming for Encoding
//! Single-Constant Multiplication into SAT". The search explores the
//! decomposition schemes using:
//!
//! - `splus`: `C = (C1 << S) + C2`
//! - `sminus`: `C = (C1 << S) - C2`
//! - `minuss`: `C = C1 - (C2 << S)`
//!
//! The resulting plan is returned in topological order so it can be executed
//! directly from the input `x`.

use std::{
	cmp::Ordering,
	fmt::{self, Display, Formatter},
	iter::from_fn,
	num::NonZero,
};

use rustc_hash::{FxHashMap, FxHashSet};

/// The best sub-plan found for one coefficient during the DP search.
///
/// A plan is identified by the set of unique intermediate coefficients it
/// produces; its cost is the sum of the costs of the operations producing them.
#[derive(Clone, Debug, PartialEq, Eq)]
struct InternalPlan {
	/// The plan's total cost under the active objective (half/full adders for
	/// min-a, or the operation count for min-k).
	cost: u32,
	/// The operation that produces the coefficient for this plan entry.
	operation: Option<ScmOperation>,
	/// The cost of `operation` alone (0 when there is no operation), cached so
	/// the union cost can be summed without recomputing each operation's cost.
	op_cost: u32,
	/// Sorted list of unique intermediate coefficients required for this plan
	/// (excluding 1 and the coefficient itself).
	intermediates: Vec<ScmCoeff>,
}

/// Identifier for an SCM intermediate.
///
/// This is not the runtime value of an expression. Instead, it names the
/// intermediate by the coefficient it represents: `ScmCoeff(k)` stands for the
/// value `k * x`. Operands refer to previously computed intermediates by this
/// identifier, so a dedicated type makes that relationship explicit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ScmCoeff(u32);

/// The optimization objective for an SCM plan.
///
/// The two variants mirror the paper's two objectives. Both are minimized by
/// the same dynamic program; only the per-operation cost differs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ScmObjective {
	#[cfg_attr(
		not(test),
		expect(
			dead_code,
			reason = "the width-independent objective, kept for the paper's min-k figures and for reuse of a product across widths"
		)
	)]
	/// Minimize the number of addition/subtraction operations (the paper's
	/// min-k objective). Every operation counts as one and pure shifts are
	/// free, so the result depends only on the constant, not on the input
	/// width.
	MinAddition,
	/// Minimize the number of one-bit half/full adders (the paper's min-a
	/// objective) for an input `x` of the given bit width. Operation costs
	/// depend on the operand widths and therefore on the width of `x`.
	MinAdders(NonZero<u32>),
}

/// A single step in an SCM plan.
///
/// The result of each operation is not stored explicitly because it can be
/// uniquely derived from the operands and shift amount. This reduces the
/// memory footprint of candidate plans during the DP search.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ScmOperation {
	/// `result = (left << shift) + right`
	ShiftAdd {
		/// The left operand before shifting.
		left: ScmCoeff,
		/// The right operand.
		right: ScmCoeff,
		/// The amount of left shift applied to `left`.
		shift: u32,
	},
	/// `result = (left << shift) - right`
	ShiftSub {
		/// The left operand before shifting.
		left: ScmCoeff,
		/// The right operand.
		right: ScmCoeff,
		/// The amount of left shift applied to `left`.
		shift: u32,
	},
	/// `result = left - (right << shift)`
	SubShift {
		/// The left operand.
		left: ScmCoeff,
		/// The right operand before shifting.
		right: ScmCoeff,
		/// The amount of left shift applied to `right`.
		shift: u32,
	},
	/// `result = source << shift`
	ShiftLeft {
		/// The value being shifted.
		source: ScmCoeff,
		/// The amount of left shift applied to `source`.
		shift: u32,
	},
}

/// A synthesized SCM plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ScmSolution {
	/// The target constant multiplier.
	pub(crate) constant: ScmCoeff,
	/// The objective the plan was synthesized for.
	///
	/// The objective fixes the cost model: [`ScmObjective::MinAddition`] counts
	/// operations, while [`ScmObjective::MinAdders`] counts half/full adders
	/// for a specific input bit width.
	pub(crate) objective: ScmObjective,
	/// The accumulated cost of the plan under `objective`.
	pub(crate) cost: u32,
	/// The operations in execution order.
	///
	/// The sequence is topologically sorted so a caller can evaluate it from
	/// left to right without doing its own dependency scheduling.
	pub(crate) operations: Vec<ScmOperation>,
}

/// Return the binary length of `value`.
///
/// The cost model uses widths rather than magnitudes because adder size is
/// driven by operand bit width.
fn bit_length(value: u32) -> u32 {
	u32::BITS - value.leading_zeros()
}

/// Iteratively emit operations for a plan into an output vector in topological
/// order.
///
/// This avoids recursion to prevent stack overflow on deep trees and ensures
/// that shared sub-expressions are only emitted once.
fn emit_operations(
	target: ScmCoeff,
	memo: &FxHashMap<ScmCoeff, InternalPlan>,
) -> Vec<ScmOperation> {
	/// One traversal state in the iterative dependency walk.
	#[derive(Clone, Copy, Debug)]
	enum WorkItem {
		/// Reachable but dependencies may not be emitted.
		Discover(ScmCoeff),
		/// Dependencies are guaranteed to be in the output; emit the operation.
		Emit(ScmOperation),
	}

	let mut emitted = FxHashSet::default();
	let mut output = Vec::new();
	let mut work_list = vec![WorkItem::Discover(target)];
	while let Some(item) = work_list.pop() {
		match item {
			WorkItem::Discover(coeff) => {
				// Base case or already emitted sub-expression.
				if coeff == ScmCoeff::INPUT || emitted.contains(&coeff) {
					continue;
				}

				let plan = memo
					.get(&coeff)
					.expect("all reached coefficients must be in memo");
				let op = plan.operation.expect("operation exists for target > 1");

				// Schedule the emission of this operation after its
				// dependencies. Pushing 'Emit' first means it will be
				// popped last (LIFO).
				work_list.push(WorkItem::Emit(op));

				let (first, second) = op.dependencies();
				// Schedule dependencies for discovery.
				// The order here ensures that the first dependency is processed
				// first.
				if let Some(second) = second {
					work_list.push(WorkItem::Discover(second));
				}
				work_list.push(WorkItem::Discover(first));
			}
			WorkItem::Emit(op) => {
				let result = op.result();
				// Shared sub-expressions might have been emitted while this
				// 'Emit' was pending on the stack.
				if !emitted.contains(&result) {
					output.push(op);
					let _ = emitted.insert(result);
				}
			}
		}
	}
	output
}

/// Yield a dependency's required intermediates (its own sub-intermediates plus
/// the dependency itself) in sorted order.
///
/// The dependency is not necessarily larger than its own sub-intermediates (a
/// MINUSS minuend exceeds its result), so it is merged into position rather
/// than appended. `ScmCoeff::INPUT` is never an intermediate, so it is dropped.
fn intermediates_with(
	intermediates: &[ScmCoeff],
	extra: ScmCoeff,
) -> impl Iterator<Item = ScmCoeff> + '_ {
	merge_coeffs(
		intermediates.iter().copied(),
		(extra != ScmCoeff::INPUT).then_some(extra).into_iter(),
	)
}

/// Lazily merge two sorted, duplicate-free iterators of coefficients into one
/// sorted, duplicate-free iterator. A coefficient present in both streams is
/// yielded once (the shared-subexpression case).
fn merge_coeffs<I1, I2>(a: I1, b: I2) -> impl Iterator<Item = ScmCoeff>
where
	I1: Iterator<Item = ScmCoeff>,
	I2: Iterator<Item = ScmCoeff>,
{
	let mut a = a.peekable();
	let mut b = b.peekable();
	from_fn(move || match (a.peek().copied(), b.peek().copied()) {
		(Some(av), Some(bv)) => match av.cmp(&bv) {
			Ordering::Less => a.next(),
			Ordering::Greater => b.next(),
			// Shared sub-expression: consume both, yield it once.
			Ordering::Equal => {
				let _ = b.next();
				a.next()
			}
		},
		(Some(_), None) => a.next(),
		(None, Some(_)) => b.next(),
		(None, None) => None,
	})
}

impl Ord for InternalPlan {
	/// Compare two candidate plans.
	///
	/// Cost is the primary objective. Tie-breaking by plan structure ensures
	/// deterministic results.
	fn cmp(&self, other: &Self) -> Ordering {
		self.cost
			.cmp(&other.cost)
			.then_with(|| self.operation.cmp(&other.operation))
			.then_with(|| self.intermediates.cmp(&other.intermediates))
	}
}

impl PartialOrd for InternalPlan {
	/// Delegate to the total ordering used by the DP minimization step.
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl ScmCoeff {
	/// The input value `x`, represented as the coefficient `1 * x`.
	const INPUT: Self = Self(1);

	/// Enumerate all candidate operations for this odd coefficient.
	///
	/// Keeping the three split families explicit preserves the structure of the
	/// reference algorithm and makes it easier to compare Rust behavior against
	/// the paper and the Picat prototype.
	fn candidate_operations(self) -> impl Iterator<Item = ScmOperation> {
		// The three rules assume an odd coefficient: it makes C2 odd in SPLUS
		// and SMINUS, and the SPLUS/MINUSS minuends odd, so the splits never
		// need to guard or normalize for those cases.
		debug_assert!(
			self.get() % 2 == 1,
			"decomposition rules assume an odd coefficient"
		);
		let pp = self
			.split_pp()
			.map(move |(left, right, shift)| ScmOperation::ShiftAdd { left, right, shift });
		let pn = self
			.split_pn()
			.map(move |(left, right, shift)| ScmOperation::ShiftSub { left, right, shift });
		let np = self
			.split_np()
			.map(move |(left, right, shift)| ScmOperation::SubShift { left, right, shift });
		pp.chain(pn).chain(np)
	}

	/// Return the represented coefficient.
	pub(crate) fn get(self) -> u32 {
		self.0
	}

	/// Construct an SCM coefficient identifier from a coefficient.
	///
	/// The module stores coefficients as `u32` because every intermediate is
	/// bounded by the target multiplier and that is sufficient for the intended
	/// use in this crate.
	fn new(value: u32) -> Self {
		Self(value)
	}

	/// Generate the `minuss` split `C = C1 - (C2 << S)`.
	///
	/// This rule captures cases where subtracting a shifted value from a larger
	/// constant is efficient. For example, 13 = 15 - (1 << 1).
	/// The formulas find a C1 > C such that C1 - (C2 << s) = C.
	fn split_np(self) -> impl Iterator<Item = (ScmCoeff, ScmCoeff, u32)> {
		let current = self.get();
		let n = bit_length(current);
		(1..n).filter_map(move |s| {
			// C2 is the one's complement of the high part `C >> s` (in `n - s`
			// bits). It is odd exactly when bit s of C is 0, which is the
			// condition for a MINUSS cut at position s.
			let c2 = ((1_u32 << (n - s)) - 1).wrapping_sub(current >> s);
			if c2 % 2 != 1 {
				return None;
			}
			let low_mask = (1_u32 << s) - 1;
			// The minuend C1 = 2^n - 2^s + (low s bits) is larger than C and
			// always odd, so it needs no trailing-zero normalization.
			let c1 = (1_u32 << n) - (1_u32 << s) + (current & low_mask);
			Some((ScmCoeff::new(c1), ScmCoeff::new(c2), s))
		})
	}

	/// Generate the `sminus` split `C = (C1 << S) - C2`.
	///
	/// This rule captures cases where a coefficient can be represented as a
	/// power of two minus some value. For example, 7 = (1 << 3) - 1.
	/// The formulas are derived by splitting the binary representation of C
	/// into parts 'a' and 'b' such that C = (a << s) | b, and then finding a
	/// C1 slightly larger than 'a' such that C = (C1 << s) - C2.
	fn split_pn(self) -> impl Iterator<Item = (ScmCoeff, ScmCoeff, u32)> {
		let current = self.get();
		let n = bit_length(current);
		(1..=n).map(move |s| {
			// With C1 = (C >> s) + 1 and C2 = 2^s - (C mod 2^s) we have
			// C = (C1 << s) - C2 for any s. C2 is always odd because C is.
			let low_mask = (1_u32 << s) - 1;
			let c2 = (1_u32 << s).wrapping_sub(current & low_mask);
			let c1 = (current + c2) >> s;
			let zeros = c1.trailing_zeros();
			// Fold C1's trailing zeros into the shift (shifts are free).
			(ScmCoeff::new(c1 >> zeros), ScmCoeff::new(c2), s + zeros)
		})
	}

	/// Generate the `splus` split `C = (C1 << S) + C2`.
	///
	/// The Picat prototype explores this split by scanning the binary
	/// representation and peeling off any low-order suffix.
	fn split_pp(self) -> impl Iterator<Item = (ScmCoeff, ScmCoeff, u32)> {
		let current = self.get();
		let n = bit_length(current);
		(1..n).filter_map(move |s| {
			// Split C into the high part C1 = C >> s and the low s bits C2.
			// Take the cut only when bit s-1 is set, so that C2 really spans
			// s bits; otherwise the same split is also produced at a smaller
			// s. C2 is odd because C is.
			if (current >> (s - 1)) & 1 == 0 {
				return None;
			}
			let c2 = current & ((1_u32 << s) - 1);
			let c1 = current >> s;
			let zeros = c1.trailing_zeros();
			// Fold C1's trailing zeros into the shift (shifts are free).
			Some((ScmCoeff::new(c1 >> zeros), ScmCoeff::new(c2), s + zeros))
		})
	}

	/// Return the effective operand width used by the reference cost model.
	///
	/// The multiplier `1` is treated specially because it corresponds to the
	/// original input `x`, which does not need an intermediate adder structure
	/// of its own.
	fn width(self) -> u32 {
		if self == Self::INPUT {
			0
		} else {
			bit_length(self.get())
		}
	}
}

impl Display for ScmCoeff {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		Display::fmt(&self.0, f)
	}
}

impl ScmOperation {
	/// Compute the contribution of this step to the cost model.
	///
	/// Pure shifts are assigned zero cost because they do not consume adders.
	/// The remaining formulas intentionally mirror the Picat reference so the
	/// Rust port stays comparable to the published recurrence.
	fn cost(self, objective: ScmObjective) -> u32 {
		let x_bits = match objective {
			// min-k: every operation counts as one; pure shifts stay free.
			ScmObjective::MinAddition => {
				return match self {
					Self::ShiftLeft { .. } => 0,
					_ => 1,
				};
			}
			ScmObjective::MinAdders(x_bits) => x_bits.get(),
		};
		match self {
			Self::ShiftLeft { .. } => 0,
			Self::ShiftAdd {
				left, right, shift, ..
			} => {
				let w1 = left.width() + x_bits;
				let w2 = right.width() + x_bits;
				// When the shift is at least the right operand's width the
				// operands do not overlap, so the addition needs no adders.
				if shift >= w2 {
					0
				} else {
					w1.max(w2 - shift)
				}
			}
			Self::SubShift { right, shift, .. } => {
				let result = self.result();
				let w1 = result.width() + x_bits;
				let w2 = right.width() + x_bits;
				if shift >= w2 {
					0
				} else {
					w1.max(w2 - shift)
				}
			}
			Self::ShiftSub { .. } => {
				// Subtraction cost is dominated by the result bit width.
				let result = self.result();
				bit_length(result.get()) + x_bits
			}
		}
	}

	/// Return the dependencies of this step.
	///
	/// Every SCM step depends on one mandatory coefficient and optionally a
	/// second one. Returning that shape directly makes the call sites reflect
	/// the structure of the operation graph.
	fn dependencies(self) -> (ScmCoeff, Option<ScmCoeff>) {
		match self {
			Self::ShiftAdd { left, right, .. }
			| Self::ShiftSub { left, right, .. }
			| Self::SubShift { left, right, .. } => (left, Some(right)),
			Self::ShiftLeft { source, .. } => (source, None),
		}
	}

	/// Return the intermediate produced by this step.
	///
	/// The planner keys intermediates by coefficient, so the produced value is
	/// the identity used by memoization and scheduling. We calculate it on the
	/// fly to keep the operation enum compact.
	pub(crate) fn result(self) -> ScmCoeff {
		match self {
			Self::ShiftAdd { left, right, shift } => {
				ScmCoeff::new((left.get() << shift) + right.get())
			}
			Self::ShiftSub { left, right, shift } => {
				ScmCoeff::new((left.get() << shift) - right.get())
			}
			Self::SubShift { left, right, shift } => {
				ScmCoeff::new(left.get() - (right.get() << shift))
			}
			Self::ShiftLeft { source, shift } => ScmCoeff::new(source.get() << shift),
		}
	}
}

impl Display for ScmOperation {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		let result = self.result();
		match self {
			Self::ShiftAdd { left, right, shift } => {
				write!(f, "{result} = {left}*(1<<{shift})+{right}")
			}
			Self::ShiftSub { left, right, shift } => {
				write!(f, "{result} = {left}*(1<<{shift})-{right}")
			}
			Self::SubShift { left, right, shift } => {
				write!(f, "{result} = {left}-{right}*(1<<{shift})")
			}
			Self::ShiftLeft { source, shift } => write!(f, "{result} = {source}*(1<<{shift})"),
		}
	}
}

impl ScmSolution {
	/// Evaluate the plan for a concrete input value.
	///
	/// This helper exists only in tests. It uses `i128` to avoid overflows
	/// when validating plans for large constants.
	#[cfg(test)]
	fn evaluate(&self, x: i64) -> i128 {
		let mut values = FxHashMap::default();
		let _ = values.insert(ScmCoeff::INPUT, x as i128);
		for op in &self.operations {
			let value = match *op {
				ScmOperation::ShiftAdd {
					left, right, shift, ..
				} => (values[&left] << shift) + values[&right],
				ScmOperation::ShiftSub {
					left, right, shift, ..
				} => (values[&left] << shift) - values[&right],
				ScmOperation::SubShift {
					left, right, shift, ..
				} => values[&left] - (values[&right] << shift),
				ScmOperation::ShiftLeft { source, shift, .. } => values[&source] << shift,
			};
			let _ = values.insert(op.result(), value);
		}
		values.get(&self.constant).copied().unwrap_or(0)
	}

	/// Synthesize an SCM plan for `constant` under `objective`.
	///
	/// The function is intentionally total:
	///
	/// - `constant == 0` produces an empty zero-cost plan,
	/// - `constant == 1` (or a power of two) produces a shift-only plan,
	/// - even constants are reduced to an odd subproblem plus a final shift.
	pub(crate) fn synthesize(constant: u32, objective: ScmObjective) -> Self {
		// Trivial case: multiplying by zero needs no operations.
		if constant == 0 {
			return Self {
				constant: ScmCoeff::new(constant),
				objective,
				cost: 0,
				operations: Vec::new(),
			};
		}

		// Reduce an even constant to its odd part plus a final shift; the shift
		// is free, so only the odd part needs a plan.
		let shift = constant.trailing_zeros();
		let odd_constant = ScmCoeff::new(constant >> shift);

		// The memoization map stores the best plan found so far for each
		// coefficient.
		let mut memo: FxHashMap<ScmCoeff, InternalPlan> = FxHashMap::default();
		let _ = memo.insert(
			ScmCoeff::INPUT,
			InternalPlan {
				cost: 0,
				operation: None,
				op_cost: 0,
				intermediates: Vec::new(),
			},
		);

		// Coefficients that have already been expanded. A coefficient may be
		// pushed many times (each dependent re-pushes it) but is expanded and
		// solved only once; this bounds the search even though MINUSS
		// dependencies grow above `coeff`.
		let mut discovered: FxHashSet<ScmCoeff> = FxHashSet::default();

		// Iterative DP over a work list, avoiding deep recursion. Each
		// coefficient is discovered once (scheduling its dependencies and
		// then its own solve) and solved once, after those dependencies by
		// LIFO order.
		#[derive(Clone, Copy, Debug)]
		enum WorkItem {
			Discover(ScmCoeff),
			Solve(ScmCoeff),
		}

		// The input (coefficient 1) is the base case and is never scheduled.
		let mut work_list = Vec::new();
		if odd_constant != ScmCoeff::INPUT {
			work_list.push(WorkItem::Discover(odd_constant));
		}
		while let Some(item) = work_list.pop() {
			match item {
				WorkItem::Discover(coeff) => {
					// Expand each coefficient once.
					if !discovered.insert(coeff) {
						continue;
					}

					// Schedule the solve first so it is popped only after the
					// dependencies pushed above it. Each dependent
					// re-pushes its own dependencies, so a
					// shared dependency is expanded (and solved) before the
					// first dependent that needs it.
					work_list.push(WorkItem::Solve(coeff));
					for op in coeff.candidate_operations() {
						let (first, second) = op.dependencies();
						for dep in [Some(first), second].into_iter().flatten() {
							if dep != ScmCoeff::INPUT {
								work_list.push(WorkItem::Discover(dep));
							}
						}
					}
				}
				WorkItem::Solve(coeff) => {
					debug_assert!(!memo.contains_key(&coeff));
					let best = coeff
						.candidate_operations()
						.filter_map(|op| {
							let (first, second) = op.dependencies();

							// Collect each dependency's full intermediate set:
							// its own sub-intermediates plus the
							// dependency itself. A dependency is
							// absent from `memo` only if it sits on the current
							// path (a back-edge); dropping the candidate
							// then keeps the emitted operation graph
							// acyclic.
							let p1 = memo.get(&first)?;
							let i1 = intermediates_with(&p1.intermediates, first);

							// The plan cost is the sum of every unique
							// operation's cost.
							let op_cost = op.cost(objective);
							let mut cost = op_cost;
							let combined: Vec<ScmCoeff> = if let Some(second) = second {
								let p2 = memo.get(&second)?;
								let i2 = intermediates_with(&p2.intermediates, second);
								merge_coeffs(i1, i2)
									.inspect(|d| cost += memo[d].op_cost)
									.collect()
							} else {
								i1.inspect(|d| cost += memo[d].op_cost).collect()
							};

							Some(InternalPlan {
								cost,
								op_cost,
								operation: Some(op),
								intermediates: combined,
							})
						})
						.min();

					if let Some(plan) = best {
						let _ = memo.insert(coeff, plan);
					}
				}
			}
		}

		let final_plan = &memo[&odd_constant];

		// Post process: Extract operations in topological order.
		let mut operations = emit_operations(odd_constant, &memo);

		// Append the final shift if the original constant was even.
		if shift > 0 {
			operations.push(ScmOperation::ShiftLeft {
				source: odd_constant,
				shift,
			});
		}

		Self {
			constant: ScmCoeff::new(constant),
			objective,
			cost: final_plan.cost,
			operations,
		}
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZero;

	use rustc_hash::FxHashSet;

	use crate::helpers::scm::{ScmCoeff, ScmObjective, ScmOperation, ScmSolution};

	/// Even constants should be handled by solving the odd part and adding a
	/// trailing shift, rather than by rejecting the input.
	#[test]
	fn even_constants_append_a_final_shift() {
		let solution = ScmSolution::synthesize(6, min_adders(4));
		assert_eq!(solution.operations.len(), 2);
		assert!(matches!(
			solution.operations[1],
			ScmOperation::ShiftLeft { .. }
		));
	}

	/// The DP min-a encoder should reproduce the encoding quality reported in
	/// the paper. This covers every constant from Table 2 (8-bit input width)
	/// together with the large `171398451` instance from Section 4.3. For each
	/// constant the plan must evaluate to the exact product and use the same
	/// number of half/full adders (`cost`) as the paper's `DPmin-a` column.
	///
	/// Run with `--release --nocapture` to print the `(c, time, #adders)`
	/// comparison table.
	#[test]
	fn min_a_quality() {
		// (constant, paper DPmin-a half/full adder count for an 8-bit input).
		// The first ten rows are Table 2; the last is the Section 4.3 instance.
		let cases: [(u32, u32); 11] = [
			(464571, 43),
			(7137249, 44),
			(8176693, 57),
			(9330001, 60),
			(11895821, 58),
			(14049001, 51),
			(15055315, 51),
			(16532753, 56),
			(27587603, 62),
			(30261031, 60),
			(171398451, 68),
		];

		println!("{:>10} {:>10} {:>6}", "c", "time(s)", "#adders");
		for (c, paper_adders) in cases {
			let start = std::time::Instant::now();
			let solution = ScmSolution::synthesize(c, min_adders(8));
			let elapsed = start.elapsed();

			for x in [-31_i64, -1, 0, 1, 123, 200] {
				assert_eq!(solution.evaluate(x), c as i128 * x as i128, "c={c} x={x}");
			}
			assert_eq!(
				solution.cost, paper_adders,
				"adder count for {c} regressed from the paper's DPmin-a result"
			);
			println!(
				"{c:>10} {:>10.3?} {:>6}",
				elapsed.as_secs_f64(),
				solution.cost,
			);
		}
	}

	/// Build a min-a objective (minimize half/full adders) for a `bits`-wide
	/// input.
	fn min_adders(bits: u32) -> ScmObjective {
		ScmObjective::MinAdders(NonZero::new(bits).expect("input width must be non-zero"))
	}

	/// The DP min-k encoder (minimize the number of additions) should stay
	/// within one operation of the paper's DPmin-k results across Table 1 and
	/// the Section 4.3 instance. Unlike min-a, the coefficient-keyed `min`
	/// model does not reproduce these exactly (the paper tables all equal-cost
	/// plans), but it stays near-optimal. The cost must also equal the number
	/// of non-shift operations, which is the definition of the min-k
	/// objective.
	///
	/// Run with `--release --nocapture` to print the `(c, time, #adds)` table.
	#[test]
	fn min_k_quality() {
		// (constant, paper DPmin-k operation count). The first ten rows are
		// Table 1; the last is the Section 4.3 instance.
		let cases: [(u32, u32); 11] = [
			(464571, 6),
			(7137249, 5),
			(8176693, 6),
			(9330001, 6),
			(11895821, 6),
			(14049001, 6),
			(15055315, 6),
			(16532753, 5),
			(27587603, 6),
			(30261031, 5),
			(171398451, 7),
		];

		println!("{:>10} {:>10} {:>6} {:>6}", "c", "time(s)", "#adds", "diff");
		for (c, paper_adds) in cases {
			let start = std::time::Instant::now();
			let solution = ScmSolution::synthesize(c, ScmObjective::MinAddition);
			let elapsed = start.elapsed();

			for x in [-31_i64, -1, 0, 1, 123, 200] {
				assert_eq!(solution.evaluate(x), c as i128 * x as i128, "c={c} x={x}");
			}
			// The min-k cost is by definition the number of non-shift
			// operations.
			let ops = solution
				.operations
				.iter()
				.filter(|op| !matches!(op, ScmOperation::ShiftLeft { .. }))
				.count() as u32;
			assert_eq!(
				solution.cost, ops,
				"min-k cost should equal the operation count for {c}"
			);
			assert!(
				solution.cost <= paper_adds + 1,
				"min-k for {c} is {} ops, more than one worse than the paper's {paper_adds}",
				solution.cost
			);
			println!(
				"{c:>10} {:>10.3?} {:>6} {:>6}",
				elapsed.as_secs_f64(),
				solution.cost,
				match solution.cost as i64 - paper_adds as i64 {
					x if x > 0 => format!("+{}", x),
					0 => String::new(),
					x => x.to_string(),
				}
			);
		}
	}

	/// A power-of-two constant has an odd part of 1, so its plan is a single
	/// free shift of the input and costs nothing under either objective.
	#[test]
	fn power_of_two_is_a_single_shift() {
		for objective in [ScmObjective::MinAddition, min_adders(8)] {
			let solution = ScmSolution::synthesize(8, objective);
			assert_eq!(solution.cost, 0);
			assert_eq!(
				solution.operations,
				vec![ScmOperation::ShiftLeft {
					source: ScmCoeff::INPUT,
					shift: 3,
				}]
			);
			for x in [-9_i64, 0, 1, 7, 50] {
				assert_eq!(solution.evaluate(x), 8_i128 * x as i128);
			}
		}
	}

	/// The emitted schedule should be directly executable without an extra
	/// topological sort by the caller.
	#[test]
	fn produce_topologically_sorted_plan() {
		for c in [45, 464571, 14049001, 171398451] {
			let solution = ScmSolution::synthesize(c, min_adders(4));
			let mut seen = FxHashSet::default();
			let _ = seen.insert(ScmCoeff::INPUT);
			for op in solution.operations {
				let (first, second) = op.dependencies();
				assert!(seen.contains(&first));
				if let Some(second) = second {
					assert!(seen.contains(&second));
				}
				let _ = seen.insert(op.result());
			}
		}
	}

	/// The MINUSS rule (`C = C1 - (C2 << S)`, with minuend `C1 > C`) must be
	/// reachable by the planner. 569 is the smallest odd constant whose best
	/// 8-bit plan uses a subtraction-from-a-larger-multiple, so its plan must
	/// contain a [`ScmOperation::SubShift`]. Without MINUSS the planner cannot
	/// emit this operation at all.
	#[test]
	fn use_minuss() {
		let solution = ScmSolution::synthesize(569, min_adders(8));
		assert!(
			solution
				.operations
				.iter()
				.any(|op| matches!(op, ScmOperation::SubShift { .. })),
			"expected the plan for 569 to use a MINUSS (SubShift) operation, got {:?}",
			solution.operations
		);
		for x in [-9_i64, 0, 1, 7, 50] {
			assert_eq!(solution.evaluate(x), 569_i128 * x as i128);
		}
	}

	/// The SMINUS rule (`C = (C1 << S) - C2`) captures near-powers-of-two. 15
	/// (binary 1111) is `(1 << 4) - 1`, so its plan must contain a
	/// [`ScmOperation::ShiftSub`] operation.
	#[test]
	fn use_sminus() {
		let solution = ScmSolution::synthesize(15, min_adders(8));
		assert!(
			solution
				.operations
				.iter()
				.any(|op| matches!(op, ScmOperation::ShiftSub { .. })),
			"expected the plan for 15 to use a SMINUS (ShiftSub) operation, got {:?}",
			solution.operations
		);
		for x in [-9_i64, 0, 1, 7, 50] {
			assert_eq!(solution.evaluate(x), 15_i128 * x as i128);
		}
	}

	/// The SPLUS rule (`C = (C1 << S) + C2`) is the additive decomposition. 11
	/// (binary 1011) is built from two shift-and-add steps, so its plan must
	/// contain [`ScmOperation::ShiftAdd`] operations.
	#[test]
	fn use_splus() {
		let solution = ScmSolution::synthesize(11, min_adders(8));
		assert!(
			solution
				.operations
				.iter()
				.any(|op| matches!(op, ScmOperation::ShiftAdd { .. })),
			"expected the plan for 11 to use a SPLUS (ShiftAdd) operation, got {:?}",
			solution.operations
		);
		for x in [-9_i64, 0, 1, 7, 50] {
			assert_eq!(solution.evaluate(x), 11_i128 * x as i128);
		}
	}

	/// Verify that the total cost is indeed the sum of unique operation costs.
	#[test]
	fn verify_cost_deduplication() {
		for c in [45, 464571, 14049001, 171398451] {
			let solution = ScmSolution::synthesize(c, min_adders(8));
			let mut manual_cost = 0;
			let mut seen_results = FxHashSet::default();
			for op in &solution.operations {
				if !seen_results.contains(&op.result()) {
					manual_cost += op.cost(solution.objective);
					let _ = seen_results.insert(op.result());
				}
			}
			assert_eq!(solution.cost, manual_cost);
		}
	}

	/// Multiplying by zero needs no operations under either objective.
	#[test]
	fn zero_constant_produces_empty_plan() {
		for objective in [ScmObjective::MinAddition, min_adders(8)] {
			let solution = ScmSolution::synthesize(0, objective);
			assert_eq!(solution.cost, 0);
			assert!(solution.operations.is_empty());
		}
	}
}
