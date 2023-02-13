use crate::Literal;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use itertools::Itertools;

use crate::{
	int::{IntVarEnc, IntVarOrd, TernLeConstraint, TernLeEncoder},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, Result,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized Totalizer (GT)
#[derive(Clone, Default)]
pub struct TotalizerEncoder<C: Coefficient> {
	add_consistency: bool,
	cutoff: Option<C>,
}

impl<C: Coefficient> TotalizerEncoder<C> {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_cutoff(&mut self, c: Option<C>) -> &mut Self {
		self.cutoff = c;
		self
	}
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for TotalizerEncoder<C> {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "totalizer_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone(), format!("x_{i}")).into()
			})
			.collect::<Vec<IntVarEnc<DB::Lit, C>>>();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		let mut model = build_totalizer(xs, &lin.cmp, *lin.k);

		let mut size = model.size();

		loop {
			for con in &mut model.cons {
				con.propagate_bounds();
			}
			let new_size = model.size();
			if size == new_size {
				break;
			} else {
				size = new_size;
			}
		}

		model.encode(db)
	}
}

// TODO perhaps id can be used by replacing vars HashMap to just vec
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct IntVar<C: Coefficient> {
	id: usize,
	dom: Vec<C>,
}

impl<C: Coefficient> IntVar<C> {
	fn encode<DB: ClauseDatabase>(&self, db: &mut DB) -> IntVarEnc<DB::Lit, C> {
		if self.size() == 1 {
			IntVarEnc::Const(*self.dom.first().unwrap())
		} else {
			IntVarEnc::Ord(IntVarOrd::from_dom(
				db,
				self.dom
					.iter()
					.sorted()
					.cloned()
					.collect::<Vec<_>>()
					.as_slice(),
				"gt".to_string(),
			))
		}
	}

	fn size(&self) -> usize {
		self.dom.len()
	}

	fn lb(&self, c: &C) -> C {
		*c * if c.is_negative() {
			self.dom[self.dom.len() - 1]
		} else {
			self.dom[0]
		}
	}

	fn ub(&self, c: &C) -> C {
		*c * if c.is_negative() {
			self.dom[0]
		} else {
			self.dom[self.dom.len() - 1]
		}
	}
}

#[derive(Debug)]
struct Lin<C: Coefficient> {
	xs: Vec<(C, Rc<RefCell<IntVar<C>>>)>,
	cmp: LimitComp,
}

impl<C: Coefficient> Lin<C> {
	fn lb(&self) -> C {
		self.xs
			.iter()
			.map(|(c, x)| x.borrow().lb(c))
			.fold(C::zero(), |a, b| a + b)
	}
	fn ub(&self) -> C {
		self.xs
			.iter()
			.map(|(c, x)| x.borrow().ub(c))
			.fold(C::zero(), |a, b| a + b)
	}

	fn propagate_bounds(&mut self) {
		loop {
			let mut fixpoint = true;
			if self.cmp == LimitComp::Equal {
				let xs_ub = self.ub();
				for (c, x) in &self.xs {
					let x_ub = x.borrow().ub(c);
					x.borrow_mut().dom.retain(|d| {
						if *c * *d + xs_ub - x_ub >= C::zero() {
							true
						} else {
							fixpoint = false;
							false
						}
					});
				}
			}

			let xs_lb = self.lb();
			for (c, x) in &self.xs {
				let x_lb = x.borrow().lb(c);
				x.borrow_mut().dom.retain(|d| {
					if *c * *d + xs_lb - x_lb <= C::zero() {
						true
					} else {
						fixpoint = false;
						false
					}
				});
				assert!(x.borrow().size() > 0);
			}

			if fixpoint {
				return;
			}
		}
	}
}

#[derive(Debug)]
struct Model<Lit: Literal, C: Coefficient> {
	vars: HashMap<usize, IntVarEnc<Lit, C>>,
	cons: Vec<Lin<C>>,
	var_ids: usize,
}

impl<Lit: Literal, C: Coefficient> Model<Lit, C> {
	fn new() -> Self {
		Self {
			vars: HashMap::new(),
			cons: vec![],
			var_ids: 0,
		}
	}

	fn new_var(&mut self, dom: Vec<C>) -> IntVar<C> {
		self.var_ids += 1;
		IntVar {
			id: self.var_ids,
			dom,
		}
	}

	fn size(&self) -> usize {
		self.cons
			.iter()
			.map(|con| con.xs.iter().map(|(_, x)| x.borrow().size()).sum::<usize>())
			.sum()
	}

	fn encode<DB: ClauseDatabase<Lit = Lit>>(&mut self, db: &mut DB) -> Result {
		for con in &self.cons {
			let Lin { xs, cmp } = con;
			assert!(
				con.xs.len() == 3
					&& con.xs.iter().map(|(c, _)| c).collect::<Vec<_>>()
						== [&C::one(), &C::one(), &-C::one()]
			);

			for (_, x) in xs {
				self.vars.entry(x.borrow().id).or_insert_with(|| {
					let enc = x.borrow().encode(db);
					enc
				});
			}

			let (x, y, z) = (
				&self.vars[&xs[0].1.borrow().id],
				&self.vars[&xs[1].1.borrow().id],
				&self.vars[&xs[2].1.borrow().id],
			);

			TernLeEncoder::default()
				.encode(db, &TernLeConstraint::new(x, y, cmp.clone(), z))
				.unwrap();
		}

		Ok(())
	}
}

fn build_totalizer<Lit: Literal, C: Coefficient>(
	xs: Vec<IntVarEnc<Lit, C>>,
	cmp: &LimitComp,
	k: C,
) -> Model<Lit, C> {
	let mut model = Model::new();
	let mut layer = xs
		.into_iter()
		.map(|x| {
			let var = model.new_var(x.dom().iter(..).map(|d| d.end - C::one()).collect());
			model.vars.insert(var.id, x);
			Rc::new(RefCell::new(var))
		})
		.collect::<Vec<_>>();

	while layer.len() > 1 {
		let mut next_layer = Vec::<Rc<RefCell<IntVar<C>>>>::new();
		for children in layer.chunks(2) {
			match children {
				[x] => {
					next_layer.push(x.clone());
				}
				[left, right] => {
					let dom = if layer.len() == 2 {
						vec![k]
					} else {
						left.borrow()
							.dom
							.iter()
							.cartesian_product(right.borrow().dom.iter())
							.map(|(&a, &b)| a + b)
							.sorted()
							.dedup()
							.collect()
					};
					let parent = Rc::new(RefCell::new(model.new_var(dom)));

					model.cons.push(Lin {
						xs: vec![
							(C::one(), left.clone()),
							(C::one(), right.clone()),
							(-C::one(), parent.clone()),
						],
						cmp: cmp.clone(),
					});
					next_layer.push(parent);
				}
				_ => panic!(),
			}
		}
		layer = next_layer;
	}

	model
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		// cardinality_one::tests::card1_test_suite, CardinalityOne,
		helpers::tests::{assert_sol, TestDB},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Comparator,
		Encoder,
		LinExp,
		LinearAggregator,
		LinearConstraint,
		SortedEncoder,
	};

	#[test]
	fn test_sort_same_coefficients_2() {
		use crate::linear::{LinearEncoder, StaticLinEncoder};
		use crate::{Checker, Encoder};
		let mut db = TestDB::new(5);
		let mut agg = LinearAggregator::default();
		agg.sort_same_coefficients(SortedEncoder::default(), 3);
		let mut encoder = LinearEncoder::<StaticLinEncoder<TotalizerEncoder<i32>>>::default();
		encoder.add_linear_aggregater(agg);
		let con = LinearConstraint::new(
			LinExp::new() + (1, 3) + (2, 3) + (3, 1) + (4, 1) + (5, 3),
			Comparator::GreaterEq,
			2,
		);
		assert!(encoder.encode(&mut db, &con).is_ok());
		db.with_check(|sol| {
			{
				let con = LinearConstraint::new(
					LinExp::new() + (1, 3) + (2, 3) + (3, 1) + (4, 1) + (5, 3),
					Comparator::GreaterEq,
					2,
				);
				con.check(sol)
			}
			.is_ok()
		})
		.check_complete()
	}

	linear_test_suite!(TotalizerEncoder::default());
	// FIXME: Totalizer does not support LimitComp::Equal
	// card1_test_suite!(TotalizerEncoder::default());
}
