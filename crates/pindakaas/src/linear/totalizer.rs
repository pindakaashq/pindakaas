use crate::Literal;
use std::collections::{HashMap, HashSet};
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
		dbg!(&xs);

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		let mut model = build_totalizer(xs, &lin.cmp, *lin.k);
		model.encode(db)?;
		Ok(())

		/*
		model
			.cons
			.iter()
			.map(|Lin { xs, cmp, k }| match children {
				[x] => x.clone(),
				[left, right] => {
					// TODO re-establish binary heurstic
					let parent = if dom.len() == 1 {
						IntVarEnc::Const(dom.into_iter().next().unwrap())
					} else {
						IntVarEnc::Ord(IntVarOrd::from_dom(
							db,
							dom.into_iter().sorted().collect::<Vec<_>>().as_slice(),
							format!("gt_{}_{}", level + 1, node + 1),
						))
					};

					TernLeEncoder::default()
						.encode(
							db,
							&TernLeConstraint::new(&left, &right, cmp.clone(), &parent),
						)
						.unwrap();
					parent
				}
				_ => unreachable!(),
			})
			.collect::<Vec<_>>();
			*/

		//Ok(())
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
		if self.dom.len() == 1 {
			IntVarEnc::Const(self.dom.iter().next().unwrap().clone())
		} else {
			IntVarEnc::Ord(IntVarOrd::from_dom(
				db,
				self.dom
					.iter()
					.sorted()
					.cloned()
					.collect::<Vec<_>>()
					.as_slice(),
				format!("gt"),
			))
		}
	}
}

#[derive(Debug)]
struct Lin<C: Coefficient> {
	xs: Vec<Rc<IntVar<C>>>,
	cmp: LimitComp,
	k: C,
}

#[derive(Debug)]
struct Model<Lit: Literal, C: Coefficient> {
	vars: HashMap<Rc<IntVar<C>>, IntVarEnc<Lit, C>>,
	cons: Vec<Lin<C>>,
}

impl<Lit: Literal, C: Coefficient> Model<Lit, C> {
	/*
	fn var_enc<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
		x: Rc<IntVar<C>>,
	) -> &IntVarEnc<DB::Lit, C> {
		self.vars.entry(x).or_insert_with(|| {})
	}
	*/

	/*
	fn encode_vars<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		enc: Vec<IntVarEnc<Lit, C>>,
	) -> HashMap<&IntVar<C>, IntVarEnc<Lit, C>> {
		dbg!(&enc);
		self.vars
			.iter()
			.zip_longest(enc)
			.map(|x_enc| match x_enc {
				EitherOrBoth::Both(x, enc) => (x, enc),
				EitherOrBoth::Left(x) => {
					let enc = if x.dom.len() == 1 {
						IntVarEnc::Const(x.dom.iter().next().unwrap().clone())
					} else {
						IntVarEnc::Ord(IntVarOrd::from_dom(
							db,
							x.dom
								.iter()
								.sorted()
								.cloned()
								.collect::<Vec<_>>()
								.as_slice(),
							format!("gt"),
						))
					};
					(x, enc)
				}
				EitherOrBoth::Right(_) => unreachable!(),
			})
			.collect::<HashMap<_, _>>()
	}
	*/

	fn encode<DB: ClauseDatabase<Lit = Lit>>(&mut self, db: &mut DB) -> Result {
		//let encs = self.encode_vars(db, encs);

		for con in &self.cons {
			let Lin { xs, cmp, k: _ } = con;
			assert!(con.xs.len() == 3);

			for x in xs {
				if !self.vars.contains_key(x) {
					self.vars.insert(x.clone(), x.encode(db));
				}
			}
			//     self.var_enc(db, x.clone()).clone())

			let (x, y, z) = (&self.vars[&xs[0]], &self.vars[&xs[1]], &self.vars[&xs[2]]);

			TernLeEncoder::default()
				.encode(
					db,
					//&TernLeConstraint::new(&v[xs[0].as_ref()], v[xs[1]], cmp.clone(), v[xs[2]]),
					&TernLeConstraint::new(&x, &y, cmp.clone(), &z),
				)
				.unwrap();
		}

		dbg!(&self);

		Ok(())
	}
}

fn build_totalizer<Lit: Literal, C: Coefficient>(
	xs: Vec<IntVarEnc<Lit, C>>,
	cmp: &LimitComp,
	k: C,
) -> Model<Lit, C> {
	let mut model = Model {
		vars: xs
			.into_iter()
			.enumerate()
			.map(|(id, x)| {
				let var = IntVar {
					id,
					dom: x.dom().iter(..).map(|d| d.end - C::one()).collect(),
				};
				(Rc::new(var), x)
			})
			.collect(),
		cons: vec![],
	};

	let mut layer = model
		.vars
		.iter()
		.map(|(l, _)| l.clone())
		.collect::<Vec<_>>();

	dbg!(&layer);
	while layer.len() > 1 {
		let mut next_layer = Vec::<Rc<IntVar<C>>>::new();
		for children in layer.chunks(2) {
			match &children[..] {
				[x] => {
					next_layer.push(x.clone());
				}
				[left, right] => {
					let parent = Rc::new(IntVar {
						id: model.vars.len(),
						dom: if layer.len() == 2 {
							vec![k]
						} else {
							left.dom
								.iter()
								.cartesian_product(right.dom.iter())
								.map(|(&a, &b)| a + b)
								.filter(|x| x <= &k)
								.sorted()
								.dedup()
								.collect()
						},
					});
					model.cons.push(Lin {
						xs: vec![left.clone(), right.clone(), parent.clone()],
						cmp: cmp.clone(),
						k: C::zero(),
					});
					next_layer.push(parent);
				}
				_ => panic!(),
			}
		}
		layer = next_layer;
	}

	model

	/*
			let (children, doms): (Vec<_>, Vec<_>) = next_layer.into_iter().unzip();
			let doms = propagate_layer_bounds(doms, cmp, root.ub());
			dbg!(&doms);
			let next_layer = children
				.into_iter()
				.zip(doms.into_iter())
				.enumerate()
				.map(|(node, (children, dom))| match children {
					[x] => x.clone(),
					[left, right] => {
						// TODO re-establish binary heurstic
						let parent = if dom.len() == 1 {
							IntVarEnc::Const(dom.into_iter().next().unwrap())
						} else {
							IntVarEnc::Ord(IntVarOrd::from_dom(
								db,
								dom.into_iter().sorted().collect::<Vec<_>>().as_slice(),
								format!("gt_{}_{}", level + 1, node + 1),
							))
						};

						TernLeEncoder::default()
							.encode(
								db,
								&TernLeConstraint::new(&left, &right, cmp.clone(), &parent),
							)
							.unwrap();
						parent
					}
					_ => unreachable!(),
				})
				.collect::<Vec<_>>();

			build_totalizer(next_layer, db, cmp, level + 1)
		}
	*/
}

//add_consistency,
//cutoff,
//root,

fn propagate_layer_bounds<C: Coefficient>(
	doms: Vec<HashSet<C>>,
	cmp: &LimitComp,
	k: C,
) -> Vec<HashSet<C>> {
	let cnt = doms.iter().map(HashSet::len).sum::<usize>();

	let doms = if cmp == &LimitComp::Equal {
		let layer_ub = doms
			.iter()
			.map(|x| x.iter().max().unwrap())
			.fold(C::zero(), |a, &b| a + b);

		doms.into_iter()
			.map(|dom| {
				let dom_ub = dom.iter().max().unwrap().clone();
				dom.into_iter()
					.filter(|d| *d + layer_ub - dom_ub >= k)
					.collect::<HashSet<_>>()
			})
			.collect::<Vec<_>>()
	} else {
		doms
	};

	let layer_lb = doms
		.iter()
		.map(|x| x.iter().min().unwrap())
		.fold(C::zero(), |a, &b| a + b);

	let doms = doms
		.into_iter()
		.map(|dom| {
			let dom_lb = *dom.iter().min().unwrap();
			dom.into_iter()
				.filter(|d| *d + layer_lb - dom_lb <= k)
				.collect()
		})
		.collect::<Vec<_>>();

	let new_cnt = doms.iter().map(HashSet::len).sum();
	if cnt == new_cnt {
		doms
	} else {
		propagate_layer_bounds(doms, cmp, k)
	}
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
