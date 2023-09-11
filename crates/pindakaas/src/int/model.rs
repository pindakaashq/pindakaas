use crate::{Encoder, Unsatisfiable};
use itertools::Itertools;
use std::{
	cell::RefCell,
	collections::{BTreeSet, HashMap},
	fmt::{self, Display},
	rc::Rc,
};

use iset::IntervalMap;

use crate::{
	int::{TernLeConstraint, TernLeEncoder},
	ClauseDatabase, Coefficient, LimitComp, Literal,
};

use super::{display_dom, enc::GROUND_BINARY_AT_LB, IntVarBin, IntVarEnc, IntVarOrd};

// TODO should we keep IntVar i/o IntVarEnc?
#[derive(Debug)]
pub struct Model<Lit: Literal, C: Coefficient> {
	vars: HashMap<usize, IntVarEnc<Lit, C>>,
	cons: Vec<Lin<C>>,
	num_var: usize,
}

// TODO Domain will be used once (/if) this is added as encoder feature.
#[allow(dead_code)]
#[derive(Default, Clone, PartialEq)]
pub enum Consistency {
	None,
	#[default]
	Bounds,
	Domain,
}

impl<Lit: Literal, C: Coefficient> Display for Model<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for con in &self.cons {
			writeln!(f, "{}", con)?;
		}
		Ok(())
	}
}

impl<C: Coefficient> Display for Lin<C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let disp_x = |x: &(C, Rc<RefCell<IntVar<C>>>)| -> String {
			let (coef, x) = x;
			assert!(coef.abs() == C::one());
			let x = x.borrow();

			format!("{}", x)
		};
		write!(
			f,
			"{} {} {}",
			self.xs.iter().map(disp_x).join(" + "),
			self.cmp,
			self.k,
			// disp_x(&(C::one(), self.k()))
		)?;
		Ok(())
	}
}

impl<C: Coefficient> fmt::Display for IntVar<C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "x{} ∈ {}", self.id, display_dom(&self.dom))
	}
}

impl<Lit: Literal, C: Coefficient> Default for Model<Lit, C> {
	fn default() -> Self {
		Self {
			vars: HashMap::new(),
			cons: vec![],
			num_var: 0,
		}
	}
}

impl<Lit: Literal, C: Coefficient> Model<Lit, C> {
	pub(crate) fn add_int_var_enc(&mut self, x: IntVarEnc<Lit, C>) -> Rc<RefCell<IntVar<C>>> {
		let var = self.new_var(x.dom().iter(..).map(|d| d.end - C::one()).collect(), false);
		self.vars.insert(var.borrow().id, x);
		var
	}

	pub fn new_var(&mut self, dom: BTreeSet<C>, add_consistency: bool) -> Rc<RefCell<IntVar<C>>> {
		self.num_var += 1;
		Rc::new(RefCell::new(IntVar {
			id: self.num_var,
			dom,
			add_consistency,
			views: HashMap::default(),
		}))
	}

	pub fn add_constraint(&mut self, constraint: Lin<C>) -> crate::Result {
		self.cons.push(constraint);
		Ok(())
	}

	pub fn new_constant(&mut self, c: C) -> Rc<RefCell<IntVar<C>>> {
		self.new_var(BTreeSet::from([c]), false)
	}

	pub fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
		cutoff: Option<C>,
	) -> crate::Result {
		// TODO decompose + aggregate constants + encode trivial constraints
		let mut all_views = HashMap::new();

		self.cons = self
			.cons
			.iter()
			.cloned()
			.map(|lin| -> Result<Vec<_>, Unsatisfiable> {
				match &lin.xs[..] {
					[] => Ok(vec![]),
					[(_, x)] => {
						match lin.cmp {
							LimitComp::Equal => {
								x.borrow_mut().fix(&C::zero())?;
							}
							LimitComp::LessEq => {
								x.borrow_mut().le(&C::zero());
							}
						};
						Ok(vec![])
					}
					[x, y] => Ok(vec![Lin::new(&[x.clone(), y.clone()], lin.cmp, C::zero())]),
					[_, _, _] => Ok(vec![lin]),
					_xs => {
						// BddEncoder::default().decompose(lin, self)
						todo!()
					}
				}
			})
			.flatten_ok()
			.flatten()
			.collect();

		for con in &self.cons {
			let Lin { xs, cmp, k: _ } = con;
			assert!(
				con.xs.len() == 3
					&& con.xs.iter().map(|(c, _)| c).collect::<Vec<_>>()
						== [&C::one(), &C::one(), &-C::one()]
			);

			for (_, x) in xs {
				let x = x.borrow();
				self.vars
					.entry(x.id)
					.or_insert_with(|| x.encode(db, &mut all_views, x.prefer_order(cutoff)));
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

	pub(crate) fn propagate(&mut self, consistency: &Consistency) {
		// TODO for Gt/Bdd we actually know we can start propagation at the last constraint
		let mut queue = BTreeSet::from_iter(0..self.cons.len());
		if consistency == &Consistency::None {
			return;
		}
		while let Some(con) = queue.pop_last() {
			let changed = self.cons[con].propagate(consistency);
			queue.extend(self.cons.iter().enumerate().filter_map(|(i, con)| {
				con.xs
					.iter()
					.any(|(_, x)| changed.contains(&x.borrow().id))
					.then_some(i)
			}));
		}
	}
}

// TODO LimitComp -> Comp
#[derive(Debug, Clone)]
pub struct Lin<C: Coefficient> {
	pub xs: Vec<(C, Rc<RefCell<IntVar<C>>>)>,
	pub cmp: LimitComp,
	pub k: C,
}

impl<C: Coefficient> Lin<C> {
	pub fn new(terms: &[(C, Rc<RefCell<IntVar<C>>>)], cmp: LimitComp, k: C) -> Self {
		Lin {
			xs: terms.to_vec(),
			cmp,
			k,
		}
	}

	pub fn tern(
		x: Rc<RefCell<IntVar<C>>>,
		y: Rc<RefCell<IntVar<C>>>,
		cmp: LimitComp,
		z: Rc<RefCell<IntVar<C>>>,
	) -> Self {
		Lin {
			xs: vec![(C::one(), x), (C::one(), y), (-C::one(), z)],
			cmp,
			k: C::zero(),
		}
	}

	pub fn vars(&self) -> Vec<Rc<RefCell<IntVar<C>>>> {
		self.xs
			.iter()
			.cloned()
			.map(|(_, x)| x)
			// .filter(|x| !x.borrow().is_const())
			.collect::<_>()
	}

	pub fn decompose<Lit: Literal>(mut self) -> Vec<Lin<C>> {
		match &mut self.xs[..] {
			[] => vec![],
			[(_, x)] => {
				match self.cmp {
					LimitComp::Equal => {
						x.borrow_mut().fix(&C::zero()).unwrap();
					}
					LimitComp::LessEq => {
						x.borrow_mut().le(&C::zero());
					}
				};
				vec![]
			}
			[x, y] => {
				vec![Lin::new(&[x.clone(), y.clone()], self.cmp, C::zero())]
			}
			_ => todo!(),
		}
	}

	pub fn lb(&self) -> C {
		self.xs
			.iter()
			.map(|(c, x)| x.borrow().lb(c))
			.fold(C::zero(), |a, b| a + b)
	}

	pub fn ub(&self) -> C {
		self.xs
			.iter()
			.map(|(c, x)| x.borrow().ub(c))
			.fold(C::zero(), |a, b| a + b)
	}

	pub(crate) fn propagate(&mut self, consistency: &Consistency) -> Vec<usize> {
		let mut changed = vec![];
		match consistency {
			Consistency::None => unreachable!(),
			Consistency::Bounds => loop {
				let mut fixpoint = true;
				if self.cmp == LimitComp::Equal {
					for (c, x) in &self.xs {
						let xs_ub = self.ub();
						let mut x = x.borrow_mut();
						let size = x.size();

						let id = x.id;
						let x_ub = if c.is_positive() {
							*x.dom.last().unwrap()
						} else {
							*x.dom.first().unwrap()
						};

						// c*d >= x_ub*c + xs_ub := d >= x_ub - xs_ub/c
						let b = x_ub - (xs_ub / *c);

						if !c.is_negative() {
							x.ge(&b);
						} else {
							x.le(&b);
						}

						if x.size() < size {
							changed.push(id);
							fixpoint = false;
						}
						assert!(x.size() > 0);
					}
				}

				let rs_lb = self.lb();
				for (c, x) in &self.xs {
					let mut x = x.borrow_mut();
					let size = x.size();
					let x_lb = if c.is_positive() {
						*x.dom.first().unwrap()
					} else {
						*x.dom.last().unwrap()
					};

					let id = x.id;

					// c*d <= c*x_lb - rs_lb
					// d <= x_lb - (rs_lb / c) (or d >= .. if d<0)
					let b = x_lb - (rs_lb / *c);

					if c.is_negative() {
						x.ge(&b);
					} else {
						x.le(&b);
					}

					if x.size() < size {
						//println!("Pruned {}", size - x.size());
						changed.push(id);
						fixpoint = false;
					}
					assert!(x.size() > 0);
				}

				if fixpoint {
					return changed;
				}
			},
			Consistency::Domain => {
				assert!(self.cmp == LimitComp::Equal);
				loop {
					let mut fixpoint = true;
					for (i, (c_i, x_i)) in self.xs.iter().enumerate() {
						let id = x_i.borrow().id;
						x_i.borrow_mut().dom.retain(|d_i| {
							if self
								.xs
								.iter()
								.enumerate()
								.filter_map(|(j, (c_j, x_j))| {
									(i != j).then(|| {
										x_j.borrow()
											.dom
											.iter()
											.map(|d_j_k| *c_j * *d_j_k)
											.collect::<Vec<_>>()
									})
								})
								.multi_cartesian_product()
								.any(|rs| {
									*c_i * *d_i + rs.into_iter().fold(C::zero(), |a, b| a + b)
										== C::zero()
								}) {
								true
							} else {
								fixpoint = false;
								changed.push(id);
								false
							}
						});
						assert!(x_i.borrow().size() > 0);
					}

					if fixpoint {
						return changed;
					}
				}
			}
		}
	}
}

// TODO perhaps id can be used by replacing vars HashMap to just vec
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntVar<C: Coefficient> {
	pub(crate) id: usize,
	pub(crate) dom: BTreeSet<C>,
	add_consistency: bool,
	pub(crate) views: HashMap<C, (usize, C)>,
}

impl<C: Coefficient> IntVar<C> {
	fn encode<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		views: &mut HashMap<(usize, C), DB::Lit>,
		prefer_order: bool,
	) -> IntVarEnc<DB::Lit, C> {
		if self.size() == 1 {
			IntVarEnc::Const(*self.dom.first().unwrap())
		} else {
			let x = if prefer_order {
				let dom = self
					.dom
					.iter()
					.sorted()
					.cloned()
					.tuple_windows()
					.map(|(a, b)| (a + C::one())..(b + C::one()))
					.map(|v| (v.clone(), views.get(&(self.id, v.end - C::one())).cloned()))
					.collect::<IntervalMap<_, _>>();
				IntVarEnc::Ord(IntVarOrd::from_views(db, dom, "x".to_string()))
			} else {
				let y = IntVarBin::from_bounds(
					db,
					*self.dom.first().unwrap(),
					*self.dom.last().unwrap(),
					"x".to_string(),
				);
				IntVarEnc::Bin(y)
			};

			if self.add_consistency {
				x.consistent(db).unwrap();
			}

			for view in self
				.views
				.iter()
				.map(|(c, (id, val))| ((*id, *val), x.geq(*c..(*c + C::one()))))
			{
				// TODO refactor
				if !view.1.is_empty() {
					views.insert(view.0, view.1[0][0].clone());
				}
			}
			x
		}
	}

	pub(crate) fn dom(&self) -> std::collections::btree_set::Iter<C> {
		self.dom.iter()
	}

	// TODO should not be C i/o &C?
	fn fix(&mut self, q: &C) -> crate::Result {
		if self.dom.contains(q) {
			self.dom = [*q].into();
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}

	fn ge(&mut self, bound: &C) {
		self.dom = self.dom.split_off(bound);
	}

	fn le(&mut self, bound: &C) {
		self.dom.split_off(&(*bound + C::one()));
	}

	pub(crate) fn size(&self) -> usize {
		self.dom.len()
	}

	pub(crate) fn lb(&self, c: &C) -> C {
		*c * *(if c.is_negative() {
			self.dom.last()
		} else {
			self.dom.first()
		})
		.unwrap()
	}

	pub(crate) fn ub(&self, c: &C) -> C {
		*c * *(if c.is_negative() {
			self.dom.first()
		} else {
			self.dom.last()
		})
		.unwrap()
	}

	pub fn required_bits(lb: C, ub: C) -> u32 {
		if GROUND_BINARY_AT_LB {
			C::zero().leading_zeros() - ((ub - lb).leading_zeros())
		} else {
			C::zero().leading_zeros() - (ub.leading_zeros())
		}
	}

	fn prefer_order(&self, cutoff: Option<C>) -> bool {
		match cutoff {
			None => true,
			Some(cutoff) if cutoff == C::zero() => false,
			Some(cutoff) => C::from(self.dom.len()).unwrap() < cutoff,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{Cnf, Lin, Model};

	#[test]
	fn model_test() {
		let mut model = Model::<i32, i32>::default();
		let x1 = model.new_var([0, 2].into(), true);
		let x2 = model.new_var([0, 3].into(), true);
		let x3 = model.new_var([0, 5].into(), true);
		let k = 6;
		model
			.add_constraint(Lin::new(&[(1, x1), (1, x2), (1, x3)], LimitComp::LessEq, k))
			.unwrap();
		let mut cnf = Cnf::new(0);
		model.propagate(&Consistency::Bounds);
		model.encode(&mut cnf, None).unwrap();
	}
}
