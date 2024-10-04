use std::{
	cell::RefCell,
	collections::{BTreeSet, HashMap},
	fmt::{self, Display},
	rc::Rc,
};

use iset::IntervalMap;
use itertools::Itertools;

use super::{display_dom, enc::GROUND_BINARY_AT_LB, IntVarBin, IntVarEnc, IntVarOrd};
use crate::{
	int::{TernLeConstraint, TernLeEncoder},
	ClauseDatabase, Coeff, Encoder, LimitComp, Lit,
};

#[derive(Debug, Default)]
pub(crate) struct Model {
	vars: HashMap<usize, IntVarEnc>,
	pub(crate) cons: Vec<Lin>,
	var_ids: usize,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Consistency {
	None,
	#[default]
	Bounds,
	Domain,
}

impl Display for Model {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for con in &self.cons {
			writeln!(f, "{}", con)?;
		}
		Ok(())
	}
}

impl Display for Lin {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let disp_x = |x: &(Coeff, Rc<RefCell<IntVar>>)| -> String {
			let (coef, x) = x;
			assert!(coef.abs() == 1);
			let x = x.borrow();

			format!("{}", x)
		};
		write!(
			f,
			"{} {} {}",
			self.xs[0..2].iter().map(disp_x).join(" + "),
			self.cmp,
			disp_x(&self.xs[2])
		)?;
		Ok(())
	}
}

impl Display for IntVar {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "x{} ∈ {}", self.id, display_dom(&self.dom))
	}
}

impl Model {
	pub(crate) fn add_int_var_enc(&mut self, x: IntVarEnc) -> IntVar {
		let var = self.new_var(x.dom().iter(..).map(|d| d.end - 1).collect(), false);
		let _ = self.vars.insert(var.id, x);
		var
	}

	pub(crate) fn new_var(&mut self, dom: BTreeSet<Coeff>, add_consistency: bool) -> IntVar {
		self.var_ids += 1;
		IntVar {
			id: self.var_ids,
			dom,
			add_consistency,
			views: HashMap::default(),
		}
	}

	pub(crate) fn new_constant(&mut self, c: Coeff) -> IntVar {
		self.new_var(BTreeSet::from([c]), false)
	}

	pub(crate) fn encode<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
		cutoff: Option<Coeff>,
	) -> crate::Result {
		let mut all_views = HashMap::new();
		for con in &self.cons {
			let Lin { xs, cmp } = con;
			assert!(
				con.xs.len() == 3 && con.xs.iter().map(|(c, _)| c).collect_vec() == [&1, &1, &-1]
			);

			for (_, x) in xs {
				let x = x.borrow();
				let _ = self
					.vars
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

	pub(crate) fn propagate(&mut self, consistency: &Consistency, mut queue: Vec<usize>) {
		if consistency == &Consistency::None {
			return;
		}
		while let Some(con) = queue.pop() {
			let changed = self.cons[con].propagate(consistency);
			let mut cons = self
				.cons
				.iter()
				.enumerate()
				.filter_map(|(i, con)| {
					con.xs
						.iter()
						.any(|(_, x)| changed.contains(&x.borrow().id))
						.then_some(i)
				})
				.collect_vec();
			queue.append(&mut cons);
		}
	}
}

#[derive(Debug)]
pub(crate) struct Lin {
	pub(crate) xs: Vec<(Coeff, Rc<RefCell<IntVar>>)>,
	pub(crate) cmp: LimitComp,
}

impl Lin {
	pub(crate) fn tern(
		x: Rc<RefCell<IntVar>>,
		y: Rc<RefCell<IntVar>>,
		cmp: LimitComp,
		z: Rc<RefCell<IntVar>>,
	) -> Self {
		Lin {
			xs: vec![(1, x), (1, y), (-1, z)],
			cmp,
		}
	}

	pub(crate) fn lb(&self) -> Coeff {
		self.xs.iter().map(|(c, x)| x.borrow().lb(c)).sum::<i64>()
	}

	pub(crate) fn ub(&self) -> Coeff {
		self.xs.iter().map(|(c, x)| x.borrow().ub(c)).sum::<i64>()
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
								.filter(|&(j, (_c_j, _x_j))| (i != j))
								.map(|(_j, (c_j, x_j))| {
									x_j.borrow()
										.dom
										.iter()
										.map(|d_j_k| *c_j * *d_j_k)
										.collect_vec()
								})
								.multi_cartesian_product()
								.any(|rs| *c_i * *d_i + rs.into_iter().sum::<i64>() == 0)
							{
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
pub(crate) struct IntVar {
	pub(crate) id: usize,
	pub(crate) dom: BTreeSet<Coeff>,
	add_consistency: bool,
	pub(crate) views: HashMap<Coeff, (usize, Coeff)>,
}

impl IntVar {
	fn encode<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		views: &mut HashMap<(usize, Coeff), Lit>,
		prefer_order: bool,
	) -> IntVarEnc {
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
					.map(|(a, b)| (a + 1)..(b + 1))
					.map(|v| (v.clone(), views.get(&(self.id, v.end - 1)).cloned()))
					.collect::<IntervalMap<_, _>>();
				IntVarEnc::Ord(IntVarOrd::from_views(db, dom, "x".to_owned()))
			} else {
				let y = IntVarBin::from_bounds(
					db,
					*self.dom.first().unwrap(),
					*self.dom.last().unwrap(),
					"x".to_owned(),
				);
				IntVarEnc::Bin(y)
			};

			if self.add_consistency {
				x.consistent(db).unwrap();
			}

			for view in self
				.views
				.iter()
				.map(|(c, (id, val))| ((*id, *val), x.geq(*c..(*c + 1))))
			{
				// TODO refactor
				if !view.1.is_empty() {
					let _ = views.insert(view.0, view.1[0][0]);
				}
			}
			x
		}
	}

	fn ge(&mut self, bound: &Coeff) {
		self.dom = self.dom.split_off(bound);
	}

	fn le(&mut self, bound: &Coeff) {
		let _ = self.dom.split_off(&(*bound + 1));
	}

	pub(crate) fn size(&self) -> usize {
		self.dom.len()
	}

	pub(crate) fn lb(&self, c: &Coeff) -> Coeff {
		*c * *(if c.is_negative() {
			self.dom.last()
		} else {
			self.dom.first()
		})
		.unwrap()
	}

	pub(crate) fn ub(&self, c: &Coeff) -> Coeff {
		*c * *(if c.is_negative() {
			self.dom.first()
		} else {
			self.dom.last()
		})
		.unwrap()
	}

	pub(crate) fn required_bits(lb: Coeff, ub: Coeff) -> u32 {
		const ZERO: Coeff = 0;
		if GROUND_BINARY_AT_LB {
			ZERO.leading_zeros() - ((ub - lb).leading_zeros())
		} else {
			ZERO.leading_zeros() - (ub.leading_zeros())
		}
	}

	fn prefer_order(&self, cutoff: Option<Coeff>) -> bool {
		match cutoff {
			None => true,
			Some(0) => false,
			Some(cutoff) => (self.dom.len() as Coeff) < cutoff,
		}
	}
}
