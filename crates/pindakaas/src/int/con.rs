#![allow(clippy::absurd_extreme_comparisons)]
use itertools::Itertools;

use super::{
	model::{PRINT_COUPLING, USE_COUPLING_IO_LEX, VIEW_COUPLING},
	IntVarEnc, IntVarId,
};
use crate::{
	helpers::{add_clauses_for, div_ceil, div_floor},
	int::{bin::BinEnc, helpers::display_cnf, required_lits, Dom},
	linear::{lex_geq_const, lex_leq_const, log_enc_add_fn, PosCoeff},
	trace::emit_clause,
	Assignment, CheckError, ClauseDatabase, Coeff, Comparator, Consistency, IntVarRef, Lit, Model,
	ModelConfig, Result, Term, Unsatisfiable,
};

#[derive(Debug, Clone, Default)]
pub struct LinExp {
	pub terms: Vec<Term>,
}

impl LinExp {
	pub fn size(&self) -> usize {
		self.terms.len()
	}

	pub fn lb(&self) -> Coeff {
		self.terms.iter().map(Term::lb).sum()
	}

	pub fn ub(&self) -> Coeff {
		self.terms.iter().map(Term::ub).sum()
	}
}

#[derive(Debug, Clone)]
pub struct Lin {
	pub exp: LinExp,
	pub cmp: Comparator,
	pub k: Coeff,
	pub lbl: Option<String>,
}

#[derive(Debug)]
pub(crate) enum LinCase {
	Couple(Term, Term),
	Fixed(Lin),
	Unary(Term, Comparator, Coeff),
	Binary(Term, Comparator, Term), // just for binary ineqs
	Scm(Term, IntVarRef),
	Rca(Term, Term, Term),
	Order,
	Other,
}

impl TryFrom<&Lin> for LinCase {
	type Error = Unsatisfiable;

	fn try_from(con: &Lin) -> Result<Self, Unsatisfiable> {
		let term_encs = con
			.exp
			.terms
			.iter()
			.map(|t| (t, t.x.borrow().e.clone()))
			.collect_vec();

		Ok(match (&term_encs[..], con.cmp, con.k) {
			([], _, _) => LinCase::Fixed(con.clone()),
			([(t, Some(IntVarEnc::Bin(_)))], cmp, _)
				if (t.c == 1
					|| t.c % 2 == 0) // multiple of 2
                    && !USE_COUPLING_IO_LEX =>
			{
				LinCase::Unary((*t).clone().encode_bin(None, cmp, None)?, cmp, con.k)
			}
			(
				[(x, Some(IntVarEnc::Bin(_))), (y, Some(IntVarEnc::Bin(_)))],
				Comparator::LessEq | Comparator::GreaterEq,
				0,
			) => LinCase::Binary((*x).clone(), con.cmp, (*y).clone()),
			// VIEW COUPLING
			// TODO this makes single literal comparisons views if possible
			// ([(t, Some(IntVarEnc::Ord(_))), (y, Some(IntVarEnc::Bin(None)))], _)
			// // | ([(y, Some(IntVarEnc::Bin(None))), (t, Some(IntVarEnc::Ord(_)))], _)
			// 	if y.c == -1
			// 		&& t.x.borrow().dom.size() <= 2
			// 		&& VIEW_COUPLING =>
			// {
			// 	// t.x.borrow_mut().encode(db, None)?;
			// 	// // let view = (*t).clone().encode_bin(None, self.cmp, None)?;
			// 	// let view = (*t).clone().encode_bin(None, self.cmp, None)?;
			// 	// y.x.borrow_mut().e = view.0.x.borrow().e.clone();
			// 	// Ok(())
			// }
			// SCM
			(
				[(t_x, Some(IntVarEnc::Bin(_))), (Term { c: -1, x: y }, Some(IntVarEnc::Bin(_)))]
				| [(Term { c: -1, x: y }, Some(IntVarEnc::Bin(_))), (t_x, Some(IntVarEnc::Bin(_)))],
				Comparator::Equal,
				0,
			) if matches!(y.borrow().e, Some(IntVarEnc::Bin(_))) => LinCase::Scm((*t_x).clone(), y.clone()),
			([(t, Some(IntVarEnc::Ord(_))), (y, Some(IntVarEnc::Bin(_)))], _, 0)
				if y.c == -1 && VIEW_COUPLING =>
			{
				LinCase::Couple((*t).clone(), (*y).clone())
			}
			// ([(x, Some(IntVarEnc::Bin(_)))], Comparator::Equal, k) => {
			// 	LinCase::Rca((*x).clone(), Term::from(0), Term::from(k))
			// }
			(
				[(x, Some(IntVarEnc::Bin(_))), (y, Some(IntVarEnc::Bin(_)))],
				Comparator::Equal,
				k,
			) => LinCase::Rca((*x).clone(), (*y).clone(), Term::from(-k)),
			(
				[(x, Some(IntVarEnc::Bin(_))), (y, Some(IntVarEnc::Bin(_))), (z, Some(IntVarEnc::Bin(_)))],
				Comparator::Equal,
				0,
			) if z.c.is_negative() => LinCase::Rca((*x).clone(), (*y).clone(), (*z).clone()),
			(encs, _, _)
				if encs
					.iter()
					.all(|e| matches!(e.1, Some(IntVarEnc::Ord(_)) | None)) =>
			{
				LinCase::Order
			}
			_ => LinCase::Other,
		})
	}
}

impl Lin {
	pub fn new(terms: &[Term], cmp: Comparator, k: Coeff, lbl: Option<String>) -> Self {
		Lin {
			exp: LinExp {
				terms: terms.to_vec(),
			},
			cmp,
			k,
			lbl,
		}
	}

	pub fn tern(x: Term, y: Term, cmp: Comparator, z: Term, lbl: Option<String>) -> Self {
		Lin {
			exp: LinExp {
				terms: vec![x, y, Term::new(-z.c, z.x)],
			},
			cmp,
			k: 0,
			lbl,
		}
	}

	pub fn lb(&self) -> Coeff {
		self.exp.lb()
	}

	pub fn ub(&self) -> Coeff {
		self.exp.ub()
	}

	pub(crate) fn propagate(
		&mut self,
		consistency: &Consistency,
	) -> Result<Vec<IntVarId>, Unsatisfiable> {
		let mut changed = vec![];
		match consistency {
			Consistency::None => unreachable!(),
			Consistency::Bounds => loop {
				let mut fixpoint = true;
				self.cmp.split().into_iter().try_for_each(|cmp| {
					match cmp {
						Comparator::LessEq => {
							let rs_lb = self.lb() - self.k;
							for term in &self.exp.terms {
								let mut x = term.x.borrow_mut();
								let size = x.size();
								let x_lb = if term.c.is_positive() {
									x.dom.lb()
								} else {
									x.dom.ub()
								};

								let id = x.id;

								// c*d <= c*x_lb - rs_lb
								// d <= x_lb - (rs_lb / c) (or d >= .. if d<0)
								let b = x_lb - (rs_lb / term.c);

								if term.c.is_negative() {
									x.ge(b);
								} else {
									x.le(b);
								}

								if x.size() < size {
									//println!("Pruned {}", size - x.size());
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == 0 {
									return Err(Unsatisfiable);
								}
							}
							Ok(())
						}
						Comparator::GreaterEq => {
							let xs_ub = self.ub() - self.k;
							for term in &self.exp.terms {
								let mut x = term.x.borrow_mut();
								let size = x.size();

								let id = x.id;
								let x_ub = if term.c.is_positive() {
									x.dom.ub()
								} else {
									x.dom.lb()
								};

								// c*d >= x_ub*c + xs_ub := d >= x_ub - xs_ub/c
								let b = x_ub - (xs_ub / term.c);

								if !term.c.is_negative() {
									x.ge(b);
								} else {
									x.le(b);
								}

								if x.size() < size {
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == 0 {
									return Err(Unsatisfiable);
								}
							}
							Ok(())
						}
						_ => unreachable!(),
					}
				})?;

				if fixpoint {
					return Ok(changed);
				}
			},
			Consistency::Domain => {
				todo!(
					"TODO: (super naive) Domain consistency propagator is not tested. Maybe remove"
				)
				/*
				assert!(self.cmp == Comparator::Equal);
				loop {
					let mut fixpoint = true;
					for (i, term) in self.exp.terms.iter().enumerate() {
						let id = term.x.borrow().id;
						term.x.borrow_mut().dom.retain(|d_i| {
							if self
								.exp
								.terms
								.iter()
								.enumerate()
								.filter_map(|(j, term_j)| {
									(i != j).then(|| {
										term_j
											.x
											.borrow()
											.dom
											.iter()
											.map(|d_j_k| term_j.c * *d_j_k)
											.collect::<Vec<_>>()
									})
								})
								.multi_cartesian_product()
								.any(|rs| {
									term.c * *d_i + rs.into_iter().sum()
										== 0
								}) {
								true
							} else {
								fixpoint = false;
								changed.push(id);
								false
							}
						});
						assert!(term.x.borrow().size() > 0);
					}

					if fixpoint {
						return changed;
					}
				}
				*/
			}
		}
	}

	pub(crate) fn is_tern(&self) -> bool {
		let cs = self.exp.terms.iter().map(|term| term.c).collect::<Vec<_>>();
		cs.len() == 3 && cs[2] == -1 && self.k == 0
	}

	pub(crate) fn check(&self, a: &Assignment) -> Result<(), CheckError> {
		let lhs = self
			.exp
			.terms
			.iter()
			.map(|term| term.c * a[&term.x.borrow().id].1)
			.sum::<Coeff>();

		if match self.cmp {
			Comparator::LessEq => lhs <= self.k,
			Comparator::Equal => lhs == self.k,
			Comparator::GreaterEq => lhs >= self.k,
		} {
			Ok(())
		} else {
			const SHOW_LP: bool = false;
			Err(CheckError::Fail(format!(
				"Inconsistency in {}: {} == {} !{} {}\n{}",
				self.lbl.clone().unwrap_or_default(),
				self.exp
					.terms
					.iter()
					.map(|term| {
						format!(
							"{} * {}={} (={})",
							term.c,
							term.x.borrow().lbl(),
							a[&term.x.borrow().id].1,
							term.c * a[&term.x.borrow().id].1,
						)
					})
					.join(" + "),
				lhs,
				self.cmp,
				self.k,
				SHOW_LP
					.then(|| {
						Model {
							cons: vec![self.clone()],
							..Model::default()
						}
						.to_text(crate::Format::Lp)
					})
					.unwrap_or_default()
			)))
		}
	}

	fn _is_simplified(&self) -> bool {
		self.exp
			.terms
			.iter()
			.all(|term| term.c != 0 && !term.x.borrow().is_constant())
	}

	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "lin_encoder", skip_all, fields(constraint = format!("{}", self)))
	)]
	pub fn encode<DB: ClauseDatabase>(&self, db: &mut DB, _config: &ModelConfig) -> Result {
		match LinCase::try_from(self)? {
			LinCase::Fixed(con) => con.check(&Assignment::default()).map_err(|_| Unsatisfiable),
			LinCase::Unary(t_x, cmp, k) => {
				// TODO refactor.....
				t_x.x.borrow_mut().encode_bin(db)?;
				let dom = t_x.x.borrow().dom.clone();
				let x = t_x.encode_bin(None, cmp, None)?;
				let x: IntVarRef = x.try_into().unwrap();
				let x_enc = x.clone().borrow_mut().encode_bin(db)?;
				x_enc.encode_unary_constraint(db, &cmp, k, &dom, false)
			}
			LinCase::Binary(t_x, cmp, t_y) => {
				println!("self = {}", self);

				t_x.x.borrow_mut().encode_bin(db)?;
				t_y.x.borrow_mut().encode_bin(db)?;

				let x_enc = t_x.x.borrow_mut().encode_bin(db)?;
				let t_y = t_y * -1;
				if let Ok(c) = t_y.clone().try_into() {
					let dom = t_x.x.borrow().dom.clone();
					x_enc.encode_unary_constraint(db, &cmp, c, &dom, false)
				} else {
					let y_enc = t_y.x.borrow_mut().encode_bin(db)?;
					x_enc.lex(db, cmp, y_enc)
				}
			}
			LinCase::Couple(t_x, t_y) => {
				t_x.x.borrow_mut().encode_ord(db)?;
				if !t_x.x.borrow().add_consistency {
					t_x.x.borrow_mut().consistent(db)?;
				}
				let y_enc = t_y.x.borrow_mut().encode_bin(db)?;

				let up = match self.cmp {
					Comparator::LessEq => false,
					Comparator::Equal => unreachable!(),
					Comparator::GreaterEq => true,
				};

				let (range_lb, range_ub) = y_enc.range();
				let dom = &t_y.x.borrow().dom;

				let mut xs = t_x
					.ineqs(up)
					.into_iter()
					.map(|(c, x, _)| (*y_enc.normalize((t_x.c * c) - self.k, dom), x))
					.collect_vec();

				if up {
					xs.reverse();
					xs.push((range_ub, vec![]));
				} else {
					xs.insert(0, (range_lb, vec![]));
				};

				xs.into_iter()
					.tuple_windows()
					.try_for_each(|((c_a, x_a), (c_b, x_b))| {
						let x = if up { x_a } else { x_b };
						let (c_a, c_b) = (c_a + 1, c_b);
						if PRINT_COUPLING >= 2 {
							println!("{up} {c_a}..{c_b} -> {x:?}");
						}
						let y = y_enc.ineqs(c_a, c_b, !up);
						if PRINT_COUPLING >= 2 {
							println!("{y:?}");
						}
						add_clauses_for(db, vec![vec![x.clone()], y])
					})
			}
			LinCase::Scm(t_x, y) => {
				t_x.x.borrow_mut().encode_bin(db)?; // encode x (if not encoded already)
									// encode y

				let tmp_y = t_x.clone().encode_bin(None, self.cmp, None)?;

				// TODO make Term decompose and use encode_bin for actual encoding incl scm, but for now (since it's not given Db, call scm_dnf) here
				(*y).borrow_mut().e = Some(IntVarEnc::Bin(Some(
					tmp_y.x.borrow_mut().encode_bin(db)?.scm_dnf(db, tmp_y.c)?,
				)));
				// TODO handle if y is already encoded
				y.borrow_mut().dom = t_x.bounds();
				Ok(())
			}
			LinCase::Rca(x, y, z) => {
				assert!(
					x.lb() + y.lb() <= -z.ub(),
					"LBs for addition not matching: {self}"
				);

				let z: IntVarRef = (z * -1).try_into().unwrap();

				let (x, y) = &[x, y]
					.into_iter()
					.map(|t| {
						// encode term and return underlying var
						t.x.borrow_mut().encode(db).unwrap();
						let t = t.encode_bin(None, self.cmp, None).unwrap();
						let x: IntVarRef = t.clone().try_into().unwrap_or_else(|_| {
							panic!("Calling Term::encode_bin on {t} should return 1*y")
						});
						x
					})
					.collect_tuple()
					.unwrap();

				assert!(
					matches!(z.borrow().e, Some(IntVarEnc::Bin(None))),
					"Last var {} should not have been encoded yet",
					z.borrow()
				);
				let z_ground = x.borrow().lb() + y.borrow().lb();
				let z_dom = Dom::from_bounds(z_ground, z.borrow().ub());
				let (x, y) = (
					x.borrow_mut().encode_bin(db)?.xs(),
					y.borrow_mut().encode_bin(db)?.xs(),
				);

				let z_lb = z.borrow().lb();
				z.borrow_mut().dom = z_dom; // fix lower bound to ground
				let lits = Some(required_lits(z_ground, z.borrow().dom.ub()));
				let z_bin = BinEnc::from_lits(&log_enc_add_fn(db, &x, &y, lits).unwrap());

				lex_geq_const(
					db,
					&z_bin.xs(),
					PosCoeff::new(z_lb - z_ground),
					z_bin.bits(),
				)?;

				// TODO [!] only has to be done for last constraint of lin decomp.. (could add_consistency to differentiate?)
				lex_leq_const(
					db,
					&z_bin.xs(),
					PosCoeff::new(z.borrow().ub() - z_ground),
					z_bin.bits(),
				)?;
				z.borrow_mut().e = Some(IntVarEnc::Bin(Some(z_bin)));
				Ok(())
			}
			LinCase::Order => {
				// encode all variables
				self.exp
					.terms
					.iter()
					.try_for_each(|t| t.x.borrow_mut().encode(db).map(|_| ()))?;

				assert!(
					self.exp.terms.iter().all(|t| match t.x.borrow().e {
						Some(IntVarEnc::Ord(_)) => true,
						Some(IntVarEnc::Bin(_)) => t.x.borrow().dom.size() <= 2,
						_ => false,
					}),
					"Non-order: {self}"
				);

				const SORT_BY_COEF: bool = true;
				let terms = if SORT_BY_COEF {
					self.exp
						.terms
						.iter()
						.cloned()
						.sorted_by_key(|t| -t.c)
						.collect_vec()
				} else {
					self.exp.terms.clone()
				};

				self.cmp.split().into_iter().try_for_each(|cmp| {
					let (_, cnf) = Self::encode_rec(&terms, &cmp, self.k, 0);
					if PRINT_COUPLING >= 3 {
						println!("{}", display_cnf(&cnf));
					}

					for c in cnf {
						emit_clause!(db, c)?;
					}
					Ok(())
				})
			}
			LinCase::Other => todo!("Cannot constrain: {self}\n{self:?}"),
		}

		/*
		   // TODO Support order-binary channelling
		// CHANNEL
		(
			[(t_x, Some(IntVarEnc::Ord(_))), (t_y, Some(IntVarEnc::Bin(_)))],
			Comparator::Equal,
		) if t_x.c.is_one() && t_y.c == -1 && USE_CHANNEL => {
			t_x.x.borrow_mut().encode_ord(db)?;
			if !t_x.x.borrow().add_consistency {
				t_x.x.borrow_mut().consistent(db)?;
			}
			let y_enc = t_y.x.borrow_mut().encode_bin(db)?;

			let (range_lb, range_ub) = unsigned_binary_range(y_enc.bits());
			y_enc.x.iter().enumerate().try_for_each(|(i, y_i)| {
				let r = 2.pow(i);
				let (l, u) = (range_lb.div(r), range_ub.div(r));
				add_clauses_for(
					db,
					vec![remove_red(
						num::iter::range_inclusive(l, u)
							.sorted_by_key(|k| (k.is_even(), *k))
							.filter_map(|k| {
								let y_i = if k.is_even() {
									-y_i.clone()
								} else {
									y_i.clone()
								};
								let a = y_enc.denormalize(r * k, &t_y.x.borrow().dom); // ??
								let b = a + r;
								let x_a = t_x.x.borrow().ineq(a, false, None).1;
								let x_b = t_x.x.borrow().ineq(b, true, None).1;
								if x_a == negate_cnf(x_b.clone()) {
									None
								} else {
									Some(
										[x_a, y_i.into(), x_b]
											.into_iter()
											.multi_cartesian_product()
											.concat()
											.into_iter()
											// .into_iter()
											.flatten()
											.collect(),
									)
								}
							})
							.collect(),
					)],
				)
			})
		}
		*/
	}

	fn encode_rec(
		terms: &[Term],
		cmp: &Comparator,
		k: Coeff,
		depth: usize,
	) -> (Option<Coeff>, Vec<Vec<Lit>>) {
		if let Some((head, tail)) = terms.split_first() {
			let up = head.c.is_positive() == (cmp == &Comparator::GreaterEq);
			if tail.is_empty() {
				let k_ = if up {
					div_ceil(k, head.c)
				} else {
					div_floor(k, head.c) + 1
				};

				if PRINT_COUPLING >= 2 {
					print!(
						"{}{} ({}*{} {cmp} {k}) (= {} {} {k_})",
						"\t".repeat(depth),
						if up { "up: " } else { "down: " },
						head.c,
						head.x.borrow(),
						head.x.borrow().lbl(),
						if head.c.is_positive() {
							*cmp
						} else {
							cmp.reverse()
						}
					);
				}

				let (c, cnf) = head.x.borrow().ineq(k_, up, None);

				if PRINT_COUPLING >= 2 {
					println!("== {cnf:?}",);
				}

				(c.map(|c| head.c * c), cnf)
			} else {
				let mut last_a = None; // last antecedent implies till here
				let mut last_k = None; // last consequent implies to here
				(
					None,
					head.ineqs(up)
						.into_iter()
						.map_while(|(d, conditions, implies)| {
							// l = x>=d+1, ~l = ~(x>=d+1) = x<d+1 = x<=d
							let k_ = k - head.c * d;

							if PRINT_COUPLING >= 2 {
								print!(
									"{} {} {}*({} {cmp} {}) (->x{cmp}{implies}) = [{:?}] (k={k} - {}*{d} = {k_}) last_a={last_a:?} last_k={last_k:?}",
                                    "\t".repeat(depth),
									if up {
										"up: "
									} else {
										"down: "
									},
									head.c,
									head.x.borrow(),
									if up { d + 1 } else { d },
									conditions,
									head.c,
								);
							}


							let antecedent_implies_next = last_a
								.map(|last_a| {
									if cmp == &Comparator::GreaterEq {
										d >= last_a
									} else {
										d <= last_a
									}
								})
								.unwrap_or_default();
							let consequent_implies_next = last_k
								.map(|last_k| {
									if cmp == &Comparator::GreaterEq {
                                        k_ <= last_k
                                    } else {
                                        k_ >= last_k
                                    }
								})
								.unwrap_or_default();

							if PRINT_COUPLING >= 2 {
								print!(" {}/{}", antecedent_implies_next, consequent_implies_next);
							}

							if PRINT_COUPLING >= 2 {
								println!();
							}

							let (c, cnf) = Self::encode_rec(tail, cmp, k_, depth + 1);
							let cnf = cnf
								.into_iter()
								.map(|r| conditions.clone().into_iter().chain(r).collect())
								.collect_vec();


							if antecedent_implies_next && consequent_implies_next  {
                                if PRINT_COUPLING >= 2 {
										println!("SKIP");
                                }
									return Some(vec![]); // some consequent -> skip clause
							}

							last_k = c;
							last_a = Some(implies);

							Some(cnf)
						})
						.flatten()
						.collect(),
				)
			}
		} else {
			unreachable!();
		}
	}

	pub fn vars(&self) -> Vec<IntVarRef> {
		self.exp
			.terms
			.iter()
			.map(|term| &term.x)
			.unique_by(|x| x.borrow().id)
			.cloned()
			.collect()
	}

	pub(crate) fn _simplified(self) -> Result<Lin> {
		let mut k = self.k;
		let con = Lin {
			exp: LinExp {
				terms: self
					.exp
					.terms
					.into_iter()
					.filter_map(|t| {
						if t.x.borrow().is_constant() {
							k -= t.c * t.x.borrow().dom.lb();
							None
						} else {
							Some(t)
						}
					})
					.collect(),
			},
			k,
			..self
		};
		if con.exp.terms.is_empty() {
			con.check(&Assignment::default())
				.map(|_| con)
				.map_err(|_| Unsatisfiable)
		} else {
			Ok(con)
		}
	}
}
