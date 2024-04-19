use crate::helpers::{add_clauses_for, unsigned_binary_range};
use crate::int::helpers::display_cnf;
use crate::int::model::Decompose;
use crate::{
	linear::log_enc_add_, trace::emit_clause, Assignment, CheckError, ClauseDatabase, Coefficient,
	Comparator, Consistency, IntVarRef, Literal, Model, ModelConfig, Result, Term, Unsatisfiable,
};
use itertools::Itertools;

use super::{
	model::{LinDecomposer, PRINT_COUPLING, USE_COUPLING_IO_LEX, VIEW_COUPLING},
	IntVarEnc, IntVarId,
};

#[derive(Debug, Clone, Default)]
pub struct LinExp<Lit: Literal, C: Coefficient> {
	pub terms: Vec<Term<Lit, C>>,
}

#[derive(Debug, Clone)]
pub struct Lin<Lit: Literal, C: Coefficient> {
	pub exp: LinExp<Lit, C>,
	pub cmp: Comparator,
	pub k: C,
	pub lbl: Option<String>,
}

impl<Lit: Literal, C: Coefficient> Lin<Lit, C> {
	pub fn new(terms: &[Term<Lit, C>], cmp: Comparator, k: C, lbl: Option<String>) -> Self {
		Lin {
			exp: LinExp {
				terms: terms.to_vec(),
			},
			cmp,
			k,
			lbl,
		}
	}

	pub fn tern(
		x: Term<Lit, C>,
		y: Term<Lit, C>,
		cmp: Comparator,
		z: Term<Lit, C>,
		lbl: Option<String>,
	) -> Self {
		Lin {
			exp: LinExp {
				terms: vec![x, y, Term::new(-z.c, z.x)],
			},
			cmp,
			k: C::zero(),
			lbl,
		}
	}

	pub fn decompose(
		self,
		model_config: &ModelConfig<C>,
		num_var: usize,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		LinDecomposer::default().decompose(self, num_var, model_config)
		// let decomp = LinDecomposer::default().decompose(self, num_var, model_config)?;
	}

	pub fn lb(&self) -> C {
		self.exp.terms.iter().map(Term::lb).fold(C::zero(), C::add)
	}

	pub fn ub(&self) -> C {
		self.exp.terms.iter().map(Term::ub).fold(C::zero(), C::add)
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
									x.ge(&b);
								} else {
									x.le(&b);
								}

								if x.size() < size {
									//println!("Pruned {}", size - x.size());
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == C::zero() {
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
									x.ge(&b);
								} else {
									x.le(&b);
								}

								if x.size() < size {
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == C::zero() {
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
				todo!()
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
									term.c * *d_i + rs.into_iter().fold(C::zero(), |a, b| a + b)
										== C::zero()
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
		cs.len() == 3 && cs[2] == -C::one() && self.k.is_zero()
	}

	pub(crate) fn check(&self, a: &Assignment<C>) -> Result<(), CheckError<Lit>> {
		let lhs = self
			.exp
			.terms
			.iter()
			.map(|term| term.c * a[&term.x.borrow().id].1)
			.fold(C::zero(), C::add);

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
			.all(|term| !term.c.is_zero() && !term.x.borrow().is_constant())
	}

	// fn into_tern(self) -> Self {
	// 	Lin {
	// 		exp: LinExp {
	// 			terms: self
	// 				.exp
	// 				.terms
	// 				.into_iter()
	// 				.with_position()
	// 				.map(|pos| match pos {
	// 					(Position::Last, term) => term * -C::one(),
	// 					(_, term) => term, // also matches Only element; so unary constraints are not minused
	// 				})
	// 				.collect(),
	// 		},
	// 		..self
	// 	}
	// }

	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "lin_encoder", skip_all, fields(constraint = format!("{}", self)))
	)]
	pub fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		_config: &ModelConfig<C>,
	) -> Result {
		const NEW_COUPLING: bool = true;
		if PRINT_COUPLING {
			println!("{self}");
		}

		// TODO only one cmp == Equality (and exchange equalities)
		let term_encs = self
			.exp
			.terms
			.iter()
			.map(|t| (t, t.x.borrow().e.clone()))
			// TODO hopefully does not clone inner enc?
			.collect_vec();

		match (&term_encs[..], self.cmp) {
			([], _) => self
				.check(&Assignment::default())
				.map_err(|_| Unsatisfiable),
			([(Term { c, x }, Some(IntVarEnc::Bin(_)))], _)
				if c.is_one() && !USE_COUPLING_IO_LEX =>
			{
				let x_enc = x.borrow_mut().encode_bin(db)?; // avoid BorrowMutError
				x_enc.encode_unary_constraint(db, &self.cmp, self.k, &x.borrow().dom, false)
			}
			// VIEW COUPLING
			([(t, Some(IntVarEnc::Ord(_))), (y, Some(IntVarEnc::Bin(None)))], cmp)
				if y.c == -C::one()
					&& t.x.borrow().dom.size() <= C::one() + C::one()
					&& cmp == Comparator::LessEq
					&& VIEW_COUPLING =>
			{
				t.x.borrow_mut().encode(db, None)?;
				let view = (*t).clone().encode_bin(None, self.cmp, None)?;
				y.x.borrow_mut().e = view.x.borrow().e.clone();
				Ok(())
			}
			// SCM
			([(t, _), (Term { c: y_c, x: y }, Some(IntVarEnc::Bin(None)))], Comparator::Equal)
				if *y_c == -C::one()
					&& self.k.is_zero() && matches!(y.borrow().e, Some(IntVarEnc::Bin(_))) =>
			{
				assert!(t.c.is_positive(), "neg scm: {self}");
				t.x.borrow_mut().encode_bin(db)?; // encode x (if not encoded already)
								  // encode y
				let new_y = (*t).clone().encode_bin(None, self.cmp, None)?;
				(*y).borrow_mut().e = Some(IntVarEnc::Bin(Some(
					new_y.x.borrow_mut().encode_bin(db)?.scm_dnf(db, new_y.c)?,
				)));
				Ok(())
			}
			(
				[(x, Some(IntVarEnc::Bin(_))), (y, Some(IntVarEnc::Bin(_))), (z, Some(IntVarEnc::Bin(_)))],
				Comparator::Equal,
			) if [y.c, z.c] == [C::one(), -C::one()] => {
				assert!(
					x.lb() + y.lb() == ((*z).clone() * -C::one()).lb(),
					"LBs for addition not matching: {self}"
				);

				// TODO do not have to encode z if we use functional addition!
				let z = (*z).clone() * -C::one();
				let (x, y, z) = &[x, y, &z] // .with_position()
					.into_iter()
					.map(|t| t.x.borrow_mut().encode_bin(db).unwrap().xs())
					.collect_tuple()
					.unwrap();

				log_enc_add_(db, x, y, &self.cmp, z)
			}
			// COUPLING
			([(x, Some(IntVarEnc::Ord(_))), (y, Some(IntVarEnc::Bin(_)))], cmp)
				if x.c == C::one() && y.c == -C::one() && cmp.is_ineq() && NEW_COUPLING =>
			{
				if PRINT_COUPLING {
					println!("NEW");
				}
				x.x.borrow_mut().encode_ord(db)?;
				let y_enc = y.x.borrow_mut().encode_bin(db)?;

				let up = match cmp {
					Comparator::LessEq => false,
					Comparator::Equal => unreachable!(),
					Comparator::GreaterEq => true,
				};

				let (range_lb, range_ub) = unsigned_binary_range::<C>(y_enc.bits());
				let dom = &y.x.borrow().dom;

				let mut xs = x
					.ineqs(up)
					.into_iter()
					.map(|(c, x, _)| (y_enc.normalize(c - self.k, dom), x))
					.collect_vec();

				if up {
					xs.reverse();
					xs.push((range_ub + C::one(), vec![]));
				} else {
					xs.insert(0, (range_lb, vec![]));
				};

				xs.into_iter()
					.tuple_windows()
					.try_for_each(|((c_a, x_a), (c_b, x_b))| {
						let x = if up { x_a } else { x_b };
						let (c_a, c_b) = (c_a + C::one(), c_b);
						if PRINT_COUPLING {
							println!("{up} {c_a}..{c_b} -> {x:?}");
						}
						let y = y_enc.ineqs(c_a, c_b, !up);
						if PRINT_COUPLING {
							println!("{y:?}");
						}
						add_clauses_for(db, vec![vec![x.clone()], y])
					})
			}
			_ => {
				// encode all variables
				self.exp
					.terms
					.iter()
					.try_for_each(|t| t.x.borrow_mut().encode(db, None).map(|_| ()))?;

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
				// TODO try putting biggest domain last

				// let mut covered = None;
				// let mut last_consequence = None;
				// let mut last_k = None;
				self.cmp.split().into_iter().try_for_each(|cmp| {
					// TODO move to closure to add DB?
					let (_, cnf) = Self::encode_rec(&terms, &cmp, self.k, 0);
					if PRINT_COUPLING {
						println!("{}", display_cnf(&cnf));
					}

					for c in cnf {
						emit_clause!(db, &c)?;
					}
					Ok(())
					/*
					let (last, firsts) = &terms.split_last().unwrap();
					[vec![(C::zero(), vec![], true)]] // handle empty conditions
						.into_iter()
						.chain(firsts.iter().map(|term| term.ineqs(&cmp.reverse())))
						.multi_cartesian_product()
						.flat_map(|conditions| {
							// calculate c*last_x !# k-sum(conditions)
							let k = self.k
								- conditions
									.iter()
									.map(|(c, _, _)| *c)
									.fold(C::zero(), C::add);

							if PRINT_COUPLING {
								print!(
									"\t({}) -> ({}*{}){}{}",
									conditions
										.iter()
										.skip(1) // skip "empty conditions" fixed ineq
										.zip(&self.exp.terms)
										.map(|((c, cnf, is_implied), t)| format!(
											"{}{}{} {:?}{}",
											t.x.borrow().lbl(),
											cmp.reverse(),
											c,
											cnf,
											is_implied.then_some("^").unwrap_or_default()
										))
										.join(" /\\ "),
									last.c,
									last.x.borrow(),
									cmp,
									k,
								);
							}

							let (k, up) = last.ineq(k, &cmp);
							if PRINT_COUPLING {
								print!(
									" (= {}{}{})",
									last.x.borrow().lbl(),
									if up {
										Comparator::GreaterEq
									} else {
										Comparator::LessEq
									},
									k
								)
							}

							// if let Some(covered) = covered {
							// 	if {
							// 		if up {
							// 			k <= covered
							// 		} else {
							// 			k >= covered
							// 		}
							// 	} && conditions.iter().all(|(_, _, is_implied)| *is_implied)
							// 		// && REMOVE_IMPLIED_CLAUSES
							// 	// && false
							// 	{
							// 		println!(" SKIP {k} <= {covered}");
							// 		return None;
							// 	}
							// }

							let (new_covered, consequence) = last.x.borrow().ineq(k, up);

							if conditions.iter().all(|(_, _, is_implied)| *is_implied)
								&& last_consequence
									.as_ref()
									.map(|c| &consequence == c)
									.unwrap_or_default()
							{
								return None;
							}
							last_consequence = Some(consequence.clone());

							covered = Some(new_covered);

							if PRINT_COUPLING {
								println!(" {:?} COV {}", consequence, covered.as_ref().unwrap());
							}
							Some((conditions, consequence))
						})
						// .chain([None])
						// .tuple_windows()
						// .flat_map(|(curr, next)| {
						// 	if let Some((next_conditions, next_consequence)) = next {
						// 		let (_, curr_consequence) = curr.as_ref().unwrap();
						// 		let all_implied =
						// 			next_conditions.iter().all(|(_, _, is_implied)| *is_implied)
						// 				&& (curr_consequence == &next_consequence); // TODO replace by checking implication i/o equivalence
						// 		if REMOVE_IMPLIED_CLAUSES && all_implied {
						// 			return None; // skip curr
						// 		}
						// 		curr
						// 	} else {
						// 		// always post last iteration
						// 		curr
						// 	}
						// })
						.try_for_each(|(conditions, consequence)| {
							add_clauses_for(
								db,
								conditions
									.iter()
									.map(|(_, cnf, _)| negate_cnf(cnf.clone())) // negate conditions
									.chain([consequence])
									.collect(),
							)
						})
						*/
				})
			}
		}
	}

	// #[cfg_attr(
	// 	feature = "trace",
	// 	tracing::instrument(name = "encode_rec", skip_all, fields(constraint = format!("{} {} {}", terms.iter().join(" "), cmp, k)))
	// )]
	fn encode_rec(
		terms: &[Term<Lit, C>],
		cmp: &Comparator,
		k: C,
		depth: usize,
	) -> (Option<C>, Vec<Vec<Lit>>) {
		if let Some((head, tail)) = terms.split_first() {
			let up = head.c.is_positive() == (cmp == &Comparator::GreaterEq);
			if tail.is_empty() {
				let k_ = if up {
					k.div_ceil(&head.c)
				} else {
					k.div_floor(&head.c.clone()) + C::one()
				};

				if PRINT_COUPLING {
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

				if PRINT_COUPLING {
					println!("== {cnf:?}",);
				}

				(c.map(|c| head.c * c), cnf)
			} else {
				let mut stop = false;
				let mut last_a = None; // last antecedent implies till here
				let mut last_k = None; // last consequent implies to here
					   // let mut last_cnf = None;
				(
					None,
					head.ineqs(up)
						.into_iter()
						.map_while(|(d, conditions, implies)| {
							if stop {
								return None;
							}

							// l = x>=d+1, ~l = ~(x>=d+1) = x<d+1 = x<=d
							let k_ = k - head.c * d;

							if PRINT_COUPLING {
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
									if up { d + C::one() } else { d },
									conditions,
									head.c,
								);
							}

							let antecedent_implies_next = last_a
								.map(|last_a| {
									// if cmp == &Comparator::GreaterEq {
                                    // TODO  ?
									if up {
										d >= last_a
									} else {
										d <= last_a
									}
								})
								.unwrap_or_default();
							let consequent_implies_next = last_k
								.map(|last_k| {
                                    // k_ <= last_k
									// if cmp == &Comparator::GreaterEq {
									if up {
										d >= last_k
									} else {
										d <= last_k
									}
								})
								.unwrap_or_default();
							if PRINT_COUPLING {
								print!(" {}/{}", antecedent_implies_next, consequent_implies_next);
							}

							if PRINT_COUPLING {
								println!();
							}


							let (c, cnf) = Self::encode_rec(tail, cmp, k_, depth + 1);
							let cnf = cnf
								.into_iter()
								.map(|r| conditions.clone().into_iter().chain(r).collect())
								.collect_vec();

                            // if PRINT_COUPLING {
                            //     print!("cnf = {:?} given {:?} -> ", cnf, last_cnf);
                            // }

                            // missing let-chain feature
                            if PRINT_COUPLING {
                            println!("{}", display_cnf(&cnf));
                            // println!("given:\n{}", display_cnf(last_cnf.unwrap_or(&vec![])));
                            }

                            // let cnf =
                            //     if let (true, Some(last_cnf)) = (REMOVE_IMPLIED_CLAUSES, last_cnf)  {
                            //         filter_cnf(cnf, last_cnf)
                            //     } else {
                            //         cnf.clone()
                            //     };
                            if PRINT_COUPLING {
                            println!("filt:\n{}", display_cnf(&cnf));
                            }

                            // if PRINT_COUPLING {
                            //     print!("cnf = {:?}", cnf);
                            // }

							// if antecedent_implies_next && consequent_implies_next {
                                // // debug_assert!(last_cnf.clone().map(|last_cnf| is_cnf_superset(&last_cnf, &cnf))
                                // //               .unwrap_or(true), "Expected {last_cnf:?} ⊆ {cnf:?}");

							// 	if PRINT_COUPLING {
							// 		println!("SKIP: {last_cnf:?} ⊆ {cnf:?}");
							// 	}

							// 	if REMOVE_IMPLIED_CLAUSES {
							// 		// if PRINT_COUPLING {
							// 		// 	println!();
							// 		// }
							// 		return Some(vec![]); // some consequent -> skip clause
							// 	}
							// }

								// if PRINT_COUPLING {
								// 	println!("NOSKIP: {last_cnf:?} !⊆ {cnf:?}");
								// }


                            // last_cnf = Some(cnf.clone());
							last_k = c;
							last_a = Some(implies);

							// // TODO or if r contains empty clause?
							if cnf == vec![vec![]] {
								stop = true;
							}

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

	pub fn vars(&self) -> Vec<IntVarRef<Lit, C>> {
		self.exp
			.terms
			.iter()
			.map(|term| &term.x)
			.unique_by(|x| x.borrow().id)
			.cloned()
			.collect()
	}

	pub(crate) fn simplified(self) -> Result<Lin<Lit, C>> {
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

	/*
		#[cfg_attr(
			feature = "trace",
			tracing::instrument(name = "lin_encoder", skip_all, fields(constraint = format!("{}", self)))
		)]
		pub fn _encode<DB: ClauseDatabase<Lit = Lit>>(
			&self,
			db: &mut DB,
			config: &ModelConfig<C>,
		) -> Result {
			// TODO assert simplified/simplify
			// assert!(self._is_simplified());

			let mut encoder = TernLeEncoder::default();
			// TODO use binary heap

			if config.decomposer == Decomposer::Rca || config.scm == Scm::Pow {
				assert!(config.cutoff == Some(C::zero()));
				let mut k = self.k;
				let mut encs = self
					.clone()
					.exp
					.terms
					.into_iter()
					.flat_map(|term| {
						term.encode(db, config).map(|(xs, c)| {
							k -= c;
							xs.into_iter()
								.filter(|x| {
									if let IntVarEnc::Const(c) = x {
										k -= *c;
										false
									} else {
										true
									}
								})
								.collect_vec()
						})
					})
					.flatten()
					.collect::<Vec<_>>();
				assert!(
					encs.iter().all(|e| matches!(e, IntVarEnc::Bin(_))),
					"{encs:?}"
				);

				if self
					.exp
					.terms
					.iter()
					.all(|term| matches!(term.x.borrow().e.as_ref().unwrap(), IntVarEnc::Bin(_)))
				{
					// TODO hard to do in a reduce ..
					// TODO Replace 0 for first element

					encs.sort_by_key(IntVarEnc::ub);
					while encs.len() > 1 {
						let x = encs.pop().unwrap();
						let z = if let Some(y) = encs.pop() {
							x.add(db, &mut encoder, &y, None, None)?
						} else {
							x
						};

						encs.insert(
							encs.iter()
								.position(|enc| z.ub() < enc.ub())
								.unwrap_or(encs.len()),
							z,
						);
						debug_assert!(encs.windows(2).all(|x| x[0].ub() <= x[1].ub()));
					}

					assert!(encs.len() == 1);
					encoder.encode(
						db,
						&TernLeConstraint::new(
							&encs.pop().unwrap(),
							&IntVarEnc::Const(C::zero()),
							&self.cmp,
							&IntVarEnc::Const(k),
						),
					)?;
				}
				return Ok(());
			}

			let mut k = self.k;
			let encs = self
				.clone()
				// Encodes terms into ternary constrain (i.e. last term is multiplied by -1)
				.into_tern()
				.exp
				.terms
				.into_iter()
				.with_position()
				.flat_map(|(pos, term)| {
					term.encode(db, config).map(|(xs, c)| {
						match pos {
							Position::Last => {
								k += c;
							}
							_ => {
								k -= c;
							}
						}
						xs
					})
				})
				.flatten()
				.collect::<Vec<_>>();

			// TODO generalize n-ary encoding; currently using fallback of TernLeEncoder
			return match &encs[..] {
				[] => return Ok(()),
				[x] if DECOMPOSE => encoder.encode(
					db,
					&TernLeConstraint::new(
						x,
						&IntVarEnc::Const(C::zero()),
						&self.cmp,
						&IntVarEnc::Const(k),
					),
				),
				[x, z] if DECOMPOSE => encoder.encode(
					db,
					&TernLeConstraint::new(x, &IntVarEnc::Const(-k), &self.cmp, z),
				),
				[x, y, z] if DECOMPOSE => {
					let z = z.add(db, &mut encoder, &IntVarEnc::Const(k), None, None)?;
					encoder.encode(db, &TernLeConstraint::new(x, y, &self.cmp, &z))
				}
				_ => {
					assert!(
						encs.iter()
							.all(|enc| matches!(enc, IntVarEnc::Ord(_) | IntVarEnc::Const(_))),
						"TODO: {encs:?}"
					);

					// just get encoding; does not need to handle terms coefficient here
					// let encs = self
					// 	.clone()
					// 	.exp
					// 	.terms
					// 	.into_iter()
					// 	.map(|term| {
					// 		term.x.borrow_mut().encode(db, &mut HashMap::new(), true)?;
					// 		Ok(term.x.borrow().e.as_ref().unwrap().clone())
					// 	})
					// 	.collect::<Result<Vec<_>>>()?;
					// TODO support binary
					self.cmp.split().into_iter().try_for_each(|cmp| {
						let is_leq = matches!(cmp, Comparator::LessEq);

						// encs[0..encs.len() - 1]
						self.exp
							.terms
							.iter()
							// .zip(&self.exp.terms)
							.map(|term| {
								term.ineqs(&Comparator::GreaterEq)
								// if is_leq == term.c.is_positive() {
								// 	term.geqs()
								// } else {
								// 	term.leqs()
								// }
							})
							.multi_cartesian_product()
							.try_for_each(|geqs| {
								let rhs = geqs
									.iter()
									.zip(&self.exp.terms)
									.map(|((d, _), term)| {
										if is_leq == term.c.is_positive() {
											term.c * (d.end - C::one())
										} else {
											term.c * d.start
										}
									})
									.fold(self.k, C::sub);

								let conditions = geqs
									.iter()
									.map(|(_, cnf)| negate_cnf(cnf.clone()))
									.collect::<Vec<_>>();

								let (last_enc, last_c) =
									(&encs[encs.len() - 1], &self.exp.terms[encs.len() - 1].c);

								let last = if is_leq == last_c.is_positive() {
									last_enc.leq_(rhs.div_ceil(last_c))
								} else {
									last_enc.geq_(rhs.div_floor(last_c))
								};

								let cnf = conditions.iter().cloned().chain([last]).collect();
								add_clauses_for(db, cnf)
							})
					})
				}
			};
		}
	*/
}
