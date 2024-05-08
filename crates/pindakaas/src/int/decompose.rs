use crate::int::con::LinCase;
use crate::ModelConfig;
use crate::{
	int::{model::USE_CHANNEL, Dom, IntVarEnc},
	Assignment, BddEncoder, Coefficient, Comparator, Decomposer, IntLinExp as LinExp, IntVarId,
	Lin, Literal, Model, SwcEncoder, Term, TotalizerEncoder, Unsatisfiable,
};
use itertools::{Itertools, Position};
use std::collections::HashMap;

pub trait Decompose<Lit: Literal, C: Coefficient> {
	fn decompose(
		&self,
		// lin: Lin<Lit, C>,
		// num_var: usize,
		model: Model<Lit, C>,
		// model_config: &ModelConfig<C>,
		// cse: Option<Cse<Lit, C>>,
	) -> Result<Model<Lit, C>, Unsatisfiable>;

	// fn fold(&self, model: Model<Lit, C>) -> Result<Model<Lit, C>> {
	// 	Ok(model)
	// }
}

#[derive(Debug, Default)]
pub struct EqualizeTernsDecomposer {}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for EqualizeTernsDecomposer {
	fn decompose(&self, model: Model<Lit, C>) -> Result<Model<Lit, C>, Unsatisfiable> {
		const REMOVE_GAPS: bool = true;

		let cons = model.cons.iter().cloned().collect_vec();
		Ok(Model {
			cons: cons
				.into_iter()
				.map(|con| {
					if REMOVE_GAPS && con.exp.terms.len() >= 2 && con.cmp.is_ineq() {
						if con
							.exp
							.terms
							.iter()
							.all(|t| matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_))))
						{
							if let Some((last, firsts)) = con.exp.terms.split_last() {
								let (lb, ub) =
									firsts.iter().fold((C::zero(), C::zero()), |(lb, ub), t| {
										(lb + t.lb(), (ub + t.ub()))
									});
								let (lb, ub) = match con.cmp {
									Comparator::LessEq => (lb, std::cmp::min(ub, -last.lb())),
									Comparator::GreaterEq => (std::cmp::max(-last.ub(), lb), ub),
									Comparator::Equal => unreachable!(),
								};

								last.x.borrow_mut().dom = Dom::from_bounds(lb, ub);

								Lin {
									exp: LinExp {
										terms: firsts.iter().chain([last]).cloned().collect(),
									},
									cmp: Comparator::Equal,
									..con
								}
							} else {
								unreachable!()
							}
						} else if USE_CHANNEL
							&& matches!(
								// terrible fix for updating domain of channelled vars
								// TODO only works for one directions of the coupling
								con.exp
									.terms
									.iter()
									.map(|t| t.x.borrow().e.clone())
									.collect_vec()[..],
								[Some(IntVarEnc::Ord(None)), Some(IntVarEnc::Bin(None))]
								if con.exp.terms[0].c.is_one() && con.exp.terms[1].c == -C::one() && USE_CHANNEL
							) {
							con.exp.terms[0].x.borrow_mut().dom =
								con.exp.terms[1].x.borrow().dom.clone();
							con
						} else {
							con
						}
					} else {
						con
					}
				})
				// .flat_map(|con| {
				// 	println!("con = {}", con);
				// 	} else {
				// 		vec![con]
				// 	}
				// })
				.collect(),
			// num_var,
			// config: config.clone(),
			// ..Model::default()
			..model
		})
	}
}

/*
#[derive(Default)]
pub struct UniformBinEqDecomposer {}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for UniformBinEqDecomposer {
	fn decompose(
		&self,
		model: Model<Lit, C>, // con: Lin<Lit, C>,
							  // num_var: usize,
							  // model_config: &ModelConfig<C>,
							  // cse: Option<Cse<Lit, C>>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		let mut model = Model::<Lit, C>::new(num_var, model_config);
		if con.cmp.is_ineq()
			&& con.exp.terms.len() >= 3
			&& con.k.is_zero() // TODO potentially could work for non-zero k
			&& con
				.exp
				.terms
				.iter()
				.all(|t| matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_))))
		{
			if let Some((last, firsts)) = con.exp.terms.split_last() {
				// sum all but last term into lhs, where lb(lhs)=lb(sum(firsts)) (to match addition)
				// but ub(lhs) is same if cmp # = <= (because its binding)
				// if # = >=, the ub(lhs) is not binding so set to inf ~= lb(sum(firsts))
				// but the lb(lhs) is, which might be set to low, so we constrain lhs>=lb later
				let lhs = model
					.new_var_from_dom(
						{
							let (lb, ub) =
								firsts.iter().fold((C::zero(), C::zero()), |(lb, ub), t| {
									(lb + t.lb(), ub + t.ub())
								});
							match con.cmp {
								Comparator::LessEq => Dom::from_bounds(lb, last.x.borrow().ub()),
								Comparator::Equal => todo!(),
								Comparator::GreaterEq => Dom::from_bounds(lb, ub),
							}
						},
						true,                       // TODO should be able to set to model_confing.add_consistency
						Some(IntVarEnc::Bin(None)), // annotate to use BinEnc
						Some(format!("eq-{}", last.x.borrow().lbl())), // None,
					)
					.unwrap();

				// sum(firsts) = sum(lhs)
				model.add_constraint(Lin {
					exp: LinExp {
						terms: firsts
							.iter()
							.cloned()
							.chain([Term::new(-C::one(), lhs.clone())])
							.collect(),
					},
					cmp: Comparator::Equal,
					k: C::zero(),
					lbl: con.lbl.clone().map(|lbl| (format!("eq-1-{}", lbl))),
				})?;

				// If # = >=, the original lb is binding!
				if matches!(con.cmp, Comparator::GreaterEq) {
					model.add_constraint(Lin {
						exp: LinExp {
							terms: [Term::new(C::one(), lhs.clone())].to_vec(),
						},
						cmp: Comparator::GreaterEq,
						k: last.x.borrow().lb(),
						lbl: con.lbl.clone().map(|lbl| (format!("eq-1-{}", lbl))),
					})?;
				}

				// if possible, we change the domain of last.x so its binary encoding is grounded at the same lower bound as z_prime so we can constrain bitwise using lex constraint
				// TODO otherwise, coupling will take care of it, but this is non-ideal
				if matches!(last.x.borrow().e, Some(IntVarEnc::Bin(None))) {
					let x_dom = last
						.x
						.borrow()
						.dom
						.clone()
						.union(Dom::constant(lhs.borrow().lb()));
					last.x.borrow_mut().dom = x_dom;
				}

				// lhs # rhs
				model.add_constraint(Lin {
					exp: LinExp {
						terms: [Term::new(C::one(), lhs), last.clone()].to_vec(),
					},
					cmp: con.cmp,
					k: C::zero(),
					lbl: con.lbl.clone().map(|lbl| (format!("eq-2-{}", lbl))),
				})?;
			} else {
				unreachable!()
			}
		} else {
			model.add_constraint(con)?;
		}
		Ok(model)
	}
}
*/

#[derive(Debug, Default)]
pub struct EncSpecDecomposer<Lit: Literal, C: Coefficient> {
	pub(crate) cutoff: Option<C>,
	pub(crate) spec: Option<HashMap<IntVarId, IntVarEnc<Lit, C>>>,
}

const COUPLE_SINGLE_VARS: bool = true;
impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for EncSpecDecomposer<Lit, C> {
	fn decompose(
		&self,
		model: Model<Lit, C>,
		// con: Lin<Lit, C>,
		// num_var: usize,
		// config: &ModelConfig<C>,
		// cse: Option<Cse<Lit, C>>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		model
			.vars()
			.into_iter()
			.map(|x| {
				if let Some(spec) = self.spec.as_ref() {
					// only encode var which are specified
					if let Some(var_enc) = {
						let id = x.borrow().id;
						spec.get(&id)
					} {
						// overwriting encodings
						x.borrow_mut().e = Some(var_enc.clone());
					}
				} else {
					x.borrow_mut().decide_encoding(self.cutoff);
				}
				let is_order = matches!(x.borrow().e, Some(IntVarEnc::Ord(_)));
				if !is_order && x.borrow().lbl.as_ref().unwrap().contains("bdd") {
					// || x.borrow().dom.density() > 0.3
					x.borrow_mut().add_consistency = false
				}
				(x.clone(), is_order)
			})
			.collect_vec();

		let cons = model.cons.iter().cloned();
		let mut model = Model {
			cons: vec![],
			..model
		};

		cons.into_iter().try_for_each(|con| {
			let encs = con
				.exp
				.terms
				.iter()
				.map(|t| matches!(t.x.borrow().e.as_ref().unwrap(), IntVarEnc::Ord(_)))
				.collect_vec();

			// Couple single order encoded variable in mixed constraints, unless this constraint itself is a coupling
			if COUPLE_SINGLE_VARS
				&& encs.len() >= 2
				&& encs.iter().any(|e| *e)
				&& encs.iter().any(|e| !e)
				&& !matches!(LinCase::try_from(&con)?, LinCase::Couple(_, _))
			{
				let mut is_last_term = false;
				let con = Lin {
					exp: LinExp {
						terms: con
							.exp
							.terms
							.iter()
							.with_position()
							.map(|(p, t)| {
								Ok(if let Some(IntVarEnc::Ord(None)) = t.x.borrow().e.clone() {
									// if !matches!(p, Position::Last) {

									is_last_term = matches!(p, Position::Last);
									t.clone().encode_bin(
										Some(&mut model),
										con.cmp,
										con.lbl.clone(),
									)?
								} else {
									t.clone()
								})
							})
							.try_collect()?,
					},
					..con
				};

				model.add_constraint(con)?;
				if is_last_term {
					let n = model.cons.len();
					model.cons.swap(n - 1, n - 2);
				}
			} else {
				model.add_constraint(con)?;
			}

			Ok(())
		})?;

		let cons = model.cons.iter().cloned();
		let mut model = Model {
			cons: vec![],
			..model
		};

		cons.into_iter().try_for_each(|con| {
			let con =
				if con.exp.terms.len() >= 2
					&& con.exp.terms.iter().all(|t| {
						t.c.is_positive() && matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_)))
					}) && con.cmp.is_ineq()
				{
					let dom = Dom::from_slice(
						&con.exp
							.terms
							.iter()
							.map(|t| t.dom().into_iter())
							.multi_cartesian_product()
							.map(|cs| cs.into_iter().reduce(C::add).unwrap())
							.sorted()
							.dedup()
							.collect_vec(),
					);

					let y = model
						.new_var_from_dom(
							dom,
							model.config.add_consistency,
							Some(IntVarEnc::Bin(None)),
							con.lbl.as_ref().map(|lbl| format!("last-lhs-{lbl}")),
						)
						.unwrap();

					model.add_constraint(Lin {
						exp: LinExp {
							terms: con
								.exp
								.terms
								.iter()
								.cloned()
								.chain(vec![Term::new(-C::one(), y.clone())])
								.collect(),
						},
						cmp: Comparator::Equal,
						k: C::zero(),
						lbl: con.lbl.as_ref().map(|lbl| format!("last-{lbl}")),
					})?;

					Lin {
						exp: LinExp {
							terms: vec![Term::from(y)],
						},
						..con.clone()
					}
				} else {
					con
				};
			model.add_constraint(con)?;
			Ok(())
		})?;

		Ok(model)

		/*
		if model.cons.len() == 1 {

				// let (terms, couplings) = con
				// 	.exp
				// 	.terms
				// 	.iter()
				// 	.with_position()
				// 	.map(
				// 		|(_p, t)| -> Result<(Term<Lit, C>, Model<Lit, C>), Unsatisfiable> {
				// 			Ok(if let Some(IntVarEnc::Ord(None)) = t.x.borrow().e.clone() {
				// 				// is_last_term = matches!(p, Position::Last);
				// 				let (new_t, m) = t.clone().encode_bin(
				// 					Some(&mut model),
				// 					con.cmp,
				// 					con.lbl.clone(),
				// 				)?;
				// 				// let new_id = IntVarId(model.num_var + new_t.x.borrow().id.0);
				// 				// new_t.x.borrow_mut().id =

				// 				// model.num_var += 1;
				// 				(new_t, m)
				// 			} else {
				// 				(t.clone(), Model::default())
				// 			})
				// 		},
				// 	)
				// 	.process_results(|x| x.unzip())?;

				// for t in terms {
				// 	// let new_id = IntVarId(x.borrow().id.clone().0 + self.num_var);
				// 	let new_id = IntVarId(model.num_var);
				// 	t.x.borrow_mut().id = new_id;
				// }

				// let mut model = Model {
				// 	cons: vec![Lin {
				// 		exp: LinExp { terms },
				// 		..con
				// 	}],
				// 	..model
				// };
				// model.extend(std::iter::once(couplings));
				// Ok(model)
			// } else {
				// Ok(model)
			// }
		// // let mut is_last_term = false;
		// // if mixed encoding of more than 2 terms, couple each xi:O<=yi:B
		// } else {
			// model.fold(self)
		// }

		// Ok(Model {
		// 	cons: if is_last_term {
		// 		[new_con].into_iter().chain(model.cons).collect()
		// 	} else {
		// 		model.cons.into_iter().chain([new_con]).collect()
		// 	},
		// 	..model
		// })
		*/
	}
}

#[derive(Default, Debug)]
pub struct ModelDecomposer<Lit: Literal, C: Coefficient> {
	pub(crate) spec: Option<HashMap<IntVarId, IntVarEnc<Lit, C>>>,
}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for ModelDecomposer<Lit, C> {
	fn decompose(&self, model: Model<Lit, C>) -> Result<Model<Lit, C>, Unsatisfiable> {
		let ModelConfig {
			equalize_ternaries,
			cutoff,
			..
		} = model.config.clone();

		// let mut num_var = None;
		model
			.decompose_with(Some(&LinDecomposer {}))?
			.decompose_with(Some(&EncSpecDecomposer {
				cutoff,
				spec: self.spec.clone(),
			}))?
			.decompose_with(
				equalize_ternaries
					.then(EqualizeTernsDecomposer::default)
					.as_ref(),
			)?
			.decompose_with(Some(&ScmDecomposer::default()))
	}
}

#[derive(Default, Debug)]
pub struct LinDecomposer {}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for LinDecomposer {
	fn decompose(
		&self,
		model: Model<Lit, C>,
		// con: Lin<Lit, C>,
		// num_var: usize,
		// model_config: &ModelConfig<C>,
		// cse: Option<Cse<Lit, C>>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		// let cons = model.cons.iter().cloned().collect_vec();
		let Model {
			cons,
			num_var,
			obj,
			config,
			cse,
		} = model;

		let lin_decomp = cons.into_iter().try_fold(
			Model {
				cons: vec![],
				num_var,
				obj,
				config,
				cse,
			},
			|mut model, con| {
				let decomp = match con.exp.terms[..] {
					[] => {
						let con_model = model.branch(con);
						con_model
							.check_assignment(&Assignment(HashMap::default()), None)
							.map(|_| con_model)
							.map_err(|_| Unsatisfiable)
					}
					_ if con.exp.terms.len() <= 2
						|| con.is_tern() || model.config.decomposer == Decomposer::Rca =>
					{
						Ok(model.branch(con))
					}
					_ => match model.config.decomposer {
						Decomposer::Bdd => BddEncoder::default().decompose(model.branch(con)),
						Decomposer::Gt => TotalizerEncoder::default().decompose(model.branch(con)),
						Decomposer::Swc => SwcEncoder::default().decompose(model.branch(con)),
						Decomposer::Rca => unreachable!(),
					},
				}?;
				model.extend(std::iter::once(decomp));
				Ok(model)
			},
		)?;
		Ok(lin_decomp)
	}
}

#[derive(Default, Debug)]
pub struct ScmDecomposer {}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for ScmDecomposer {
	fn decompose(&self, model: Model<Lit, C>) -> Result<Model<Lit, C>, Unsatisfiable> {
		let cons = model.cons.iter().cloned();
		let mut model = Model {
			cons: vec![],
			..model
		};
		cons.into_iter().try_for_each(|con| {
			let terms = con
				.exp
				.terms
				.iter()
				.cloned()
				.with_position()
				.map(|(p, t)| {
					if let Some(IntVarEnc::Bin(None)) = t.x.borrow().e.clone() {
						if matches!(p, Position::Last) {
							Ok(t.clone())
						} else {
							t.clone()
								.encode_bin(Some(&mut model), con.cmp, con.lbl.clone())
						}
					} else {
						Ok(t.clone())
					}
				})
				.try_collect()?;
			model.add_constraint(Lin {
				exp: LinExp { terms },
				..con
			})
		})?;
		Ok(model)

		// Ok({
		// 	let (terms, couplings): (Vec<Term<Lit, C>>, Model<Lit, C>) =
		// 		con.exp.terms.iter().map(|t| {}).unzip();
		// 	[
		// 		couplings,
		// 		Model {
		// 			cons: vec![Lin {
		// 				exp: LinExp { terms },
		// 				..con
		// 			}],
		// 			..model
		// 		},
		// 	]
		// 	.into_iter()
		// 	.collect()
		// })
		// })
		// .collect()
		// let (terms, couplings) = con
		//     .exp
		//     .terms
		//     .iter()
		//     .with_position()
		//     .map(|(_p, t)| {
		//         Ok(if let Some(IntVarEnc::Ord(None)) = t.x.borrow().e.clone() {
		//             // is_last_term = matches!(p, Position::Last);
		//             let (new_t, m) = t.clone().encode_bin(con.cmp, con.lbl.clone())?;
		//             new_t.x.borrow_mut().id =
		//                 IntVarId(model.num_var + new_t.x.borrow().id.0);
		//             model.num_var += 1;
		//             (new_t, m)
		//         } else {
		//             (t.clone(), Model::default())
		//         })
		//     })
		// .process_results(|x| x.unzip())?;
	}
}

/*
impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for ScmDecomposer {
	fn decompose(&self, mut model: Model<Lit, C>) -> Result<Model<Lit, C>, Unsatisfiable> {
		// let (terms, couplings) = con
		//     .exp
		//     .terms
		//     .iter()
		//     .with_position()
		//     .map(|(_p, t)| {
		//         Ok(if let Some(IntVarEnc::Ord(None)) = t.x.borrow().e.clone() {
		//             // is_last_term = matches!(p, Position::Last);
		//             let (new_t, m) = t.clone().encode_bin(con.cmp, con.lbl.clone())?;
		//             new_t.x.borrow_mut().id =
		//                 IntVarId(model.num_var + new_t.x.borrow().id.0);
		//             model.num_var += 1;
		//             (new_t, m)
		//         } else {
		//             (t.clone(), Model::default())
		//         })
		//     })
		// .process_results(|x| x.unzip())?;

		println!("scm model = {}", model);

		if model.cons.len() == 1 {
			let con = model.cons.first().unwrap().clone();

			Ok({
				let (terms, couplings): (Vec<Term<Lit, C>>, Model<Lit, C>) = con
					.exp
					.terms
					.iter()
					.map(|t| {
						if con
							.exp
							.terms
							.iter()
							.all(|t| matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_))))
						{
							let (new_t, mut m) =
								t.clone().encode_bin(con.cmp, con.lbl.clone()).unwrap();
							// let new_id = IntVarId(model.num_var + new_t.x.borrow().id.0);
							let new_id = if m.num_var == 0 {
								model.num_var += 1;
								IntVarId(model.num_var)
							} else {
								model.num_var += 1;
								let new_id = IntVarId(model.num_var + new_t.x.borrow().id.0);
								new_id
							};
							// let new_id = IntVarId(m.num_var + new_t.x.borrow().id.0);
							// let new_id = IntVarId(m.num_var + new_t.x.borrow().id.0);
							new_t.x.borrow_mut().id = new_id;
							// model.num_var += m.num_var;
							// m.num_var = model.num_var;
							(new_t, m)
						} else {
							(t.clone(), Model::default())
						}
					})
					.unzip();
				[
					couplings,
					Model {
						cons: vec![Lin {
							exp: LinExp { terms },
							..con
						}],
						..model
					},
				]
				.into_iter()
				.collect()
			})
		// .process_results(|x| x.unzip())
		// .map(|x| x?)
		} else {
			model.fold(self)
		}
	}
}
*/

/*
impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for LinDecomposer {
	fn decompose(
		&self,
		model: Model<Lit, C>,
		// con: Lin<Lit, C>,
		// num_var: usize,
		// model_config: &ModelConfig<C>,
		// cse: Option<Cse<Lit, C>>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		// model.decompose_with( Some(self))
		// let Model { cons, .. } = model;
		model
			.cons
			.iter()
			.cloned()
			.map(|con| match &con.exp.terms[..] {
				[] => con
					.check(&Assignment(HashMap::default()), None)
					.map(|_| Model {
						cons: vec![con],
						..model.clone()
					})
					.map_err(|_| Unsatisfiable),
				_ if con.exp.terms.len() <= 2
					|| con.is_tern() || model.config.decomposer == Decomposer::Rca =>
				{
					// let mut model = Model::<Lit, C>::new(num_var, model_config);
					// model.add_constraint(con)?;
					// Ok(model)
					Ok(Model {
						cons: vec![con],
						..model.clone()
					})
				}
				_ => {
					// let con_model = Model::from(con);
					let con_model = Model {
						cons: vec![con],
						..model.clone()
					};
					match con_model.config.decomposer {
						Decomposer::Bdd => BddEncoder::default().decompose(con_model),
						Decomposer::Gt => TotalizerEncoder::default().decompose(con_model),
						Decomposer::Swc => SwcEncoder::default().decompose(con_model),
						Decomposer::Rca => unreachable!(),
					}
				}
			})
			.collect()
	}
}
*/
