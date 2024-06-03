use std::collections::HashMap;

use itertools::{Itertools, Position};

use crate::{
	int::{con::LinCase, enc::IntVarEnc, model::USE_CHANNEL, Dom},
	Assignment, BddEncoder, Coeff, Comparator, Decomposer, IntLinExp as LinExp, IntVarId, Lin,
	Model, ModelConfig, SwcEncoder, Term, TotalizerEncoder, Unsatisfiable,
};

pub trait Decompose {
	fn decompose(&self, model: Model) -> Result<Model, Unsatisfiable>;
}

#[derive(Debug, Default)]
pub struct EqualizeTernsDecomposer {}

impl Decompose for EqualizeTernsDecomposer {
	fn decompose(&self, mut model: Model) -> Result<Model, Unsatisfiable> {
		let cons = model.cons.iter().cloned().collect_vec();
		Ok(Model {
			cons: cons
				.into_iter()
				.with_position()
				.flat_map(|(pos, con)| {
					if con.exp.terms.len() >= 2 && con.cmp.is_ineq() {
						if con
							.exp
							.terms
							.iter()
							.all(|t| matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_))))
						{
							if let Some((last, firsts)) = con.exp.terms.split_last() {
								let (lb, ub) = firsts
									.iter()
									.fold((0, 0), |(lb, ub), t| (lb + t.lb(), (ub + t.ub())));
								let (lb, ub) = match con.cmp {
									Comparator::LessEq => (lb, std::cmp::min(ub, -last.lb())),
									Comparator::GreaterEq => (std::cmp::max(-last.ub(), lb), ub),
									Comparator::Equal => unreachable!(),
								};
								let dom = Dom::from_bounds(lb, ub);
								if matches!(pos, Position::First | Position::Middle) {
									last.x.borrow_mut().dom = dom;

									vec![Lin {
										exp: LinExp {
											terms: firsts.iter().chain([last]).cloned().collect(),
										},
										cmp: Comparator::Equal,
										..con
									}]
								} else if con.exp.terms.len() >= 3 {
									// x+y<=z == x+y=z' /\ z' <= z
									let y = model
										.new_aux_var(
											dom,
											true,
											Some(IntVarEnc::Bin(None)),
											Some(String::from("last")),
										)
										.unwrap();

									vec![
										Lin {
											exp: LinExp {
												terms: firsts
													.iter()
													.chain([&Term::new(-1, y.clone())])
													.cloned()
													.collect(),
											},
											cmp: Comparator::Equal,
											k: 0,
											lbl: Some(String::from("last")),
										},
										Lin {
											exp: LinExp {
												terms: vec![Term::from(y), last.clone()],
											},
											cmp: con.cmp,
											..con
										},
									]
								} else {
									vec![con]
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
								if con.exp.terms[0].c == 1 && con.exp.terms[1].c == -1 && USE_CHANNEL
							) {
							con.exp.terms[0].x.borrow_mut().dom =
								con.exp.terms[1].x.borrow().dom.clone();
							vec![con]
						} else {
							vec![con]
						}
					// } else if con.exp.terms.len() == 2 && con.cmp == Comparator::Equal && false {
					// 	let z = con.exp.terms[0]
					// 		.clone()
					// 		.add(con.exp.terms[1].clone(), &mut model)
					// 		.unwrap();
					// 	vec![Lin {
					// 		exp: LinExp { terms: vec![z] },
					// 		cmp: con.cmp,
					// 		..con
					// 	}]
					} else {
						vec![con]
					}
				})
				.collect(),
			..model
		})
	}
}

#[derive(Debug, Default)]
pub struct EncSpecDecomposer {
	pub(crate) cutoff: Option<Coeff>,
	pub(crate) spec: Option<HashMap<IntVarId, IntVarEnc>>,
}

const COUPLE_SINGLE_VARS: bool = true;
impl Decompose for EncSpecDecomposer {
	fn decompose(&self, model: Model) -> Result<Model, Unsatisfiable> {
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
					// TODO experiment using density heuristic: || x.borrow().dom.density() > 0.3
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
							.map(|cs| cs.into_iter().sum())
							.sorted()
							.dedup()
							.collect_vec(),
					);

					let y = model
						.new_aux_var(
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
								.chain(vec![Term::new(-1, y.clone())])
								.collect(),
						},
						cmp: Comparator::Equal,
						k: 0,
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
	}
}

#[derive(Default, Debug)]
pub struct ModelDecomposer {
	pub(crate) spec: Option<HashMap<IntVarId, IntVarEnc>>,
}

impl Decompose for ModelDecomposer {
	fn decompose(&self, model: Model) -> Result<Model, Unsatisfiable> {
		let ModelConfig {
			equalize_ternaries,
			cutoff,
			..
		} = model.config.clone();

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

impl Decompose for LinDecomposer {
	fn decompose(&self, model: Model) -> Result<Model, Unsatisfiable> {
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
							.check_assignment(&Assignment(HashMap::default()))
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
						Decomposer::Gt(_) => {
							TotalizerEncoder::default().decompose(model.branch(con))
						}
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

impl Decompose for ScmDecomposer {
	fn decompose(&self, model: Model) -> Result<Model, Unsatisfiable> {
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
	}
}
