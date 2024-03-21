use crate::{
	int::IntVarEnc, Coefficient, Comparator, IntLinExp as LinExp, Lin, Literal, Model, ModelConfig,
	Term, Unsatisfiable,
};

use super::Decompose;

#[derive(Default)]
pub struct ScmDecomposer {}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for ScmDecomposer {
	fn decompose(
		&self,
		con: Lin<Lit, C>,
		num_var: usize,
		model_config: &ModelConfig<C>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		let mut model = Model::<Lit, C>::new(num_var, model_config);
		if con
			.exp
			.terms
			.iter()
			.all(|t| matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_))))
		{
			let con = Lin {
				exp: LinExp {
					terms: con
						.exp
						.terms
						.iter()
						.map(|t| {
							if t.c.abs().is_one() {
								return t.clone();
							}
							let y = model
								.new_var(
									&t.dom(),
									model_config.add_consistency,
									Some(IntVarEnc::Bin(None)), // annotate to use BinEnc
									Some(format!("scm-{}·{}", t.c, t.x.borrow().lbl())),
								)
								.unwrap();

							model
								.add_constraint(Lin {
									exp: LinExp {
										terms: vec![t.clone(), Term::new(-C::one(), y.clone())],
									},
									cmp: Comparator::Equal,
									k: C::zero(),
									lbl: con.lbl.clone().map(|lbl| (format!("scm-{}", lbl))),
								})
								.unwrap();
							Term::from(y)
						})
						.collect(),
				},
				..con
			};
			model.add_constraint(con)?;
		} else {
			model.add_constraint(con)?;
		}

		Ok(model)
	}
}
