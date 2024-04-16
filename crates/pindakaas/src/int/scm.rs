use crate::{
	int::IntVarEnc, Coefficient, IntLinExp as LinExp, Lin, Literal, Model, ModelConfig,
	Unsatisfiable,
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
							t.clone()
								.encode_bin(Some(&mut model), con.cmp, con.lbl.clone())
								.unwrap()
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
