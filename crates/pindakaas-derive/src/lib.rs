use darling::FromDeriveInput;
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, DeriveInput, Ident};

#[derive(FromDeriveInput)]
#[darling(attributes(ipasir))]
struct IpasirOpts {
	krate: Ident,
	#[darling(default)]
	ptr: Option<Ident>,
	#[darling(default)]
	vars: Option<Ident>,
	#[darling(default)]
	assumptions: bool,
	#[darling(default)]
	learn_callback: bool,
	#[darling(default)]
	learn_callback_ident: Option<Ident>,
	#[darling(default)]
	term_callback: bool,
	#[darling(default)]
	term_callback_ident: Option<Ident>,
	#[darling(default)]
	ipasir_up: bool,
	#[darling(default = "default_true")]
	has_default: bool,
}

#[proc_macro_derive(IpasirSolver, attributes(ipasir))]
pub fn ipasir_solver_derive(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input);
	let opts = IpasirOpts::from_derive_input(&input).expect("Invalid options");
	let DeriveInput { ident, .. } = input;

	let krate = opts.krate;
	let ptr_attr = match opts.ptr {
		Some(x) => quote! {  #x },
		None => quote! { ptr },
	};
	let ptr = quote! { self. #ptr_attr };
	let vars = match opts.vars.clone() {
		Some(x) => quote! { self. #x },
		None => quote! { self.vars },
	};
	let sol_ident = format_ident!("{}Sol", ident);

	let (assumptions, fail_type) = if opts.assumptions {
		let fail_ident = format_ident!("{}Failed", ident);
		(
			quote! {
				impl #ident {
					pub fn solver_fail_obj(&self) -> #fail_ident {
						#fail_ident { slv: self }
					}
				}

				impl crate::solver::SolveAssuming for #ident {
					#[expect(refining_impl_trait)]
					fn solve_assuming<I: IntoIterator<Item = crate::Lit>>(
						&mut self,
						assumptions: I,
					) -> crate::solver::SolveResult<#sol_ident <'_>, #fail_ident <'_>> {
						use crate::solver::Solver;
						for i in assumptions {
							unsafe { #krate::ipasir_assume(#ptr, i.into()) }
						}
						self.solve()
					}
				}

				pub struct #fail_ident <'a> {
					slv: &'a #ident,
				}
				impl crate::solver::FailedAssumtions for #fail_ident <'_> {
					fn fail(&self, lit: crate::Lit) -> bool {
						let lit: i32 = lit.into();
						let failed = unsafe { #krate::ipasir_failed( self.slv. #ptr_attr, lit) };
						failed != 0
					}
				}
			},
			quote! { #fail_ident <'_> },
		)
	} else {
		(
			quote! {
				impl #ident {
					fn solver_fail_obj(&self) {}
				}
			},
			quote! { () },
		)
	};

	let term_callback = if opts.term_callback {
		let term_cb = match opts.term_callback_ident {
			Some(x) => quote! { self. #x },
			None => quote! { self.term_cb },
		};
		quote! {
			impl crate::solver::TermCallback for #ident {
				fn set_terminate_callback<F: FnMut() -> crate::solver::SlvTermSignal + 'static>(
					&mut self,
					cb: Option<F>,
				) {
					if let Some(mut cb) = cb {
						let wrapped_cb = move || -> std::ffi::c_int {
							match cb() {
								crate::solver::SlvTermSignal::Continue => std::ffi::c_int::from(0),
								crate::solver::SlvTermSignal::Terminate => std::ffi::c_int::from(1),
							}
						};
						let trampoline = crate::solver::get_trampoline0(&wrapped_cb);
						#term_cb = crate::solver::FFIPointer::new(wrapped_cb);
						unsafe {
							#krate::ipasir_set_terminate(
								#ptr,
								#term_cb .get_ptr(),
								Some(trampoline),
							)
						}
					} else {
						#term_cb = crate::solver::FFIPointer::default();
						unsafe { #krate::ipasir_set_terminate(#ptr, std::ptr::null_mut(), None) }
					}
				}
			}
		}
	} else {
		quote!()
	};

	let learn_callback = if opts.learn_callback {
		let learn_cb = match opts.learn_callback_ident {
			Some(x) => quote! { self. #x },
			None => quote! { self.learn_cb },
		};

		quote! {
			impl crate::solver::LearnCallback for #ident {
				fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = crate::Lit>) + 'static>(
					&mut self,
					cb: Option<F>,
				) {
					const MAX_LEN: std::ffi::c_int = 512;
					if let Some(mut cb) = cb {
						let wrapped_cb = move |clause: *const i32| {
							let mut iter = crate::solver::ExplIter(clause)
								.map(|i: i32| crate::Lit(std::num::NonZeroI32::new(i).unwrap()));
							cb(&mut iter)
						};
						let trampoline = crate::solver::get_trampoline1(&wrapped_cb);
						#learn_cb = crate::solver::FFIPointer::new(wrapped_cb);
						unsafe {
							#krate::ipasir_set_learn(
								#ptr,
								#learn_cb .get_ptr(),
								MAX_LEN,
								Some(trampoline),
							)
						}
					} else {
						#learn_cb = crate::solver::FFIPointer::default();
						unsafe { #krate::ipasir_set_learn(#ptr, std::ptr::null_mut(), MAX_LEN, None) }
					}
				}
			}
		}
	} else {
		quote!()
	};

	let ipasir_up = if opts.ipasir_up {
		let prop_slv = format_ident!("Propagating{}", ident);
		quote! {
			#[cfg(feature = "external-propagation")]
			pub struct #prop_slv<P> {
				container: Box<crate::solver::propagation::IpasirPropStore <P, #ident>>,
			}

			#[cfg(feature = "external-propagation")]
			impl<P: crate::solver::propagation::Propagator> crate::solver::propagation::WithPropagator<P> for #ident {
				type PropSlv = #prop_slv <P>;
				fn with_propagator(self, prop: P) -> Self::PropSlv {
					let is_lazy = prop.is_check_only();
					let forgettable_reasons = prop.reason_persistence() == crate::solver::propagation::ClausePersistence::Forgettable;
					let notify_fixed = prop.enable_persistent_assignments();

					let mut container = Box::new(crate::solver::propagation::IpasirPropStore::new(prop, self));
					unsafe {
						#krate::ipasir_connect_external_propagator(
							container.slv. #ptr_attr,
							&mut *container as *mut _ as *mut std::ffi::c_void,
							crate::solver::propagation::ipasir_notify_assignments_cb::<P, #ident>,
							crate::solver::propagation::ipasir_notify_new_decision_level_cb::<P, #ident>,
							crate::solver::propagation::ipasir_notify_backtrack_cb::<P, #ident>,
							crate::solver::propagation::ipasir_check_model_cb::<P, #ident>,
							crate::solver::propagation::ipasir_has_external_clause_cb::<P, #ident>,
							crate::solver::propagation::ipasir_add_external_clause_lit_cb::<P, #ident>,
							is_lazy,
							forgettable_reasons,
							notify_fixed,
							crate::solver::propagation::ipasir_decide_cb::<P, #ident>,
							crate::solver::propagation::ipasir_propagate_cb::<P, #ident>,
							crate::solver::propagation::ipasir_add_reason_clause_lit_cb::<P, #ident>,
							crate::solver::propagation::ipasir_notify_persistent_assignments_cb::<P, #ident>,
						)
					};

					#prop_slv { container }
				}
			}

			#[cfg(feature = "external-propagation")]
			impl<P: crate::solver::propagation::Propagator> crate::solver::propagation::PropagatingSolver<P> for #prop_slv <P> {
				type Slv = #ident;

				fn access_solving(&mut self) -> (&mut dyn crate::solver::propagation::SolvingActions, &mut P) {
					(&mut self.container.slv, &mut self.container.prop)
				}

				fn add_observed_var(&mut self, var: crate::Var) {
					unsafe { #krate::ipasir_add_observed_var( self.container.slv. #ptr_attr, var.0.get()) };
				}

				fn into_parts(self) -> (Self::Slv, P) {
					unsafe { #krate::ipasir_disconnect_external_propagator( self.container.slv. #ptr_attr ) };
					(self.container.slv, self.container.prop)
				}

				fn propagator(&self) -> &P {
					&self.container.prop
				}

				fn propagator_mut(&mut self) -> &mut P {
					&mut self.container.prop
				}

				fn remove_observed_var(&mut self, var: crate::Var) {
					unsafe { #krate::ipasir_remove_observed_var( self.container.slv. #ptr_attr, var.0.get()) };
				}

				fn reset_observed_vars(&mut self) {
					unsafe { #krate::ipasir_reset_observed_vars( self.container.slv. #ptr_attr ) };
				}

				fn solve(&mut self) -> (&P, crate::solver::SolveResult<#sol_ident <'_>, #fail_type >) {
					use crate::solver::Solver;
					let res = self.container.slv.solve();
					(&self.container.prop, res)
				}

				#[expect(
					refining_impl_trait,
					reason = "user can use more specific type if needed"
				)]
				fn solve_assuming<I: IntoIterator<Item = crate::Lit>>(
					&mut self,
					assumptions: I,
				) -> (
					&P,
					crate::solver::SolveResult<#sol_ident <'_>, #fail_type >,
				) {
					use crate::solver::SolveAssuming;
					let res = self.container.slv.solve_assuming(assumptions);
					(&self.container.prop, res)
				}

				fn solver(&self) -> &Self::Slv {
					&self.container.slv
				}

				fn solver_mut(&mut self) -> &mut Self::Slv {
					&mut self.container.slv
				}
			}

			#[cfg(feature = "external-propagation")]
			impl<P> crate::ClauseDatabase for #prop_slv <P> {
				fn add_clause_from_slice(&mut self, clause: &[crate::Lit]) -> crate::Result {
					self.container.slv.add_clause_from_slice(clause)
				}

				fn new_var_range(&mut self, len: usize) -> crate::VarRange {
					self.container.slv.new_var_range(len)
				}
			}

			#[cfg(feature = "external-propagation")]
			impl crate::solver::propagation::SolvingActions for #ident {
				fn new_var(&mut self) -> crate::Var {
					let var = <Self as crate::ClauseDatabaseTools>::new_var(self);
					unsafe { #krate::ipasir_add_observed_var( #ptr , var.0.get()) };
					var
				}
				fn is_decision(&mut self, lit: crate::Lit) -> bool {
					unsafe { #krate::ipasir_is_decision( #ptr, lit.0.get() ) }
				}
			}

			#[cfg(feature = "external-propagation")]
			impl crate::solver::propagation::ExtendedSolvingActions for #ident {
				fn force_backtrack(&mut self, new_level: usize) {
					unsafe { #krate::ipasir_force_backtrack( #ptr, new_level ) }
				}
			}
		}
	} else {
		quote!()
	};

	let from_cnf = if opts.has_default {
		let var_member = match opts.vars {
			Some(x) => quote! { #x },
			None => quote! { vars },
		};

		quote! {
			impl From<&crate::Cnf> for #ident {
				fn from(value: &crate::Cnf) -> #ident {
					let mut slv: #ident = Default::default();
					slv. #var_member = value.nvar;
					for cl in value.iter() {
						// Ignore early detected unsatisfiability
						let _ = crate::ClauseDatabaseTools::add_clause(&mut slv, cl.iter().copied());
					}
					slv
				}
			}
		}
	} else {
		quote!()
	};

	quote! {
		impl Drop for #ident {
			fn drop(&mut self) {
				unsafe { #krate::ipasir_release( #ptr ) }
			}
		}

		impl crate::ClauseDatabase for #ident {
			fn add_clause_from_slice(&mut self, clause: &[crate::Lit]) -> crate::Result{
				let mut empty = true;
				for &lit in clause {
					unsafe { #krate::ipasir_add( #ptr , lit.into()) };
					empty = false;
				}
				unsafe { #krate::ipasir_add( #ptr , 0) };
				if empty {
					Err(crate::Unsatisfiable)
				} else {
					Ok(())
				}
			}

			fn new_var_range(&mut self, len: usize) -> crate::VarRange {
				#vars .next_var_range(len)
			}
		}

		impl crate::solver::Solver for #ident {
			fn signature(&self) -> &str {
				unsafe { std::ffi::CStr::from_ptr(#krate::ipasir_signature()) }
					.to_str()
					.unwrap()
			}

			#[expect(
				refining_impl_trait,
				reason = "user can use more specific type if needed"
			)]
			fn solve(&mut self) -> crate::solver::SolveResult<#sol_ident <'_>, #fail_type > {
				let res = unsafe { #krate::ipasir_solve( #ptr ) };
				match res {
					10 => {
						// 10 -> Sat
						let sol = self.solver_solution_obj();
						crate::solver::SolveResult::Satisfied(sol)
					}
					20 => {
						// 20 -> Unsat
						let fail = self.solver_fail_obj();
						crate::solver::SolveResult::Unsatisfiable(fail)
					},
					_ => {
						debug_assert_eq!(res, 0); // According to spec should be 0, unknown
						crate::solver::SolveResult::Unknown
					}
				}
			}
		}

		pub struct #sol_ident <'a> {
			slv: &'a #ident,
		}

		impl #ident {
			pub fn solver_solution_obj(&self) -> #sol_ident {
				#sol_ident { slv: self }
			}
		}

		impl crate::Valuation for #sol_ident <'_> {
			fn value(&self, lit: crate::Lit) -> bool {
				let var: i32 = lit.var().into();
				// WARN: Always ask about variable (positive) literal, otherwise solvers sometimes seem incorrect
				let ret = unsafe { #krate::ipasir_val( self.slv. #ptr_attr, var) };
				match ret {
					_ if ret == var => !lit.is_negated(),
					_ if ret == -var => lit.is_negated(),
					_ => {
						debug_assert_eq!(ret, 0); // zero according to spec, both value are valid
						false
					}
				}
			}
		}

		#from_cnf
		#assumptions
		#term_callback
		#learn_callback
		#ipasir_up
	}
	.into()
}

#[derive(FromDeriveInput)]
#[darling(attributes(python_clause_database))]
struct PythonClauseDatabaseOpts {
	/// The struct field which implements ClauseDatabase and ClauseDatabaseTools
	#[darling(default)]
	db: Option<Ident>,
	#[darling(default = "default_true")]
	tools: bool,
	#[darling(default)]
	solver: bool,
	#[darling(default)]
	assumptions: bool,
}

#[proc_macro_derive(PythonClauseDatabase, attributes(python_clause_database))]
pub fn python_clause_database_derive(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input);
	let opts = PythonClauseDatabaseOpts::from_derive_input(&input).expect("Invalid options");
	// TODO actually, I want to make this non-optional but I can't get an Ident for tuple struct field access
	let db = match opts.db {
		Some(x) => quote! {  self.#x },
		None => quote! { self.0 },
	};
	let DeriveInput { ident, .. } = input;

	let clause_database = quote! {
	#[pymethods]
	impl #ident {
		/// Add a clause to the clause database
		fn add_clause(&mut self, clause: Vec<Lit>) -> Result {
			base::ClauseDatabase::add_clause_from_slice(
				&mut #db,
				&clause.into_iter().map(|l| l.0).collect_vec(),
			)
			.map_err(|_| Unsatisfiable)
		}

		/// Add ``n`` variables to the clause database
	fn add_variables(&mut self, n: usize) -> VarRange {
			VarRange(
			base::ClauseDatabase::new_var_range(
							&mut #db,
							n
							))

								// TODO not sure if we can make a generator here, but perhaps that's
								// the proper translation to python
				// Lit(
				// base::ClauseDatabaseTools::new_vars(
				// 				&mut self.0
				// 			).into())
	}
		}
		};

	let tools = if opts.tools {
		quote! {
		#[pymethods]
		impl #ident {

					// TODO not entirely sure if this shouldn't also go to ClauseDatabase
		fn add_variable(&mut self) -> Lit {
				Lit(
				base::ClauseDatabaseTools::new_var(
								&mut #db
							).into())
		}

		///// TODO not sure if this one should be in ClauseDatabase or ClauseDatabaseTools
		///
		/// Encode a linear constraint over Boolean literals
							///
		/// The default arguments encode a clause: all coefficients are one, comparator is >=, and k = 1.
		/// Currently, the encoding is fixed as ``adder`` for PB and Cardinality constraints, and ``PairWise`` for AMOs/ALOs
		#[pyo3(signature=(literals, /, coefficients = None, comparator = Some(Comparator::GreaterEq), k = Some(1), conditions = vec![]))]
		fn add_linear(
			&mut self,
			literals: Vec<Lit>,
			coefficients: Option<Vec<Coeff>>,
			// TODO I'm not sure if adding Option is the best way to allow None to return default
			comparator: Option<Comparator>,
			k: Option<Coeff>,
						conditions: Vec<Lit>,
		) -> Result {
			let coefficients = coefficients.unwrap_or(literals.iter().map(|_| 1).collect());
			assert_eq!(
				coefficients.len(),
				literals.len(),
				"Literals and coefficients should have the same length"
			);
			let enc: LinearEncoder = LinearEncoder::default();
						let mut db = base::ClauseDatabaseTools::with_conditions(&mut #db, conditions.into_iter().map(|l| l.into()).collect());
			Ok(enc.encode(
				&mut db,
				&BoolLinear::new(
					BoolLinExp::from_slices(
						&coefficients,
						&literals.into_iter().map(|l| l.0).collect_vec(),
					),
					comparator.unwrap_or_default().into(),
					k.unwrap_or(1),
				),
			)?)
		}
		}
		}
	} else {
		quote! {()}
	};

	let solver = if opts.solver {
		let solve = if opts.assumptions {
			quote! {
						#[pyo3(signature=(assumptions = Vec::default()))]
			fn solve(&mut self, assumptions: Vec<Lit>) -> Option<bool> {
				match base::solver::SolveAssuming::solve_assuming(&mut #db, assumptions.into_iter().map(|l| l.into())) {
					base::solver::SolveResult::Satisfied(_) => Some(true),
					base::solver::SolveResult::Unsatisfiable(_) => Some(false),
					base::solver::SolveResult::Unknown => None,
				}
			}

					fn fail(&self, lit: Lit) -> bool {
						base::solver::FailedAssumtions::fail(&#db.solver_fail_obj(), lit.into())
					}
			}
		} else {
			quote! {
			fn solve(&mut self) -> Option<bool> {
				match base::solver::Solver::solve(&mut #db) {
					base::solver::SolveResult::Satisfied(_) => Some(true),
					base::solver::SolveResult::Unsatisfiable(_) => Some(false),
					base::solver::SolveResult::Unknown => None,
				}
			}
			}
		};

		quote! {
			#[pymethods]
			impl #ident {
		#[new]
		fn new() -> Self {
			Self::default()
		}
				#solve
						fn value(&self, lit: Lit) -> bool {
								base::Valuation::value(&#db.solver_solution_obj(), lit.into())
						}
		}
		}
	} else {
		quote! {()}
	};

	/*
	let conditional_database = if opts.conditions.unwrap_or(true) {
		let conditional_database_ident = format_ident!("Conditional{}", ident);
		quote! {

					#[pymethods]
					impl #ident {


				fn with_conditions(slf: PyRefMut<'_, Self>, conditions: Vec<Lit>) -> #conditional_database_ident {
					// TODO can't really use this, because can't keep impl ClauseDatabase as struct field ?
					// let c_db = base::ClauseDatabaseTools::with_conditions(
					// 	&mut self.0,
					// 	conditions.into_iter().map(|l| l.into()).collect(),
					// );
					Python::with_gil(move |py| {
						#conditional_database_ident(
							slf.into_py_any(py).unwrap().extract(py).unwrap(),
							conditions,
						)
					})
				}

					}

			// #[pyclass(extends = ClauseDatabase)] // TODO can't quite get this to work
				// #[new]
				// fn new(db: Py<#ident>, conditions: Vec<Lit>) -> (Self, ClauseDatabase) {
				// 	(Self(db, conditions), ClauseDatabase::new())
				// }
			// TODO this approach works but now we don't get Cnf's methods in ConditionalCnf
			#[pyclass]
						// #[derive(PythonClauseDatabaseTools)]
						// #[python_clause_database_tools(conditions = false)]
			struct #conditional_database_ident(Py<#ident>, Vec<Lit>);

			#[pymethods]
			impl #conditional_database_ident {

				fn __enter__(slf: Py<Self>) -> Py<Self> {
					slf
				}

				fn __exit__(&mut self, _exc_type: PyObject, _exc_value: PyObject, _traceback: PyObject) {}

				fn add_clause_from_slice(&mut self, clause: Vec<Lit>) -> Result {
					Python::with_gil(move |py| {
						self.0.borrow_mut(py).add_clause_from_slice(
							self.1
								.clone()
								.into_iter()
								.chain(clause.into_iter())
								.collect(),
						)
					})
				}

				fn new_var_range(&mut self, len: usize) -> VarRange {
					Python::with_gil(move |py| self.0.borrow_mut(py).new_var_range(len))
				}

							// TODO unfortunately, I can't derive ClauseDatabaseTools for Conditional*
							// b/c it has a Py<ClauseDatabase>, but we
														// only have to duplicate the methods once
								fn add_clause(&mut self, clause: Vec<Lit>) -> Result {
									self.add_clause_from_slice(clause)
								}

		fn add_variable(&mut self) -> Lit {
					Python::with_gil(move |py| {
						self.0.borrow_mut(py).add_variable()
					})
				}


		fn add_variables(&mut self, len: usize) -> VarRange {
					Python::with_gil(move |py| {
						self.0.borrow_mut(py).add_variables(len)
					})
		}

		#[pyo3(signature=(literals, /, coefficients = None, comparator = Some(Comparator::GreaterEq), k = Some(1)))]
		fn add_linear(
			&mut self,
			literals: Vec<Lit>,
			coefficients: Option<Vec<Coeff>>,
			comparator: Option<Comparator>,
			k: Option<Coeff>,
		) -> Result {
					Python::with_gil(move |py| {
						self.0.borrow_mut(py).extract().0.with_conditions(self.1).add_linear(literals, coefficients, comparator, k)
					})

				}
						}
				}
	} else {
		quote! {()}
	};
		*/

	quote! {
	#clause_database
	#tools
	#solver
	}
	.into()
}

fn default_true() -> bool {
	true
}
