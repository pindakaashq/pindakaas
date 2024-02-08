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
	term_callback: bool,
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
	let ptr = match opts.ptr {
		Some(x) => quote! { self. #x },
		None => quote! { self.ptr },
	};
	let vars = match opts.vars.clone() {
		Some(x) => quote! { self. #x },
		None => quote! { self.vars },
	};

	let (mark_assumptions, set_assumptions, process_unsat) = if opts.assumptions {
		(
			quote! { impl crate::solver::SolveAssuming for #ident {} },
			quote! {
				if let Some(assumptions) = args.take_assumptions() {
					for i in assumptions {
						unsafe { #krate::ipasir_assume(#ptr, i.into()) }
					}
				}
			},
			quote! {
				if let Some(on_fail) = args.take_on_fail() {
					let fail_fn = |lit: crate::Lit| {
						let lit: i32 = lit.into();
						let failed = unsafe { #krate::ipasir_failed(#ptr, lit) };
						failed != 0
					};
					on_fail(&fail_fn);
				}
			},
		)
	} else {
		(quote!(), quote!(), quote!())
	};

	let (mark_term, set_term, reset_term) = if opts.term_callback {
		(
			quote! { impl crate::solver::CheckTermCallback for #ident{} },
			quote! {
				if let Some(cb) = args.take_term_callback() {
					let mut wrapped_cb = || -> std::ffi::c_int {
						match cb() {
							crate::solver::SlvTermSignal::Continue => std::ffi::c_int::from(0),
							crate::solver::SlvTermSignal::Terminate => std::ffi::c_int::from(1),
						}
					};
					let data = &mut wrapped_cb as *mut _ as *mut std::ffi::c_void;
					unsafe {
						#krate::ipasir_set_terminate(
							#ptr,
							data,
							Some(crate::solver::libloading::get_trampoline0(&wrapped_cb)),
						)
					}
				}
			},
			quote! { unsafe { #krate::ipasir_set_terminate(#ptr, std::ptr::null_mut(), None); } },
		)
	} else {
		(quote!(), quote!(), quote!())
	};

	let (mark_learn, set_learn, reset_learn) = if opts.learn_callback {
		(
			quote! { impl crate::solver::CallbackOnLearn for #ident {} },
			quote! {
				const MAX_LEN: std::ffi::c_int = 512;
				if let Some(mut cb) = args.take_learn_callback() {
					let mut wrapped_cb = |clause: *const i32| {
						let mut iter = crate::solver::libloading::ExplIter(clause)
							.map(|i: i32| crate::Lit(std::num::NonZeroI32::new(i).unwrap()));
						cb(&mut iter)
					};
					let data = &mut wrapped_cb as *mut _ as *mut std::ffi::c_void;
					unsafe {
						#krate::ipasir_set_learn(
							#ptr,
							data,
							MAX_LEN,
							Some(crate::solver::libloading::get_trampoline1(&wrapped_cb)),
						)
					}
				}
			},
			quote! { unsafe { #krate::ipasir_set_learn(#ptr, std::ptr::null_mut(), MAX_LEN, None) } },
		)
	} else {
		(quote!(), quote!(), quote!())
	};

	let (propagating_slv, connect_prop, disconnect_prop) = if opts.ipasir_up {
		let prop_ident = format_ident!("{}Prop", ident);
		(
			quote! {
				#[cfg(feature = "ipasir-up")]
				pub(crate) struct #prop_ident <'a> {
					/// Rust Propagator Storage
					prop: Box<crate::solver::libloading::IpasirPropStore<'a>>,
					/// C Wrapper Object
					wrapper: *mut std::ffi::c_void,
				}

				#[cfg(feature = "ipasir-up")]
				impl<'a> Drop for #prop_ident<'a> {
					fn drop(&mut self) {
						unsafe { #krate::ipasir_prop_release(self.wrapper) };
					}
				}

				#[cfg(feature = "ipasir-up")]
				impl<'a> #prop_ident<'a> {
					pub(crate) fn new(prop: &'a mut dyn crate::solver::Propagator, slv: *mut dyn crate::solver::SolvingActions) -> Self {
						// Construct wrapping structures
						let mut prop = Box::new(crate::solver::libloading::IpasirPropStore::new(prop, slv));
						let data = (&mut (*prop)) as *mut _;
						let wrapper = unsafe { #krate::ipasir_prop_init(data as *mut std::ffi::c_void) };

						// Set function pointers for methods
						unsafe { #krate::ipasir_prop_set_notify_assignment(wrapper, Some(crate::solver::libloading::ipasir_notify_assignment_cb)) };
						unsafe { #krate::ipasir_prop_set_notify_new_decision_level(wrapper, Some(crate::solver::libloading::ipasir_notify_new_decision_level_cb)) };
						unsafe { #krate::ipasir_prop_set_notify_backtrack(wrapper, Some(crate::solver::libloading::ipasir_notify_backtrack_cb)) };
						unsafe { #krate::ipasir_prop_set_check_model(wrapper, Some(crate::solver::libloading::ipasir_check_model_cb)) };
						unsafe { #krate::ipasir_prop_set_decide(wrapper, Some(crate::solver::libloading::ipasir_decide_cb)) };
						unsafe { #krate::ipasir_prop_set_propagate(wrapper, Some(crate::solver::libloading::ipasir_propagate_cb)) };
						unsafe { #krate::ipasir_prop_set_add_reason_clause_lit(wrapper, Some(crate::solver::libloading::ipasir_add_reason_clause_lit_cb)) };
						unsafe { #krate::ipasir_prop_set_has_external_clause(wrapper, Some(crate::solver::libloading::ipasir_has_external_clause_cb)) };
						unsafe { #krate::ipasir_prop_set_add_external_clause_lit(wrapper, Some(crate::solver::libloading::ipasir_add_external_clause_lit_cb)) };

						Self { prop, wrapper, }
					}
				}

				#[cfg(feature = "ipasir-up")]
				impl crate::solver::PropagatingSolver for #ident {
					fn add_observed_var(&mut self, var: crate::Var){
						unsafe { #krate::ipasir_add_observed_var( #ptr, var.0.get()) };
					}
					fn remove_observed_var(&mut self, var: crate::Var){
						unsafe { #krate::ipasir_remove_observed_var( #ptr, var.0.get()) };
					}
					fn reset_observed_vars(&mut self) {
						unsafe { #krate::ipasir_reset_observed_vars( #ptr ) };
					}
				}

				#[cfg(feature = "ipasir-up")]
				impl crate::solver::SolvingActions for #ident {
					fn new_var(&mut self) -> crate::Var {
						<#ident as crate::ClauseDatabase>::new_var(self)
					}
					fn add_observed_var(&mut self, var: crate::Var) {
						<#ident as crate::solver::PropagatingSolver>::add_observed_var(self, var)
					}
					fn is_decision(&mut self, lit: crate::Lit) -> bool {
						unsafe { #krate::ipasir_is_decision( #ptr, lit.0.get() ) }
					}
				}
			},
			quote! {
				let mut propagator_wrapper = None;
				if let Some(p) = args.take_propagator() {
					propagator_wrapper = Some(Box::new(#prop_ident ::new(p, (self as *mut _))));
					unsafe { #krate::ipasir_connect_external_propagator( #ptr, propagator_wrapper.as_ref().unwrap().wrapper ) };
				}
			},
			quote! {
				unsafe { #krate::ipasir_disconnect_external_propagator( #ptr ) };
				propagator_wrapper = None;
			},
		)
	} else {
		(quote!(), quote!(), quote!())
	};

	let from_cnf = if opts.has_default {
		let var_member = match opts.vars {
			Some(x) => quote! { #x },
			None => quote! { vars },
		};
		quote! {
			impl From<crate::Cnf> for #ident {
				fn from(value: crate::Cnf) -> #ident {
					let mut slv: #ident = Default::default();
					slv. #var_member = value.nvar;
					for cl in value.iter() {
						let _ = crate::ClauseDatabase::add_clause(&mut slv, cl.iter().copied());
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
			fn new_var(&mut self) -> crate::Var {
				#vars .next().expect("variable pool exhaused")
			}

			fn add_clause<I: IntoIterator<Item = crate::Lit>>(
				&mut self,
				clause: I,
			) -> crate::Result {
				let mut added = false;
				for lit in clause.into_iter() {
					unsafe { #krate::ipasir_add( #ptr , lit.into()) };
					added = true;
				}
				if added {
					unsafe { #krate::ipasir_add( #ptr , 0) };
				}
				Ok(())
			}
		}

		impl #ident {
			/// Return the next [`size`] variables that can be stored as an inclusive range.
			pub fn new_var_range(&mut self, size: usize) -> crate::helpers::VarRange {
				#vars .new_var_range(size).expect("variable pool exhaused")
			}
		}

		impl crate::solver::Solver for #ident {
			fn signature(&self) -> &str {
				unsafe { std::ffi::CStr::from_ptr(#krate::ipasir_signature()) }
					.to_str()
					.unwrap()
			}

			fn solve(&mut self, mut args: crate::solver::SolveArgs<Self>) -> crate::solver::SolveResult {
				#set_assumptions
				#connect_prop
				#set_learn
				#set_term
				let res = unsafe { #krate::ipasir_solve( #ptr ) };
				#reset_term
				#reset_learn
				#disconnect_prop
				match res {
					10 => {
						// 10 -> Sat
						if let Some(on_sol) = args.take_on_sol() {
							let val_fn = |lit: crate::Lit| {
								let var: i32 = lit.var().into();
								// WARN: Always ask about variable (positive) literal, otherwise solvers sometimes seem incorrect
								let ret = unsafe { #krate::ipasir_val( #ptr , var) };
								match ret {
									_ if ret == var => Some(!lit.is_negated()),
									_ if ret == -var => Some(lit.is_negated()),
									_ => {
										debug_assert_eq!(ret, 0); // zero according to spec, both value are valid
										None
									}
								}
							};
							on_sol(&val_fn);
						}
						crate::solver::SolveResult::Sat
					}
					20 => {
						// 20 -> Unsat
						#process_unsat
						crate::solver::SolveResult::Unsat
					}
					_ => {
						debug_assert_eq!(res, 0); // According to spec should be 0, unknown
						crate::solver::SolveResult::Unknown
					}
				}
			}
		}

		#from_cnf
		#mark_assumptions
		#mark_term
		#mark_learn
		#propagating_slv
	}
	.into()
}

fn default_true() -> bool {
	true
}
