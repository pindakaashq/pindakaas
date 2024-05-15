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
	prop: Option<Ident>,
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

	let assumptions = if opts.assumptions {
		let fail_ident = format_ident!("{}Failed", ident);
		quote! {
			impl crate::solver::SolveAssuming for #ident {
				type FailFn = #fail_ident;

				fn solve_assuming<
					I: IntoIterator<Item = crate::Lit>,
					SolCb: FnOnce(&Self::ValueFn),
					FailCb: FnOnce(&Self::FailFn),
				>(
					&mut self,
					assumptions: I,
					on_sol: SolCb,
					on_fail: FailCb,
				) -> crate::solver::SolveResult {
					use crate::solver::Solver;
					for i in assumptions {
						unsafe { #krate::ipasir_assume(#ptr, i.into()) }
					}
					match self.solve(on_sol) {
						crate::solver::SolveResult::Unsat => {
							let fail_fn = #fail_ident { ptr: #ptr };
							on_fail(&fail_fn);
							crate::solver::SolveResult::Unsat
						}
						r => r,
					}
				}
			}

			pub struct #fail_ident {
				ptr: *mut std::ffi::c_void,
			}
			impl crate::solver::FailedAssumtions for #fail_ident {
				fn fail(&self, lit: crate::Lit) -> bool {
					let lit: i32 = lit.into();
					let failed = unsafe { #krate::ipasir_failed(#ptr, lit) };
					failed != 0
				}
			}
		}
	} else {
		quote!()
	};

	let term_callback = if opts.term_callback {
		quote! {
			impl crate::solver::TermCallback for #ident {
				fn set_terminate_callback<F: FnMut() -> crate::solver::SlvTermSignal>(
					&mut self,
					cb: Option<F>,
				) {
					if let Some(mut cb) = cb {
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
					} else {
						unsafe { #krate::ipasir_set_terminate(#ptr, std::ptr::null_mut(), None) }
					}
				}
			}
		}
	} else {
		quote!()
	};

	let learn_callback = if opts.learn_callback {
		quote! {
			impl crate::solver::LearnCallback for #ident {
				fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = crate::Lit>)>(
					&mut self,
					cb: Option<F>,
				) {
					const MAX_LEN: std::ffi::c_int = 512;
					if let Some(mut cb) = cb {
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
					} else {
						unsafe { #krate::ipasir_set_learn(#ptr, std::ptr::null_mut(), MAX_LEN, None) }
					}
				}
			}
		}
	} else {
		quote!()
	};

	let sol_ident = format_ident!("{}Sol", ident);
	let ipasir_up = if opts.ipasir_up {
		let prop_ident = format_ident!("{}Prop", ident);
		let prop_member = match opts.prop {
			Some(x) => quote! { self. #x },
			None => quote! { self.prop },
		};
		quote! {
			#[cfg(feature = "ipasir-up")]
			pub(crate) struct #prop_ident {
				/// Rust Propagator Storage
				prop: Box<crate::solver::libloading::IpasirPropStore>,
				/// C Wrapper Object
				wrapper: *mut std::ffi::c_void,
			}

			#[cfg(feature = "ipasir-up")]
			impl Drop for #prop_ident {
				fn drop(&mut self) {
					unsafe { #krate::ipasir_prop_release(self.wrapper) };
				}
			}

			#[cfg(feature = "ipasir-up")]
			impl #prop_ident {
				pub(crate) fn new(prop: Box<dyn crate::solver::Propagator>, slv: *mut dyn crate::solver::SolvingActions) -> Self {
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
				fn set_external_propagator(
					&mut self,
					prop: Option<Box<dyn crate::solver::Propagator>>,
				) -> Option<Box<dyn crate::solver::Propagator>> {
					// Store old propagator (setting member to None)
					let old = #prop_member.take();
					// Disconnect old propagator (if one was set)
					if old.is_some() {
						unsafe { #krate::ipasir_disconnect_external_propagator( #ptr ) };
					}
					// If new propagator, set it now
					if let Some(p) = prop {
						#prop_member = Some(Box::new(#prop_ident ::new(p, (self as *mut _))));
						unsafe { #krate::ipasir_connect_external_propagator( #ptr, #prop_member .as_ref().unwrap().wrapper ) };
					}
					// Return old propagator
					if let Some(mut old) = old {
						// Replace rust propagator with dummy to not interfere with Drop
						let mut prop: Box<dyn crate::solver::Propagator> = Box::new(crate::solver::libloading::NoProp{});
						std::mem::swap(&mut old.prop.prop, &mut prop);
						Some(prop)
					} else {
						None
					}
				}

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
			impl crate::solver::PropagatorAccess for #ident {
				fn propagator<P: crate::solver::Propagator + 'static>(&self) -> Option<&P> {
					#prop_member.as_ref().map(|p| p.prop.prop.as_any().downcast_ref()).flatten()
				}
			}

			#[cfg(feature = "ipasir-up")]
			impl crate::solver::MutPropagatorAccess for #ident {
				fn propagator_mut<P: crate::solver::Propagator + 'static>(&mut self) -> Option<&mut P> {
					#prop_member.as_mut().map(|p| p.prop.prop.as_mut_any().downcast_mut()).flatten()
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

			pub struct #sol_ident {
				ptr: *mut std::ffi::c_void,
				#[cfg(feature = "ipasir-up")]
				prop: Option<*mut std::ffi::c_void>,
			}
			impl #ident {
				fn solver_solution_obj(&mut self) -> #sol_ident {
					#sol_ident {
						ptr: self.ptr,
						#[cfg(feature = "ipasir-up")]
						prop: if let Some(p) = #prop_member .as_mut() {
							Some((&mut (*p.prop)) as *mut _ as *mut std::ffi::c_void)
						} else {
							None
						},
					}
				}
			}
			#[cfg(feature = "ipasir-up")]
			impl crate::solver::PropagatorAccess for #sol_ident {
				fn propagator<P: crate::solver::Propagator + 'static>(&self) -> Option<&P> {
					if let Some(prop) = self.prop {
						let prop = unsafe { &*(prop as *const crate::solver::libloading::IpasirPropStore) };
						prop.prop.as_any().downcast_ref()
					} else {
						None
					}
				}
			}
			#[cfg(feature = "ipasir-up")]
			impl crate::solver::MutPropagatorAccess for #sol_ident {
				fn propagator_mut<P: crate::solver::Propagator + 'static>(&mut self) -> Option<&mut P> {
					if let Some(prop) = self.prop {
						let prop = unsafe { &mut *(prop as *mut crate::solver::libloading::IpasirPropStore) };
						prop.prop.as_mut_any().downcast_mut()
					} else {
						None
					}
				}
			}
		}
	} else {
		quote! {
			pub struct #sol_ident {
				ptr: *mut std::ffi::c_void,
			}
			impl #ident {
				fn solver_solution_obj(&self) -> #sol_ident {
					#sol_ident { ptr: self.ptr }
				}
			}
		}
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

			type CondDB = Self;
			fn with_conditions(&mut self, conditions: Vec<crate::Lit>) -> crate::ConditionalDatabase<Self::CondDB> {
				crate::ConditionalDatabase {
					db: self,
					conditions,
				}
			}
		}

		impl crate::solver::NextVarRange for #ident {
			fn next_var_range(&mut self, size: usize) -> Option<crate::helpers::VarRange> {
				#vars .next_var_range(size)
			}
		}

		impl crate::solver::Solver for #ident {
			type ValueFn = #sol_ident;

			fn signature(&self) -> &str {
				unsafe { std::ffi::CStr::from_ptr(#krate::ipasir_signature()) }
					.to_str()
					.unwrap()
			}

			fn solve<SolCb: FnOnce(&Self::ValueFn)>(
				&mut self,
				on_sol: SolCb,
			) -> crate::solver::SolveResult {
				let res = unsafe { #krate::ipasir_solve( #ptr ) };
				match res {
					10 => {
						// 10 -> Sat
						let model = self.solver_solution_obj();
						on_sol(&model);
						crate::solver::SolveResult::Sat
					}
					20 => crate::solver::SolveResult::Unsat, // 20 -> Unsat
					_ => {
						debug_assert_eq!(res, 0); // According to spec should be 0, unknown
						crate::solver::SolveResult::Unknown
					}
				}
			}
		}

		impl crate::Valuation for #sol_ident {
			fn value(&self, lit: crate::Lit) -> Option<bool> {
				let var: i32 = lit.var().into();
				// WARN: Always ask about variable (positive) literal, otherwise solvers sometimes seem incorrect
				let ret = unsafe { #krate::ipasir_val(self.ptr, var) };
				match ret {
					_ if ret == var => Some(!lit.is_negated()),
					_ if ret == -var => Some(lit.is_negated()),
					_ => {
						debug_assert_eq!(ret, 0); // zero according to spec, both value are valid
						None
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

fn default_true() -> bool {
	true
}
