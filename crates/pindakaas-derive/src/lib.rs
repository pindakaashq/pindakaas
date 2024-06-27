#![allow(clippy::manual_unwrap_or_default)] // TODO: Remove this when fixed in darling

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
						let trampoline = crate::solver::libloading::get_trampoline0(&wrapped_cb);
						#term_cb = crate::solver::libloading::FFIPointer::new(wrapped_cb);
						unsafe {
							#krate::ipasir_set_terminate(
								#ptr,
								#term_cb .get_ptr(),
								Some(trampoline),
							)
						}
					} else {
						#term_cb = crate::solver::libloading::FFIPointer::default();
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
							let mut iter = crate::solver::libloading::ExplIter(clause)
								.map(|i: i32| crate::Lit(std::num::NonZeroI32::new(i).unwrap()));
							cb(&mut iter)
						};
						let trampoline = crate::solver::libloading::get_trampoline1(&wrapped_cb);
						#learn_cb = crate::solver::libloading::FFIPointer::new(wrapped_cb);
						unsafe {
							#krate::ipasir_set_learn(
								#ptr,
								#learn_cb .get_ptr(),
								MAX_LEN,
								Some(trampoline),
							)
						}
					} else {
						#learn_cb = crate::solver::libloading::FFIPointer::default();
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
		let actions_ident = format_ident!("{}SolvingActions", ident);
		let prop_member = match opts.prop {
			Some(x) => quote! { self. #x },
			None => quote! { self.prop },
		};
		quote! {
			#[cfg(feature = "ipasir-up")]
			pub(crate) struct #prop_ident {
				/// Rust Propagator Storage
				prop: crate::solver::libloading::FFIPointer,
				access_prop: fn(*mut c_void) -> *mut dyn std::any::Any,
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
				pub(crate) fn new<P: crate::solver::Propagator + 'static>(prop: P, slv: #actions_ident) -> Self {
					// Construct wrapping structures
					let store = crate::solver::libloading::IpasirPropStore::new(prop, slv);
					let prop = crate::solver::libloading::FFIPointer::new(store);
					let access_prop = |x: *mut std::ffi::c_void| -> *mut dyn std::any::Any {
						let store = unsafe{ &mut *(x as *mut crate::solver::libloading::IpasirPropStore<P, #actions_ident>) } ;
					  (&mut store.prop) as *mut dyn std::any::Any
					};
					let wrapper = unsafe { #krate::ipasir_prop_init(prop.get_ptr()) };

					// Set function pointers for methods
					unsafe { #krate::ipasir_prop_set_notify_assignment(wrapper, Some(crate::solver::libloading::ipasir_notify_assignment_cb::<P, #actions_ident>)) };
					unsafe { #krate::ipasir_prop_set_notify_new_decision_level(wrapper, Some(crate::solver::libloading::ipasir_notify_new_decision_level_cb::<P, #actions_ident>)) };
					unsafe { #krate::ipasir_prop_set_notify_backtrack(wrapper, Some(crate::solver::libloading::ipasir_notify_backtrack_cb::<P, #actions_ident>)) };
					unsafe { #krate::ipasir_prop_set_check_model(wrapper, Some(crate::solver::libloading::ipasir_check_model_cb::<P, #actions_ident>)) };
					unsafe { #krate::ipasir_prop_set_decide(wrapper, Some(crate::solver::libloading::ipasir_decide_cb::<P, #actions_ident>)) };
					unsafe { #krate::ipasir_prop_set_propagate(wrapper, Some(crate::solver::libloading::ipasir_propagate_cb::<P, #actions_ident>)) };
					unsafe { #krate::ipasir_prop_set_add_reason_clause_lit(wrapper, Some(crate::solver::libloading::ipasir_add_reason_clause_lit_cb::<P, #actions_ident>)) };
					unsafe { #krate::ipasir_prop_set_has_external_clause(wrapper, Some(crate::solver::libloading::ipasir_has_external_clause_cb::<P, #actions_ident>)) };
					unsafe { #krate::ipasir_prop_set_add_external_clause_lit(wrapper, Some(crate::solver::libloading::ipasir_add_external_clause_lit_cb::<P, #actions_ident>)) };

					Self { prop, access_prop, wrapper, }
				}
			}

			#[cfg(feature = "ipasir-up")]
			impl crate::solver::PropagatingSolver for #ident {
				fn set_external_propagator<P: crate::solver::Propagator + 'static>(
					&mut self,
					prop: Option<P>,
				) {
					// Store old propagator (setting member to None)
					let old = #prop_member.take();
					// Disconnect old propagator (if one was set)
					if old.is_some() {
						unsafe { #krate::ipasir_disconnect_external_propagator( #ptr ) };
					}
					// If new propagator, set it now
					if let Some(p) = prop {
						#prop_member = Some(#prop_ident ::new(p, #actions_ident::new(#ptr, Arc::clone(&#vars))));
						unsafe { #krate::ipasir_connect_external_propagator( #ptr, #prop_member .as_ref().unwrap().wrapper ) };
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
					#prop_member.as_ref().map(|p| unsafe { &*(p.access_prop)(p.prop.get_ptr()) } .downcast_ref()).flatten()
				}
			}

			#[cfg(feature = "ipasir-up")]
			impl crate::solver::MutPropagatorAccess for #ident {
				fn propagator_mut<P: crate::solver::Propagator + 'static>(&mut self) -> Option<&mut P> {
					#prop_member.as_ref().map(|p| unsafe { &mut *(p.access_prop)(p.prop.get_ptr()) } .downcast_mut()).flatten()
				}
			}

			#[cfg(feature = "ipasir-up")]
			pub(crate) struct #actions_ident {
				ptr: *mut std::ffi::c_void,
				vars: Arc<Mutex<crate::VarFactory>>,
			}

			#[cfg(feature = "ipasir-up")]
			impl #actions_ident {
				pub fn new(ptr: *mut std::ffi::c_void, vars: Arc<Mutex<crate::VarFactory>>) -> Self {
					Self { ptr, vars }
				}
			}

			#[cfg(feature = "ipasir-up")]
			impl crate::solver::SolvingActions for #actions_ident {
				fn new_var(&mut self) -> crate::Var {
					self.vars.as_ref().lock().unwrap().next().expect("variable pool exhaused")
				}
				fn add_observed_var(&mut self, var: crate::Var) {
					unsafe { #krate::ipasir_add_observed_var( self.ptr, var.0.get()) };
				}
				fn is_decision(&mut self, lit: crate::Lit) -> bool {
					unsafe { #krate::ipasir_is_decision( self.ptr, lit.0.get() ) }
				}
			}

			pub struct #sol_ident {
				ptr: *mut std::ffi::c_void,
				#[cfg(feature = "ipasir-up")]
				prop: Option<*mut std::ffi::c_void>,
				#[cfg(feature = "ipasir-up")]
				access_prop: Option<fn(*mut std::ffi::c_void) -> *mut dyn std::any::Any>,
			}
			impl #ident {
				fn solver_solution_obj(&mut self) -> #sol_ident {
					#sol_ident {
						ptr: self.ptr,
						#[cfg(feature = "ipasir-up")]
						prop: #prop_member .as_mut().map(|p| p.prop.get_ptr()),
						#[cfg(feature = "ipasir-up")]
						access_prop: #prop_member .as_ref().map(|p| p.access_prop),
					}
				}
			}
			#[cfg(feature = "ipasir-up")]
			impl crate::solver::PropagatorAccess for #sol_ident {
				fn propagator<P: crate::solver::Propagator + 'static>(&self) -> Option<&P> {
					if let Some(prop) = self.prop {
						unsafe { &*(self.access_prop.unwrap())(prop) }.downcast_ref()
					} else {
						None
					}
				}
			}
			#[cfg(feature = "ipasir-up")]
			impl crate::solver::MutPropagatorAccess for #sol_ident {
				fn propagator_mut<P: crate::solver::Propagator + 'static>(&mut self) -> Option<&mut P> {
					if let Some(prop) = self.prop {
						unsafe { &mut *(self.access_prop.unwrap())(prop) }.downcast_mut()
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

	let new_var = if opts.ipasir_up {
		quote! {
			fn new_var(&mut self) -> crate::Var {
				#[cfg(feature = "ipasir-up")]
				let var = #vars .as_ref().lock().unwrap().next().expect("variable pool exhaused");
				#[cfg(not(feature = "ipasir-up"))]
				let var = #vars .next().expect("variable pool exhaused");
				var
			}
		}
	} else {
		quote! {
			fn new_var(&mut self) -> crate::Var {
				#vars .next().expect("variable pool exhaused")
			}
		}
	};

	let next_var_range = if opts.ipasir_up {
		quote! {
			fn next_var_range(&mut self, size: usize) -> Option<crate::helpers::VarRange> {
				#[cfg(feature = "ipasir-up")]
				let r = #vars .as_ref().lock().unwrap().next_var_range(size);
				#[cfg(not(feature = "ipasir-up"))]
				let r = #vars .next_var_range(size);
				r
			}
		}
	} else {
		quote! {
			fn next_var_range(&mut self, size: usize) -> Option<crate::helpers::VarRange> {
				#vars .next_var_range(size)
			}
		}
	};

	let from_cnf = if opts.has_default {
		let var_member = match opts.vars {
			Some(x) => quote! { #x },
			None => quote! { vars },
		};
		let up_version = if opts.ipasir_up {
			quote! {
				#[cfg(feature = "ipasir-up")]
				impl From<crate::Cnf> for #ident {
					fn from(value: crate::Cnf) -> #ident {
						let mut slv: #ident = Default::default();
						slv. #var_member = Arc::new(Mutex::new(value.nvar));
						for cl in value.iter() {
							let _ = crate::ClauseDatabase::add_clause(&mut slv, cl.iter().copied());
						}
						slv
					}
				}
				#[cfg(not(feature = "ipasir-up"))]
			}
		} else {
			quote!()
		};

		quote! {
			#up_version
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
			#new_var

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
			#next_var_range
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
