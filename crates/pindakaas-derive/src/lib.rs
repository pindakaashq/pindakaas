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

	let (term_callback, term_drop) = if opts.term_callback {
		let term_cb = match opts.term_callback_ident {
			Some(x) => quote! { self. #x },
			None => quote! { self.term_cb },
		};
		(
			quote! {
				impl crate::solver::TermCallback for #ident {
					fn set_terminate_callback<F: FnMut() -> crate::solver::SlvTermSignal + 'static>(
						&mut self,
						cb: Option<F>,
					) {
						if let Some(mut cb) = cb {
							let mut wrapped_cb = move || -> std::ffi::c_int {
								match cb() {
									crate::solver::SlvTermSignal::Continue => std::ffi::c_int::from(0),
									crate::solver::SlvTermSignal::Terminate => std::ffi::c_int::from(1),
								}
							};
							let trampoline = crate::solver::libloading::get_trampoline0(&wrapped_cb);
							let layout = std::alloc::Layout::for_value(&wrapped_cb);
							let data = Box::leak(Box::new(wrapped_cb)) as *mut _ as *mut std::ffi::c_void;
							if layout.size() != 0 {
								// Otherwise nothing was leaked.
								#term_cb = Some((data, layout));
							}
							unsafe {
								#krate::ipasir_set_terminate(
									#ptr,
									data,
									Some(trampoline),
								)
							}
						} else {
							if let Some((ptr, layout)) = #term_cb .take() {
								unsafe { std::alloc::dealloc(ptr as *mut _, layout) };
							}
							unsafe { #krate::ipasir_set_terminate(#ptr, std::ptr::null_mut(), None) }
						}
					}
				}
			},
			quote! {
				if let Some((ptr, layout)) = #term_cb .take() {
					unsafe { std::alloc::dealloc(ptr as *mut _, layout) };
				}
			},
		)
	} else {
		(quote!(), quote!())
	};

	let (learn_callback, learn_drop) = if opts.learn_callback {
		let learn_cb = match opts.learn_callback_ident {
			Some(x) => quote! { self. #x },
			None => quote! { self.learn_cb },
		};
		(
			quote! {
				impl crate::solver::LearnCallback for #ident {
					fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = crate::Lit>) + 'static>(
						&mut self,
						cb: Option<F>,
					) {
						const MAX_LEN: std::ffi::c_int = 512;
						if let Some(mut cb) = cb {
							let mut wrapped_cb = move |clause: *const i32| {
								let mut iter = crate::solver::libloading::ExplIter(clause)
									.map(|i: i32| crate::Lit(std::num::NonZeroI32::new(i).unwrap()));
								cb(&mut iter)
							};
							let trampoline = crate::solver::libloading::get_trampoline1(&wrapped_cb);
							let layout = std::alloc::Layout::for_value(&wrapped_cb);
							let data = Box::leak(Box::new(wrapped_cb)) as *mut _ as *mut std::ffi::c_void;
							if layout.size() != 0 {
								// Otherwise nothing was leaked.
								#learn_cb = Some((data, layout));
							}
							unsafe {
								#krate::ipasir_set_learn(
									#ptr,
									data,
									MAX_LEN,
									Some(trampoline),
								)
							}
						} else {
							if let Some((ptr, layout)) = #learn_cb .take() {
								unsafe { std::alloc::dealloc(ptr as *mut _, layout) };
							}
							unsafe { #krate::ipasir_set_learn(#ptr, std::ptr::null_mut(), MAX_LEN, None) }
						}
					}
				}
			},
			quote! {
				if let Some((ptr, layout)) = #learn_cb .take() {
					unsafe { std::alloc::dealloc(ptr as *mut _, layout) };
				}
			},
		)
	} else {
		(quote!(), quote!())
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
				prop: *mut c_void,
				drop_prop: fn(*mut c_void),
				access_prop: fn(*mut c_void) -> *mut dyn std::any::Any,
				/// C Wrapper Object
				wrapper: *mut std::ffi::c_void,
			}

			#[cfg(feature = "ipasir-up")]
			impl Drop for #prop_ident {
				fn drop(&mut self) {
					unsafe { #krate::ipasir_prop_release(self.wrapper) };
					(self.drop_prop)(self.prop);
				}
			}

			#[cfg(feature = "ipasir-up")]
			impl #prop_ident {
				pub(crate) fn new<P: crate::solver::Propagator + 'static>(prop: P, slv: *mut dyn crate::solver::SolvingActions) -> Self {
					// Construct wrapping structures
					let prop = crate::solver::libloading::IpasirPropStore::<P>::new(prop, slv);
					let drop_prop = |x: *mut std::ffi::c_void| {
						let prop = unsafe { Box::<P>::from_raw(x as *mut P) };
						drop(prop);
					};
					let access_prop = |x: *mut std::ffi::c_void| {
						x as *mut P as *mut dyn std::any::Any
					};
					let data = Box::leak(Box::new(prop)) as *mut _ as *mut std::ffi::c_void;
					let wrapper = unsafe { #krate::ipasir_prop_init(data as *mut std::ffi::c_void) };

					// Set function pointers for methods
					unsafe { #krate::ipasir_prop_set_notify_assignment(wrapper, Some(crate::solver::libloading::ipasir_notify_assignment_cb::<P>)) };
					unsafe { #krate::ipasir_prop_set_notify_new_decision_level(wrapper, Some(crate::solver::libloading::ipasir_notify_new_decision_level_cb::<P>)) };
					unsafe { #krate::ipasir_prop_set_notify_backtrack(wrapper, Some(crate::solver::libloading::ipasir_notify_backtrack_cb::<P>)) };
					unsafe { #krate::ipasir_prop_set_check_model(wrapper, Some(crate::solver::libloading::ipasir_check_model_cb::<P>)) };
					unsafe { #krate::ipasir_prop_set_decide(wrapper, Some(crate::solver::libloading::ipasir_decide_cb::<P>)) };
					unsafe { #krate::ipasir_prop_set_propagate(wrapper, Some(crate::solver::libloading::ipasir_propagate_cb::<P>)) };
					unsafe { #krate::ipasir_prop_set_add_reason_clause_lit(wrapper, Some(crate::solver::libloading::ipasir_add_reason_clause_lit_cb::<P>)) };
					unsafe { #krate::ipasir_prop_set_has_external_clause(wrapper, Some(crate::solver::libloading::ipasir_has_external_clause_cb::<P>)) };
					unsafe { #krate::ipasir_prop_set_add_external_clause_lit(wrapper, Some(crate::solver::libloading::ipasir_add_external_clause_lit_cb::<P>)) };

					Self { prop: data, drop_prop, access_prop, wrapper, }
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
						#prop_member = Some(#prop_ident ::new(p, (self as *mut _)));
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
					#prop_member.as_ref().map(|p| unsafe { &*(p.access_prop)(p.prop) } .downcast_ref()).flatten()
				}
			}

			#[cfg(feature = "ipasir-up")]
			impl crate::solver::MutPropagatorAccess for #ident {
				fn propagator_mut<P: crate::solver::Propagator + 'static>(&mut self) -> Option<&mut P> {
					#prop_member.as_ref().map(|p| unsafe { &mut *(p.access_prop)(p.prop) } .downcast_mut()).flatten()
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
				#[cfg(feature = "ipasir-up")]
				access_prop: Option<fn(*mut std::ffi::c_void) -> *mut dyn std::any::Any>,
			}
			impl #ident {
				fn solver_solution_obj(&mut self) -> #sol_ident {
					#sol_ident {
						ptr: self.ptr,
						#[cfg(feature = "ipasir-up")]
						prop: #prop_member .as_mut().map(|p| p.prop),
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
				#learn_drop
				#term_drop
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
