//! This crate provides a procedural macro that registers a
//! [`pindakaas::tracer::Tracer`] as a global subscriber to the test case.

use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse, ItemFn, Stmt};

/// A procedural macro that adds the pindakaas [`Tracer`] to the test case.
#[proc_macro_attribute]
pub fn test(_attr: TokenStream, item: TokenStream) -> TokenStream {
	// Parse annotated function
	let mut function: ItemFn = parse(item).expect("unable to parse function");
	let subscriber = parse::<Stmt>(
		quote! {
			let (my_subscriber, _guard) = crate::trace::Tracer::new();
		}
		.into(),
	)
	.expect("unable to parse subscriber declaration");
	let exec = parse::<Stmt>(
		format!(
			"tracing::subscriber::with_default(my_subscriber, || {} );",
			function.block.to_token_stream()
		)
		.parse::<TokenStream>()
		.expect("unable to parse tracing execution token stream"),
	)
	.expect("unable to parse tracing execution statement");
	// Replace function body
	function.block.stmts = vec![subscriber, exec];

	// Create new function with core test attribute
	let fn_body = function.to_token_stream();
	quote! {
		#[::core::prelude::v1::test]
		#fn_body
	}
	.into()
}
