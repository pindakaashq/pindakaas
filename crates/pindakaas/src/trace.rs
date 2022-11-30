/// Helper marco to add
#[cfg(feature = "trace")]
macro_rules! new_var {
	($db:expr) => {{
		let var = $db.new_var();
		tracing::info!(var = ?var, "new var");
		var
	}};
	($db:expr, $lbl:expr) => {{
		let var = $db.new_var();
		tracing::info!(var = ?var, label = $lbl, "new var");
		var
	}};
}
#[cfg(not(feature = "trace"))]
#[macro_export]
macro_rules! new_var {
	($db:expr) => {
		$db.new_var()
	};
	($db:expr, $lbl:expr) => {
		$db.new_var()
	};
}
pub(crate) use new_var;

#[cfg(feature = "trace")]
macro_rules! emit_clause {
	($db:expr, $cl:expr) => {{
		let slice = $cl;
		let res = $db.add_clause(slice);
		tracing::info!(clause = ?slice, fail = matches!(res, Err($crate::Unsatisfiable)), "clause");
		res
	}};
}
#[cfg(not(feature = "trace"))]
#[macro_export]
macro_rules! emit_clause {
	($db:expr, $cl:expr) => {
		$db.add_clause($cl)
	};
}
pub(crate) use emit_clause;
