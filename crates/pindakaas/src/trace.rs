//! Module containing a specialized [`Subscriber`] for tracing encoding methods
//! in the Pindakaas library, named [`Tracer`] .

use std::{
	fmt,
	io::{stderr, BufWriter, Stderr, Write},
	sync::{
		atomic::{AtomicU64, Ordering},
		Arc, Mutex,
	},
	thread::panicking,
	time::Instant,
};

use itertools::join;
use tracing::{
	field::{Field, Visit},
	metadata::LevelFilter,
	span::{Attributes, Record},
	Event, Id, Level, Metadata, Subscriber,
};

use crate::{helpers::subscript_number, Lit};

#[derive(Debug)]
enum EventKind {
	NewVar,
	Clause,
}

#[derive(Debug, Default)]
struct EventVisitor {
	kind: Option<EventKind>,
	var: Option<String>,
	label: Option<String>,
	clause: Option<String>,
	fail: Option<bool>,
}

#[derive(Debug)]
/// Guarding type that will ensure a [`BufWriter`] is flushed when dropped.
pub struct FlushGuard {
	out: Arc<Mutex<BufWriter<Stderr>>>,
}

enum RecordedEvent {
	NewVar(String, String),
	Clause(Vec<(bool, String)>, bool),
}

#[derive(Debug)]
struct SpanVisitor {
	ident: Id,
	name: String,
	start: Option<Instant>,
	constraint: Option<String>,
	vars: usize,
	clauses: usize,
}

#[derive(Debug)]
/// Specialized [`Subscriber`] implementation that will trace CNF encoding
/// methods in pindakaas library.
///
/// Tracer will track literal names, and will visualize the recursive calls to
/// different encoders.
pub struct Tracer {
	lit_names: Mutex<rustc_hash::FxHashMap<String, String>>,
	next_span_id: AtomicU64,
	stack: Mutex<Vec<SpanVisitor>>,
	out: Arc<Mutex<BufWriter<Stderr>>>,
}

fn create_var_name(var: &str, prepend: &str) -> String {
	if let Ok(x) = var.parse::<usize>() {
		subscripted_name(prepend, x)
	} else {
		String::from(var)
	}
}

pub(crate) fn subscripted_name(name: &str, sub: usize) -> String {
	let mut s = String::from(name);
	for c in subscript_number(sub) {
		s.push(c);
	}
	s
}

pub(crate) fn trace_print_lit(l: &Lit) -> String {
	format!("{}{{{:?}}}", if l.is_negated() { "¬" } else { "" }, l.var())
}

impl EventVisitor {
	fn recorded_event(self) -> Option<RecordedEvent> {
		match self.kind {
			Some(EventKind::NewVar) if self.var.is_some() => {
				let var = self.var.unwrap();
				let name = self.label.unwrap_or_else(|| create_var_name(&var, "i"));
				Some(RecordedEvent::NewVar(var, name))
			}
			Some(EventKind::Clause) if self.clause.is_some() && self.fail.is_some() => {
				let clause_str = self.clause.unwrap();
				let fail = self.fail.unwrap();
				let braces: &[_] = &['[', ']'];
				let negations: &[_] = &['-', '!', '¬'];
				let s = clause_str.trim_matches(braces);
				let names = s
					.split(',')
					.map(|s| {
						let s = s.trim();
						let x = s.trim_start_matches(negations);
						(s == x, x.into())
					})
					.collect();
				Some(RecordedEvent::Clause(names, fail))
			}
			_ => None,
		}
	}
}

impl Visit for EventVisitor {
	fn record_bool(&mut self, field: &Field, value: bool) {
		if field.name() == "fail" {
			self.fail = Some(value);
		}
	}
	fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
		let value = format!("{value:?}");
		match field.name() {
			"message" => match value.as_str() {
				"new variable" => self.kind = Some(EventKind::NewVar),
				"emit clause" => self.kind = Some(EventKind::Clause),
				_ => {}
			},
			"var" => self.var = Some(value),
			"clause" => self.clause = Some(value),
			_ => {}
		}
	}
	fn record_str(&mut self, field: &Field, value: &str) {
		if field.name() == "label" {
			self.label = Some(value.to_owned());
		}
	}
}
impl FlushGuard {
	fn flush(&self) {
		let mut guard = match self.out.lock() {
			Ok(guard) => guard,
			Err(e) => {
				if !panicking() {
					panic!("{}", e);
				} else {
					return;
				}
			}
		};

		// FIXME: Deal with flush error
		guard.flush().expect("unable to flush output");
	}
}

impl Drop for FlushGuard {
	fn drop(&mut self) {
		self.flush();
	}
}

impl SpanVisitor {
	fn new(ident: Id, name: String) -> Self {
		Self {
			ident,
			name,
			start: None,
			constraint: None,
			vars: 0,
			clauses: 0,
		}
	}
}

impl Visit for SpanVisitor {
	fn record_debug(&mut self, _field: &Field, _value: &dyn fmt::Debug) {}
	fn record_str(&mut self, field: &Field, value: &str) {
		if field.name() == "constraint" {
			self.constraint = Some(String::from(value));
		}
	}
}

impl Tracer {
	/// Returns a `FlushGuard` which will flush the `Tracer`'s writers when
	/// it is dropped, or when `flush` is manually invoked on the guard.
	pub fn flush_on_drop(&self) -> FlushGuard {
		FlushGuard {
			out: Arc::clone(&self.out),
		}
	}

	fn indented_output(&self, indent: usize, line: &str) {
		let mut out = self.out.lock().unwrap();
		for _ in 0..indent {
			write!(out, "│ ").unwrap();
		}
		writeln!(out, "{line}").unwrap();
	}

	/// Creates a new `Tracer` instance with a `FlushGuard` that will flush the
	/// `Tracer`'s writers when it is dropped.
	pub fn new() -> (Self, FlushGuard) {
		let writer = BufWriter::new(stderr());
		let tracer = Self {
			next_span_id: 1.into(),
			lit_names: Default::default(),
			stack: Vec::new().into(),
			out: Arc::new(writer.into()),
		};
		let guard = tracer.flush_on_drop();
		(tracer, guard)
	}

	fn pretty_constraint(&self, cons: String) -> String {
		let mut it = cons.split('{');
		let mut ret = String::from(it.next().unwrap_or_default());

		let lit_names = self.lit_names.lock().unwrap();
		for chunk in it {
			if let Some((lit, rem)) = chunk.split_once('}') {
				if let Some(label) = lit_names.get(lit) {
					ret.push_str(label);
				} else {
					ret.push_str(&create_var_name(lit, "x"));
				}
				ret.push_str(rem);
			} else {
				ret.push_str(chunk);
			}
		}
		ret
	}
}

impl Subscriber for Tracer {
	fn enabled(&self, metadata: &Metadata<'_>) -> bool {
		if metadata.level() < &Level::INFO {
			return false;
		}
		if metadata.is_event() {
			let mut msg = false;
			let mut var = false;
			let mut clause = false;
			let mut fail = false;
			for f in metadata.fields() {
				match f.name() {
					"message" => msg = true,
					"var" => var = true,
					"clause" => clause = true,
					"fail" => fail = true,
					_ => {}
				}
			}
			msg && (var || (clause && fail))
		} else {
			let mut cons = false;
			for f in metadata.fields() {
				if f.name() == "constraint" {
					cons = true;
				}
			}
			cons
		}
	}

	fn enter(&self, span: &Id) {
		let mut stack = self.stack.lock().unwrap();
		let indent = stack.len() - 1;
		let visitor = stack.last_mut().unwrap();
		assert_eq!(&visitor.ident, span); // FIXME: Deal with out of order execution
		assert_eq!(visitor.start, None); // FIXME: Deal with re-entrant spans
		visitor.start = Some(Instant::now());
		let constraint = if let Some(cons) = &visitor.constraint {
			cons.as_str()
		} else {
			""
		};
		self.indented_output(indent, &format!("╭─╴{}: {}", visitor.name, constraint));
	}

	fn event(&self, event: &Event<'_>) {
		let mut stack = self.stack.lock().unwrap();
		let indent = stack.len();
		let frame = stack.last_mut();
		let mut visitor = EventVisitor::default();
		event.record(&mut visitor);
		if let Some(event) = visitor.recorded_event() {
			match event {
				RecordedEvent::NewVar(var, name) => {
					if let Some(frame) = frame {
						frame.vars += 1;
					}
					let mut lit_names = self.lit_names.lock().unwrap();
					let _ = lit_names.insert(var, name);
				}
				RecordedEvent::Clause(cl, fail) => {
					if let Some(frame) = frame {
						frame.clauses += 1;
					}
					let lit_names = self.lit_names.lock().unwrap();
					let clause = join(
						cl.into_iter().map(|(pos, lit)| {
							let mut label = lit_names
								.get(&lit)
								.cloned()
								.unwrap_or_else(|| create_var_name(&lit, "x"));
							if !pos {
								label.insert(0, '¬');
							};
							label
						}),
						" ∨ ",
					);
					self.indented_output(indent, &clause);
					if fail {
						self.indented_output(indent, "├ UNSAT");
					}
				}
			}
		}
	}

	fn exit(&self, span: &Id) {
		let mut stack = self.stack.lock().unwrap();
		let visitor = stack.pop().unwrap();
		assert_eq!(&visitor.ident, span); // FIXME: Deal with out of order execution
		if let Some(start) = visitor.start {
			let dur = Instant::now() - start;
			self.indented_output(
				stack.len(),
				&format!(
					"╰─╴time: {dur:?} vars: {} clauses: {}",
					visitor.vars, visitor.clauses
				),
			);
		}
		if let Some(parent) = stack.last_mut() {
			parent.vars += visitor.vars;
			parent.clauses += visitor.clauses;
		}
	}

	fn max_level_hint(&self) -> Option<LevelFilter> {
		Some(LevelFilter::INFO)
	}

	fn new_span(&self, span: &Attributes<'_>) -> Id {
		let res = self.next_span_id.fetch_add(1, Ordering::Relaxed);
		let ident = Id::from_u64(res);
		let mut visitor = SpanVisitor::new(ident.clone(), span.metadata().name().into());
		span.record(&mut visitor);
		if let Some(cons) = visitor.constraint {
			visitor.constraint = Some(self.pretty_constraint(cons));
		}
		let mut stack = self.stack.lock().unwrap();
		stack.push(visitor);
		ident
	}

	fn record(&self, _span: &Id, _values: &Record<'_>) {
		todo!() // FIXME: Currently everything is recorded in `new_span`
	}

	fn record_follows_from(&self, _span: &Id, _follows: &Id) {}
}
