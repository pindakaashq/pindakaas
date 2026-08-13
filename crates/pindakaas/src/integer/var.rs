use std::{cell::RefCell, ops::Bound, rc::Rc};

use itertools::{Either, Itertools};
use rangelist::{IntervalIterator, RangeList};
use rustc_hash::FxHashMap;

use crate::{
	bool_linear::{Comparator, PosCoeff},
	helpers::{as_binary, new_named_lit, new_named_var_range},
	integer::{lex_geq_const, lex_leq_const},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Lit, Result, Unsatisfiable, Var, VarRange,
};

/// The binary encoding of an integer variable.
///
/// The bits are those of `value - lb`, least significant first, so that the
/// lower bound of the domain costs nothing to enforce. A bit may be fixed
/// rather than free, which is what lets a shifted, complemented or otherwise
/// derived encoding be expressed without introducing literals for it.
#[derive(Clone, Debug)]
pub(crate) struct BinEnc {
	x: Lits<BoolVal>,
	lb: Coeff,
}

/// The literals of an encoding.
///
/// Literals created for an encoding are allocated in one block and so are
/// consecutive, which a range holds in a couple of words however wide the
/// encoding is — worth having, since an encoding is handed out by value every
/// time a constraint asks for it. Literals recovered from a constraint that
/// already mentions them, or bits fixed by a shift, are kept as given.
#[derive(Clone, Debug)]
pub(crate) enum Lits<T> {
	Explicit(Vec<T>),
	Range(VarRange),
}

/// The direct encoding of an integer variable.
///
/// There is one literal per domain value except the first, holding when the
/// variable takes exactly that value; none of them holding means it takes the
/// first. At most one may hold, which for a group of mutually exclusive
/// pseudo-Boolean terms is what the caller has already asserted.
#[derive(Clone, Debug)]
pub(crate) struct DirEnc {
	dom: RangeList<Coeff>,
	x: Lits<Lit>,
}

/// An integer decision variable, together with whichever Boolean encodings of
/// it have been asked for so far.
///
/// A variable may hold several encodings at once. They are created on first
/// request rather than up front, and the moment a second one appears it is
/// channelled against the first, so that every view of the variable agrees on
/// its value. A constraint can therefore ask for whichever view suits it — the
/// order literals for a sequential decomposition, the bits for an adder —
/// without having to commit to one in advance or introduce a second variable
/// to hold the other.
///
/// Variables are shared between the constraints that mention them, as
/// `Rc<IntVar>`.
// ponytail: `Rc` rather than `Arc`, since nothing needs integer constraints to
// be `Send`; the interior `RefCell` would have to become an `RwLock` anyway.
#[derive(Debug)]
pub(crate) struct IntVar {
	lbl: String,
	/// Whether the encodings are restricted to the domain. The order encoding
	/// is exact by construction, so this only concerns the binary one.
	add_consistency: bool,
	state: RefCell<IntVarState>,
}

/// The parts of a variable that change as it is encoded.
#[derive(Debug)]
struct IntVarState {
	dom: RangeList<Coeff>,
	ord: Option<OrdEnc>,
	bin: Option<BinEnc>,
	dir: Option<DirEnc>,
	/// Which pairs of encodings have been tied together already. With three of
	/// them, "the channel fires when the second appears" no longer says enough.
	channelled: [bool; 2],
	/// Literals to reuse as `x ≥ v` when the order encoding is created, rather
	/// than introducing a fresh one.
	ord_views: FxHashMap<Coeff, Lit>,
	/// Values whose literal is to be taken from another variable, and which of
	/// its values to take it from. Resolved when the order encoding is created,
	/// since the literal may not exist before then.
	view_of: FxHashMap<Coeff, (Rc<IntVar>, Coeff)>,
}

/// The order encoding of an integer variable.
///
/// There is one literal per domain value except the first, where `x[i]` holds
/// exactly when the variable is at least the `i+1`'th value of the domain. The
/// domain is kept alongside the literals so that a value can be resolved to a
/// literal without consulting the variable it came from.
#[derive(Clone, Debug)]
pub(crate) struct OrdEnc {
	dom: RangeList<Coeff>,
	x: Lits<Lit>,
}

impl BinEnc {
	/// The largest value `bits` bits can hold, the inverse of
	/// [`Self::required_bits`].
	pub(crate) fn largest_in(bits: u32) -> Coeff {
		// Summed rather than `(1 << bits) - 1`, which overflows at the width of
		// a coefficient where the sum lands exactly on its largest value.
		const TWO: Coeff = 2;
		(0..bits).fold(0, |sum, i| sum + TWO.pow(i))
	}

	/// The number of bits needed to represent `0..=span`.
	pub(crate) fn required_bits(span: Coeff) -> usize {
		debug_assert!(
			span >= 0,
			"a domain cannot span a negative number of values"
		);
		(Coeff::BITS - span.leading_zeros()) as usize
	}

	/// The `i`'th bit, where bits beyond the encoding's width are zero.
	pub(crate) fn bit(&self, i: usize) -> BoolVal {
		self.x.get(i).unwrap_or(BoolVal::Const(false))
	}

	/// The width of the encoding.
	pub(crate) fn bits(&self) -> usize {
		self.x.len()
	}

	/// Restrict the encoding to the values of `dom`.
	///
	/// The lower bound costs nothing when the bits count from it, which is how
	/// an encoding made for a variable is grounded. One taken from literals
	/// that were already there counts from wherever they do, and then it needs
	/// enforcing like any other.
	pub(crate) fn consistent<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		dom: &RangeList<Coeff>,
	) -> Result {
		let floor = *dom.min().unwrap() - self.lb;
		if floor > 0 {
			lex_geq_const(db, &self.x.to_vec(), PosCoeff::new(floor), self.bits())?;
		}
		let span = *dom.max().unwrap() - self.lb;
		lex_leq_const(db, &self.x.to_vec(), PosCoeff::new(span), self.bits())?;
		// ponytail: one clause per value in a gap, so a sparse domain over a
		// wide range pays for every value it skips. Worth revisiting only if
		// such domains show up; a range-aware exclusion would be the fix.
		for (below, above) in dom.iter().tuple_windows() {
			for v in (*below.end() + 1)..*above.start() {
				self.encode_neq(db, v)?;
			}
		}
		Ok(())
	}

	/// Restrict the encoding to the values on one side of `v`.
	pub(crate) fn encode_bound<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		cmp: Comparator,
		v: Coeff,
		dom: &RangeList<Coeff>,
	) -> Result {
		let (lb, ub) = (*dom.min().unwrap(), *dom.max().unwrap());
		match cmp {
			Comparator::LessEq if v >= ub => Ok(()),
			Comparator::LessEq if v < lb => db.contradiction(),
			Comparator::LessEq => lex_leq_const(
				db,
				&self.x.to_vec(),
				PosCoeff::new(v - self.lb),
				self.bits(),
			),
			Comparator::GreaterEq if v <= lb => Ok(()),
			Comparator::GreaterEq if v > ub => db.contradiction(),
			Comparator::GreaterEq => lex_geq_const(
				db,
				&self.x.to_vec(),
				PosCoeff::new(v - self.lb),
				self.bits(),
			),
			Comparator::Equal => unreachable!("an equality is split before it is encoded"),
		}
	}

	/// Forbid the encoding from taking the value `v`.
	pub(crate) fn encode_neq<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db, v: Coeff) -> Result {
		let k = as_binary(PosCoeff::new(v - self.lb), Some(self.bits() as u32));
		db.add_clause(
			self.x
				.iter()
				.zip(k)
				.map(|(b, set)| if set { !b } else { b }),
		)
	}

	/// The encoding of a two-valued variable, whose single order literal
	/// already distinguishes both values and so can stand in for every bit
	/// that tells them apart.
	pub(crate) fn from_two_valued(lit: Lit, dom: &RangeList<Coeff>) -> Self {
		let (lb, ub) = (*dom.min().unwrap(), *dom.max().unwrap());
		let x = Lits::Explicit(
			as_binary(PosCoeff::new(ub - lb), None)
				.into_iter()
				.map(|set| {
					if set {
						BoolVal::Lit(lit)
					} else {
						BoolVal::Const(false)
					}
				})
				.collect(),
		);
		Self { x, lb }
	}

	/// An encoding of bits already built, counting from `lb`.
	pub(crate) fn from_bits(bits: Vec<BoolVal>, lb: Coeff) -> Self {
		Self {
			x: Lits::Explicit(bits),
			lb,
		}
	}

	/// The encoding as a weighted sum of literals, plus what it is worth when
	/// none of them hold.
	pub(crate) fn as_weighted(&self) -> (Vec<(Lit, Coeff)>, Coeff) {
		let mut constant = self.lb;
		let terms = self
			.x
			.iter()
			.enumerate()
			.filter_map(|(i, b)| {
				let weight = 1 << i;
				match b {
					BoolVal::Lit(l) => Some((l, weight)),
					// A bit that is fixed is worth what it is worth regardless.
					BoolVal::Const(true) => {
						constant += weight;
						None
					}
					BoolVal::Const(false) => None,
				}
			})
			.collect();
		(terms, constant)
	}

	/// The bits of the encoding, least significant first.
	pub(crate) fn to_vec(&self) -> Vec<BoolVal> {
		self.x.to_vec()
	}

	/// The value the encoding is offset by.
	pub(crate) fn lb(&self) -> Coeff {
		self.lb
	}

	/// Create the bits for `dom`, all of them free.
	pub(crate) fn new<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		dom: &RangeList<Coeff>,
		_lbl: &str,
	) -> Self {
		let (lb, ub) = (*dom.min().unwrap(), *dom.max().unwrap());
		let x = Lits::Range(new_named_var_range!(
			db,
			Self::required_bits(ub - lb),
			|i| format!("{_lbl}^{i}")
		));
		Self { x, lb }
	}

	/// The value represented under an assignment.
	#[cfg(test)]
	pub(crate) fn value<F: crate::Valuation + ?Sized>(&self, value: &F) -> Coeff {
		self.lb + crate::helpers::tests::bin_value(&self.x.to_vec(), value)
	}
}

impl<T: Copy + From<Var>> Lits<T> {
	/// The `i`'th literal, if the encoding is that wide.
	pub(crate) fn get(&self, i: usize) -> Option<T> {
		match self {
			Lits::Explicit(x) => x.get(i).copied(),
			Lits::Range(r) => (i < r.len()).then(|| r.index(i).into()),
		}
	}

	/// The literals, in order.
	pub(crate) fn iter(&self) -> impl Iterator<Item = T> + '_ {
		match self {
			Lits::Explicit(x) => Either::Left(x.iter().copied()),
			Lits::Range(r) => Either::Right(r.map(T::from)),
		}
	}

	/// The number of literals.
	pub(crate) fn len(&self) -> usize {
		match self {
			Lits::Explicit(x) => x.len(),
			Lits::Range(r) => r.len(),
		}
	}

	/// The literals as a slice, materialising a range into one.
	pub(crate) fn to_vec(&self) -> Vec<T> {
		self.iter().collect()
	}
}

impl DirEnc {
	/// Restrict the encoding to holding for exactly one value.
	pub(crate) fn consistent<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		db.add_clause(self.x.iter())?;
		// ponytail: pairwise, so quadratic in the domain. A variable that also
		// has an order encoding gets exclusivity from the channel for nothing,
		// which is the case that arises in practice.
		for (i, a) in self.x.iter().enumerate() {
			for b in self.x.iter().skip(i + 1) {
				db.add_clause([!a, !b])?;
			}
		}
		Ok(())
	}

	/// Whether the variable takes exactly `v`.
	pub(crate) fn eq_val(&self, v: Coeff) -> BoolVal {
		match self.dom.iter().flatten().position(|d| d == v) {
			None => BoolVal::Const(false),
			Some(pos) => BoolVal::Lit(self.x.get(pos).unwrap()),
		}
	}

	/// Create a direct encoding from the literals it is already on, one for
	/// each value of `dom` in order.
	pub(crate) fn from_lits(dom: RangeList<Coeff>, x: Vec<Lit>) -> Self {
		debug_assert_eq!(
			x.len(),
			dom.card().unwrap(),
			"a direct encoding has a literal for every value"
		);
		Self {
			dom,
			x: Lits::Explicit(x),
		}
	}

	/// The encoding as a weighted sum of literals, plus what it is worth when
	/// none of them hold.
	///
	/// Exactly one literal holds, so the variable is worth whichever value that
	/// one stands for.
	pub(crate) fn as_weighted(&self) -> (Vec<(Lit, Coeff)>, Coeff) {
		(
			self.dom
				.iter()
				.flatten()
				.zip(self.x.iter())
				.map(|(v, l)| (l, v))
				.collect(),
			0,
		)
	}

	/// The literals of the encoding.
	pub(crate) fn lits(&self) -> Vec<Lit> {
		self.x.to_vec()
	}

	/// The steps of a sequential decomposition over this variable.
	///
	/// Each step is a value paired with the clause that holds unless the
	/// variable takes it, so that what the constraint then demands can be
	/// disjoined onto it — the same shape the order encoding gives, except that
	/// a step here pins the value exactly rather than bounding it.
	///
	/// The value at the far end contributes the least of any, so what it
	/// demands holds whatever the variable turns out to be; its clause is
	/// `false` and drops out, leaving that demand unconditional.
	pub(crate) fn steps(&self, geq: bool) -> Vec<(Coeff, BoolVal)> {
		let vals: Vec<Coeff> = self.dom.iter().flatten().collect();
		let step = |(i, d): (usize, Coeff)| {
			(
				d,
				if i == 0 {
					BoolVal::Const(false)
				} else {
					!self.eq_val(d)
				},
			)
		};
		if geq {
			vals.into_iter().enumerate().map(step).collect()
		} else {
			vals.into_iter().rev().enumerate().map(step).collect()
		}
	}

	/// The value represented under an assignment.
	#[cfg(test)]
	pub(crate) fn value<F: crate::Valuation + ?Sized>(&self, value: &F) -> Coeff {
		self.dom
			.iter()
			.flatten()
			.zip(self.x.to_vec())
			.find(|(_, l)| value.value(*l))
			.expect("a direct encoding holds for one of its values")
			.0
	}
}

impl IntVar {
	/// The binary encoding of the variable, created if this is the first
	/// request for it.
	pub(crate) fn bin<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result<BinEnc> {
		if let Some(bin) = self.state.borrow().bin.as_ref() {
			return Ok(bin.clone());
		}
		// Take what is needed out of the variable before touching the database,
		// so that no borrow is held while clauses are emitted.
		let (dom, view) = {
			let state = self.state.borrow();
			let view = state
				.ord
				.as_ref()
				.and_then(OrdEnc::single_lit)
				.map(|l| BinEnc::from_two_valued(l, &state.dom));
			(state.dom.clone(), view)
		};

		// A two-valued variable needs no channelling: its order literal is
		// already the whole of its binary encoding.
		let derived = view.is_some();
		let bin = match view {
			Some(bin) => bin,
			None => {
				let bin = BinEnc::new(db, &dom, &self.lbl);
				if self.add_consistency {
					bin.consistent(db, &dom)?;
				}
				bin
			}
		};

		{
			let mut state = self.state.borrow_mut();
			state.bin = Some(bin.clone());
			// A two-valued variable needs no tying: its order literal is
			// already the whole of its binary encoding.
			state.channelled[0] |= derived;
		}
		self.reconcile(db)?;
		Ok(bin)
	}

	/// Constrain the order and binary encodings to represent the same value.
	///
	/// For each bit, the values it separates form blocks of `2ⁱ` consecutive
	/// values, alternating between the bit being zero and one. Placing the
	/// variable in a block therefore fixes the bit, and conversely the bits of
	/// a value pin down which blocks it lies in, so the two directions come out
	/// of the same clauses. Blocks reaching past the domain fold away, since
	/// their bounds resolve to constants.
	fn channel<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (ord, bin) = {
			let mut state = self.state.borrow_mut();
			match (state.ord.as_ref(), state.bin.as_ref()) {
				(Some(ord), Some(bin)) if !state.channelled[0] => {
					let pair = (ord.clone(), bin.clone());
					state.channelled[0] = true;
					pair
				}
				_ => return Ok(()),
			}
		};
		for i in 0..bin.bits() {
			let width = 1 << i;
			for k in 0..(1 << (bin.bits() - i)) {
				let below = bin.lb() + width * k;
				db.add_clause([
					ord.leq_val(below - 1),
					ord.geq_val(below + width),
					if k % 2 == 0 { !bin.bit(i) } else { bin.bit(i) },
				])?;
			}
		}
		Ok(())
	}

	/// The direct encoding of the variable, created if this is the first
	/// request for it.
	pub(crate) fn dir<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result<DirEnc> {
		if let Some(dir) = self.state.borrow().dir.as_ref() {
			return Ok(dir.clone());
		}
		let dom = self.dom();
		let lits = new_named_var_range!(db, dom.card().unwrap(), |i| format!("{}={i}", self.lbl))
			.map(Lit::from)
			.collect();
		let dir = DirEnc::from_lits(dom, lits);
		// Literals it was found on are already exclusive, the caller having
		// said so; ones made here are not, and nothing else says it.
		dir.consistent(db)?;
		self.state.borrow_mut().dir = Some(dir.clone());
		self.reconcile(db)?;
		Ok(dir)
	}

	/// Tie together whatever encodings the variable now has, so that every view
	/// of it reads the same value.
	///
	/// The order encoding is the go-between: tying a new encoding to it is
	/// enough for the new one to agree with everything already tied to it. A
	/// variable holding only the other two therefore gains one, which is the
	/// price of reading it two ways at once.
	fn reconcile<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (has_ord, others) = {
			let state = self.state.borrow();
			(
				state.ord.is_some(),
				usize::from(state.bin.is_some()) + usize::from(state.dir.is_some()),
			)
		};
		if others + usize::from(has_ord) < 2 {
			return Ok(());
		}
		if !has_ord {
			// Creating it reconciles in turn.
			let _ = self.ord(db)?;
			return Ok(());
		}
		self.channel(db)?;
		self.channel_dir(db)
	}

	/// Constrain the order and direct encodings to represent the same value.
	///
	/// Taking a value means reaching it, and reaching a value without reaching
	/// the next is taking it. Those two are the whole of it, and they are one
	/// clause each per value.
	fn channel_dir<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (ord, dir, dom) = {
			let mut state = self.state.borrow_mut();
			match (state.ord.as_ref(), state.dir.as_ref()) {
				(Some(ord), Some(dir)) if !state.channelled[1] => {
					let all = (ord.clone(), dir.clone(), state.dom.clone());
					state.channelled[1] = true;
					all
				}
				_ => return Ok(()),
			}
		};
		let vals: Vec<Coeff> = dom.iter().flatten().collect();
		for (i, &v) in vals.iter().enumerate() {
			// Beyond the last value there is nothing to reach.
			let beyond = vals
				.get(i + 1)
				.map_or(BoolVal::Const(false), |&n| ord.geq_val(n));
			// Taking a value is reaching it and going no further, and reaching
			// it and going no further is taking it.
			db.add_clause([!dir.eq_val(v), ord.geq_val(v)])?;
			db.add_clause([!dir.eq_val(v), !beyond])?;
			db.add_clause([!ord.geq_val(v), beyond, dir.eq_val(v)])?;
		}
		Ok(())
	}

	/// The domain of the variable.
	pub(crate) fn dom(&self) -> RangeList<Coeff> {
		self.state.borrow().dom.clone()
	}

	/// The variable as a weighted sum of literals, plus what it is worth when
	/// none of them hold.
	///
	/// Read through whichever encoding it has, so that a constraint wanting
	/// literals rather than integers gets the ones already standing for it.
	pub(crate) fn as_weighted<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<(Vec<(Lit, Coeff)>, Coeff), Unsatisfiable> {
		{
			let state = self.state.borrow();
			match (state.dir.as_ref(), state.ord.as_ref(), state.bin.as_ref()) {
				(Some(dir), ..) => return Ok(dir.as_weighted()),
				(_, Some(ord), _) => return Ok(ord.as_weighted()),
				(.., Some(bin)) => return Ok(bin.as_weighted()),
				_ => {}
			}
		}
		// Nothing has been asked of it yet. The order encoding is the one that
		// costs least to make, and nothing at all where the literals for it are
		// already there.
		Ok(self.ord(db)?.as_weighted())
	}

	/// Whether the variable is held in a direct encoding.
	pub(crate) fn has_dir(&self) -> bool {
		self.state.borrow().dir.is_some()
	}

	/// The direct encoding of the variable, if it has one.
	pub(crate) fn dir_now(&self) -> Option<DirEnc> {
		self.state.borrow().dir.clone()
	}

	/// Create a variable held in the direct encoding it was found on.
	pub(crate) fn with_dir(dom: RangeList<Coeff>, lbl: String, dir: DirEnc) -> Rc<Self> {
		let x = Self::new(dom, false, lbl);
		x.state.borrow_mut().dir = Some(dir);
		x
	}

	/// Whether the variable's literals are settled, so that its domain can no
	/// longer move.
	///
	/// An encoding that exists is settled for the obvious reason. So is one
	/// that does not exist yet but is spoken for: a variable found on literals
	/// that were already there cannot drop a value, because the literal
	/// standing for it is out in the world regardless, and dropping the value
	/// would leave nothing to say it cannot hold.
	pub(crate) fn is_committed(&self) -> bool {
		let state = self.state.borrow();
		state.ord.is_some()
			|| state.bin.is_some()
			|| state.dir.is_some()
			|| !state.ord_views.is_empty()
			|| !state.view_of.is_empty()
	}

	/// Drop the values below `v` from the domain, reporting whether any went.
	pub(crate) fn set_lb(&self, v: Coeff) -> bool {
		debug_assert!(
			!self.is_committed(),
			"the domain of {} cannot move once it is encoded",
			self.lbl
		);
		let mut state = self.state.borrow_mut();
		if v <= *state.dom.min().unwrap() {
			return false;
		}
		state.dom.tighten_min(v);
		true
	}

	/// Drop the values above `v` from the domain, reporting whether any went.
	pub(crate) fn set_ub(&self, v: Coeff) -> bool {
		debug_assert!(
			!self.is_committed(),
			"the domain of {} cannot move once it is encoded",
			self.lbl
		);
		let mut state = self.state.borrow_mut();
		if v >= *state.dom.max().unwrap() {
			return false;
		}
		state.dom.tighten_max(v);
		true
	}

	/// The greatest value the variable can take.
	pub(crate) fn ub(&self) -> Coeff {
		*self.state.borrow().dom.max().unwrap()
	}

	/// The least value the variable can take.
	pub(crate) fn lb(&self) -> Coeff {
		*self.state.borrow().dom.min().unwrap()
	}

	/// The label of the variable.
	pub(crate) fn lbl(&self) -> &str {
		&self.lbl
	}

	/// Create a variable over `dom`.
	pub(crate) fn new(dom: RangeList<Coeff>, add_consistency: bool, lbl: String) -> Rc<Self> {
		debug_assert!(!dom.is_empty(), "an integer variable needs a domain");
		Rc::new(Self {
			lbl,
			add_consistency,
			state: RefCell::new(IntVarState {
				dom,
				ord: None,
				bin: None,
				dir: None,
				channelled: [false; 2],
				ord_views: FxHashMap::default(),
				view_of: FxHashMap::default(),
			}),
		})
	}

	/// Whether the variable is better held in binary than in order form.
	///
	/// An encoding it already has settles the question: reaching for the other
	/// one would mean paying to channel between them. Otherwise a variable is
	/// held in binary once its domain grows past `cutoff`, and always in order
	/// form when there is no cutoff.
	pub(crate) fn prefers_binary(&self, cutoff: Option<Coeff>) -> bool {
		let state = self.state.borrow();
		match (state.bin.is_some(), state.ord.is_some(), cutoff) {
			(true, _, _) => true,
			(_, true, _) => false,
			(_, _, None) => false,
			(_, _, Some(cutoff)) => state.dom.card().unwrap() as Coeff >= cutoff,
		}
	}

	/// The order encoding of the variable, created if this is the first request
	/// for it.
	pub(crate) fn ord<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result<OrdEnc> {
		if let Some(ord) = self.state.borrow().ord.as_ref() {
			return Ok(ord.clone());
		}
		// Fetch the literals taken from elsewhere first, which may encode the
		// variables they come from. Collected before any of that, so that this
		// variable is not borrowed while another is being encoded.
		let pulls: Vec<(Coeff, Rc<IntVar>, Coeff)> = self
			.state
			.borrow()
			.view_of
			.iter()
			.map(|(&v, (src, sv))| (v, Rc::clone(src), *sv))
			.collect();
		for (v, src, src_val) in pulls {
			if let BoolVal::Lit(l) = src.ord(db)?.geq_val(src_val) {
				let _ = self.state.borrow_mut().ord_views.insert(v, l);
			}
		}

		let (dom, views) = {
			let state = self.state.borrow();
			(state.dom.clone(), state.ord_views.clone())
		};

		let ord = OrdEnc::new(db, &dom, &views, &self.lbl);
		ord.consistent(db)?;

		self.state.borrow_mut().ord = Some(ord.clone());
		self.reconcile(db)?;
		Ok(ord)
	}

	/// Whether the variable has been given an order encoding.
	#[cfg(test)]
	pub(crate) fn has_ord(&self) -> bool {
		self.state.borrow().ord.is_some()
	}

	/// The literals that decide the variable, through whichever encoding it was
	/// given.
	#[cfg(test)]
	pub(crate) fn lits(&self) -> Vec<Lit> {
		let state = self.state.borrow();
		match (state.ord.as_ref(), state.bin.as_ref(), state.dir.as_ref()) {
			(Some(ord), _, _) => ord.lits(),
			(_, Some(bin), _) => bin
				.to_vec()
				.into_iter()
				.filter_map(|b| match b {
					BoolVal::Lit(l) => Some(l),
					BoolVal::Const(_) => None,
				})
				.collect(),
			(_, _, Some(dir)) => dir.lits(),
			_ => Vec::new(),
		}
	}

	/// The value the variable takes under an assignment, read through whichever
	/// encoding it was given.
	#[cfg(test)]
	pub(crate) fn value<F: crate::Valuation + ?Sized>(&self, value: &F) -> Coeff {
		let state = self.state.borrow();
		match (state.ord.as_ref(), state.bin.as_ref(), state.dir.as_ref()) {
			(Some(ord), _, _) => ord.value(value),
			(_, Some(bin), _) => bin.value(value),
			(_, _, Some(dir)) => dir.value(value),
			// Nothing was ever asked of it, so it can only be its one value.
			_ => *state.dom.min().unwrap(),
		}
	}

	/// Create a variable held in the binary encoding it was found on, and
	/// restrict it to `dom`.
	pub(crate) fn with_bin<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		dom: RangeList<Coeff>,
		lbl: String,
		bin: BinEnc,
	) -> Result<Rc<Self>, Unsatisfiable> {
		bin.consistent(db, &dom)?;
		let x = Self::new(dom, false, lbl);
		x.state.borrow_mut().bin = Some(bin);
		Ok(x)
	}

	/// Create a variable whose order encoding will reuse the given literals.
	pub(crate) fn with_ord_views(
		dom: RangeList<Coeff>,
		lbl: String,
		ord_views: FxHashMap<Coeff, Lit>,
	) -> Rc<Self> {
		let x = Self::new(dom, false, lbl);
		x.state.borrow_mut().ord_views = ord_views;
		x
	}

	/// Take the literal for `x ≥ v` from `src`, which has the same values from
	/// `src_val` upwards.
	///
	/// Two variables often agree above some point — a layer of a decision
	/// diagram and the one after it reach the same totals once enough has been
	/// decided — and where they do, one literal can serve both. The literal is
	/// fetched when this variable is encoded rather than now, since `src` may
	/// not have been encoded yet.
	pub(crate) fn set_ord_view_of(&self, v: Coeff, src: Rc<IntVar>, src_val: Coeff) {
		debug_assert!(
			self.state.borrow().ord.is_none(),
			"the order encoding of {} already exists",
			self.lbl
		);
		let _ = self.state.borrow_mut().view_of.insert(v, (src, src_val));
	}

	/// Reuse `lit` as the literal for `x ≥ v` when the order encoding is
	/// created.
	pub(crate) fn set_ord_view(&self, v: Coeff, lit: Lit) {
		debug_assert!(
			self.state.borrow().ord.is_none(),
			"the order encoding of {} already exists",
			self.lbl
		);
		let _ = self.state.borrow_mut().ord_views.insert(v, lit);
	}

	/// The number of values in the domain.
	pub(crate) fn size(&self) -> usize {
		self.state.borrow().dom.card().unwrap()
	}
}

impl OrdEnc {
	/// Constrain consecutive literals, so that the encoding represents a single
	/// value of the domain.
	///
	/// Unlike the bounds and holes of a binary encoding this is not optional:
	/// without it there is no well defined value to speak of, and anything
	/// reading the encoding, channelling included, would be meaningless.
	pub(crate) fn consistent<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		for (prev, next) in self.x.iter().tuple_windows() {
			if prev.var() != next.var() {
				db.add_clause([!next, prev])?;
			}
		}
		Ok(())
	}

	/// The encoding as a weighted sum of literals, plus what it is worth when
	/// none of them hold.
	///
	/// Each literal is worth the step it takes from the value before it, so the
	/// ones that hold add up to how far past the first value it has reached.
	pub(crate) fn as_weighted(&self) -> (Vec<(Lit, Coeff)>, Coeff) {
		let vals = self.dom.iter().flatten().collect_vec();
		(
			vals.iter()
				.zip(vals.iter().skip(1))
				.zip(self.x.iter())
				.map(|((below, above), l)| (l, above - below))
				.collect(),
			vals[0],
		)
	}

	/// Whether the variable is at least `v`.
	pub(crate) fn geq_val(&self, v: Coeff) -> BoolVal {
		if v <= *self.dom.min().unwrap() {
			BoolVal::Const(true)
		} else if v > *self.dom.max().unwrap() {
			BoolVal::Const(false)
		} else {
			// The first domain value at or above `v`; the variable reaches `v`
			// exactly when it reaches that value.
			let pos = self
				.dom
				.first_position_bound(&Bound::Included(v))
				.expect("value within the domain bounds has a position");
			BoolVal::Lit(
				self.x
					.get(pos - 1)
					.expect("a domain value has an order literal"),
			)
		}
	}

	/// Whether the variable is at most `v`.
	pub(crate) fn leq_val(&self, v: Coeff) -> BoolVal {
		!self.geq_val(v + 1)
	}

	/// Create the order literals for `dom`, reusing whatever literal `views`
	/// already provides for a value.
	pub(crate) fn new<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		dom: &RangeList<Coeff>,
		views: &FxHashMap<Coeff, Lit>,
		_lbl: &str,
	) -> Self {
		let vals = || dom.iter().flatten().skip(1);
		let x = if views.is_empty() {
			// Nothing to reuse, so the literals can be taken in one block.
			Lits::Range(new_named_var_range!(db, vals().count(), |i| {
				format!("{_lbl}≥{}", vals().nth(i).unwrap())
			}))
		} else {
			Lits::Explicit(
				vals()
					.map(|v| {
						views
							.get(&v)
							.copied()
							.unwrap_or_else(|| new_named_lit!(db, format!("{_lbl}≥{v}")))
					})
					.collect(),
			)
		};
		Self {
			dom: dom.clone(),
			x,
		}
	}

	/// The steps of a sequential decomposition over this variable.
	///
	/// Each step is a domain value `d` paired with the clause that holds unless
	/// the variable reaches `d` — from below when `geq`, from above otherwise.
	/// Whatever the constraint demands once `d` is reached can therefore just
	/// be disjoined onto that clause.
	///
	/// The step at the far end of the domain guards nothing, since the variable
	/// always reaches it; its clause is `false` and drops out, leaving the
	/// demand unconditional.
	pub(crate) fn steps(&self, geq: bool) -> Vec<(Coeff, BoolVal)> {
		let vals = self.dom.iter().flatten();
		if geq {
			vals.map(|d| (d, self.leq_val(d - 1))).collect()
		} else {
			vals.rev().map(|d| (d, self.geq_val(d + 1))).collect()
		}
	}

	/// The single literal of a two-valued variable, which on its own already
	/// distinguishes both of its values.
	pub(crate) fn single_lit(&self) -> Option<Lit> {
		(self.x.len() == 1).then(|| self.x.get(0).unwrap())
	}

	/// The literals of the encoding.
	#[cfg(test)]
	pub(crate) fn lits(&self) -> Vec<Lit> {
		self.x.to_vec()
	}

	/// The value represented under an assignment.
	#[cfg(test)]
	pub(crate) fn value<F: crate::Valuation + ?Sized>(&self, value: &F) -> Coeff {
		let reached = self.x.iter().filter(|&l| value.value(l)).count();
		self.dom
			.iter()
			.flatten()
			.nth(reached)
			.expect("the order literals cannot reach past the domain")
	}
}

#[cfg(test)]
mod tests {
	use std::rc::Rc;

	use rangelist::RangeList;
	use traced_test::test;

	use super::{BinEnc, IntVar};
	use crate::{
		solver::{cadical::Cadical, SolveResult, Solver},
		ClauseDatabaseTools, Cnf, Coeff, Valuation,
	};

	/// A handful of domains covering the shapes an encoding has to survive: a
	/// contiguous one, holes, negative values, a power-of-two span that fills
	/// the bits exactly, and a two-valued one.
	fn test_domains() -> Vec<RangeList<Coeff>> {
		vec![
			RangeList::from_iter([0..=3]),
			RangeList::from_iter([0..=4]),
			RangeList::from_elements([0, 1, 3]),
			RangeList::from_elements([2, 5, 6, 7, 9]),
			RangeList::from_elements([-3, -1, 0, 4]),
			RangeList::from_elements([-7, -6]),
			RangeList::from_elements([0, 5]),
		]
	}

	/// Every model of `cnf`, as the values each of `read` extracts from it.
	fn all_values(cnf: &Cnf, read: &dyn Fn(&dyn Valuation) -> Vec<Coeff>) -> Vec<Vec<Coeff>> {
		let mut slv = Cadical::from(cnf);
		let vars = cnf.get_variables();
		let mut solutions = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			solutions.push(read(&value));
			let no_good: Vec<_> = vars
				.map(|v| {
					let l = v.into();
					if value.value(l) {
						!l
					} else {
						l
					}
				})
				.collect();
			if slv.add_clause(no_good).is_err() {
				break;
			}
		}
		solutions.sort();
		solutions
	}

	#[test]
	fn all_three_encodings_agree_on_every_value() {
		// Whichever order they are asked for in, and whichever two or three of
		// them exist, every view of the variable must read the same value.
		for dom in test_domains() {
			for order in [[0, 1, 2], [2, 1, 0], [1, 2, 0], [2, 0, 1]] {
				let mut cnf = Cnf::default();
				let x = IntVar::new(dom.clone(), true, "x".to_owned());
				let mut read: Vec<Box<dyn Fn(&dyn Valuation) -> Coeff>> = Vec::new();
				for which in order {
					match which {
						0 => {
							let e = x.ord(&mut cnf).unwrap();
							read.push(Box::new(move |v| e.value(v)));
						}
						1 => {
							let e = x.bin(&mut cnf).unwrap();
							read.push(Box::new(move |v| e.value(v)));
						}
						_ => {
							let e = x.dir(&mut cnf).unwrap();
							read.push(Box::new(move |v| e.value(v)));
						}
					}
				}
				let solutions = all_values(&cnf, &|v| read.iter().map(|f| f(v)).collect());
				let expected: Vec<Vec<Coeff>> = dom.iter().flatten().map(|d| vec![d; 3]).collect();
				assert_eq!(solutions, expected, "dom {dom} asked in order {order:?}");
			}
		}
	}

	#[test]
	fn a_direct_encoding_represents_exactly_the_domain() {
		for dom in test_domains() {
			let mut cnf = Cnf::default();
			let dir = IntVar::new(dom.clone(), true, "x".to_owned())
				.dir(&mut cnf)
				.unwrap();
			assert_eq!(
				all_values(&cnf, &|v| vec![dir.value(v)]),
				dom.iter().flatten().map(|d| vec![d]).collect::<Vec<_>>(),
				"direct encoding of {dom}"
			);
		}
	}

	#[test]
	fn a_width_and_the_values_it_holds_are_inverses() {
		for bits in 0..=8 {
			let largest = BinEnc::largest_in(bits);
			assert_eq!(BinEnc::required_bits(largest), bits as usize);
			if bits > 0 {
				assert_eq!(BinEnc::required_bits(largest + 1), bits as usize + 1);
			}
		}
		// The widest a coefficient goes lands exactly on its largest value,
		// where computing it as a power of two would overflow.
		assert_eq!(BinEnc::largest_in(Coeff::BITS - 1), Coeff::MAX);
	}

	#[test]
	fn channelled_encodings_agree_on_every_value() {
		for dom in test_domains() {
			for bin_first in [false, true] {
				let mut cnf = Cnf::default();
				let x = IntVar::new(dom.clone(), true, "x".to_owned());
				// The order the encodings are asked for must not matter: whichever
				// arrives second is the one that triggers the channelling.
				let (ord, bin) = if bin_first {
					let bin = x.bin(&mut cnf).unwrap();
					(x.ord(&mut cnf).unwrap(), bin)
				} else {
					let ord = x.ord(&mut cnf).unwrap();
					(ord, x.bin(&mut cnf).unwrap())
				};

				let solutions = all_values(&cnf, &|v| vec![ord.value(v), bin.value(v)]);
				let expected: Vec<Vec<Coeff>> = dom.iter().flatten().map(|d| vec![d, d]).collect();
				// Exactly the domain, once each, with both views reading alike. A
				// disagreement or a value outside the domain would show up as an
				// extra row, a missing one, or a row whose two entries differ.
				assert_eq!(
					solutions,
					expected,
					"dom {dom} channelled with {} first",
					if bin_first { "bin" } else { "ord" }
				);
			}
		}
	}

	#[test]
	fn a_single_encoding_represents_exactly_the_domain() {
		for dom in test_domains() {
			let mut ord_cnf = Cnf::default();
			let ord = IntVar::new(dom.clone(), true, "x".to_owned())
				.ord(&mut ord_cnf)
				.unwrap();
			let mut bin_cnf = Cnf::default();
			let bin = IntVar::new(dom.clone(), true, "x".to_owned())
				.bin(&mut bin_cnf)
				.unwrap();

			let expected: Vec<Vec<Coeff>> = dom.iter().flatten().map(|d| vec![d]).collect();
			assert_eq!(
				all_values(&ord_cnf, &|v| vec![ord.value(v)]),
				expected,
				"order encoding of {dom}"
			);
			assert_eq!(
				all_values(&bin_cnf, &|v| vec![bin.value(v)]),
				expected,
				"binary encoding of {dom}"
			);
		}
	}

	#[test]
	fn encodings_are_created_once() {
		let dom = RangeList::from_elements([0, 1, 3]);
		let mut cnf = Cnf::default();
		let x = IntVar::new(dom, true, "x".to_owned());

		let _ = x.ord(&mut cnf).unwrap();
		let _ = x.bin(&mut cnf).unwrap();
		let (vars, clauses) = (cnf.num_vars(), cnf.num_clauses());

		// Asking again hands back what is already there: no new literals, and in
		// particular no second round of channelling clauses.
		let _ = x.ord(&mut cnf).unwrap();
		let _ = x.bin(&mut cnf).unwrap();
		assert_eq!((cnf.num_vars(), cnf.num_clauses()), (vars, clauses));
	}

	#[test]
	fn a_detected_variable_encodes_onto_the_literals_it_was_found_on() {
		// An integer recovered from a constraint that already mentions its
		// literals has to encode onto those rather than introduce its own, and
		// must still channel like any other variable.
		let mut cnf = Cnf::default();
		let dom = RangeList::from_elements([0, 1, 3]);
		let found: Vec<_> = (0..2).map(|_| cnf.new_lit()).collect();
		let vars_before = cnf.num_vars();

		let x = IntVar::new(dom.clone(), true, "x".to_owned());
		x.set_ord_view(1, found[0]);
		x.set_ord_view(3, found[1]);
		let ord = x.ord(&mut cnf).unwrap();
		assert_eq!(
			cnf.num_vars(),
			vars_before,
			"the order encoding should reuse the literals it was given"
		);

		let bin = x.bin(&mut cnf).unwrap();
		let solutions = all_values(&cnf, &|v| vec![ord.value(v), bin.value(v)]);
		assert_eq!(
			solutions,
			dom.iter().flatten().map(|d| vec![d, d]).collect::<Vec<_>>()
		);
	}

	#[test]
	fn a_two_valued_variable_shares_its_literal() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(RangeList::from_elements([0, 5]), true, "x".to_owned());
		let _ = x.ord(&mut cnf).unwrap();
		let (vars, clauses) = (cnf.num_vars(), cnf.num_clauses());

		// The order literal already tells the two values apart, so the binary
		// encoding is a view onto it rather than fresh bits to channel against.
		let _ = x.bin(&mut cnf).unwrap();
		assert_eq!(
			(cnf.num_vars(), cnf.num_clauses()),
			(vars, clauses),
			"a two-valued variable should not pay for a second encoding"
		);
	}

	#[test]
	fn a_variable_may_appear_twice_in_one_constraint() {
		// Reading the same variable more than once, as `x + x` would, must not
		// trip over the borrow the accessors take internally.
		let mut cnf = Cnf::default();
		let x = IntVar::new(RangeList::from_iter([0..=3]), true, "x".to_owned());
		let y = Rc::clone(&x);
		let encs = [x.bin(&mut cnf).unwrap(), y.bin(&mut cnf).unwrap()];
		let ords = [x.ord(&mut cnf).unwrap(), y.ord(&mut cnf).unwrap()];

		let solutions = all_values(&cnf, &|v| {
			vec![
				encs[0].value(v),
				encs[1].value(v),
				ords[0].value(v),
				ords[1].value(v),
			]
		});
		assert_eq!(
			solutions,
			(0..4).map(|d| vec![d; 4]).collect::<Vec<_>>(),
			"both handles are the same variable and must read alike"
		);
	}
}
