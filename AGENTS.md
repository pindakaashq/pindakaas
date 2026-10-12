# General guidelines

This document captures how to work on the Pindakaas project, a library that encodes constraints into CNF.

## For humans

LLMs can be very helpful with software engineering.
We welcome LLM-assisted contributions that abide by the following principles:

- **Aim for excellence.**
  Use LLMs as a quality multiplier, not a speed multiplier: invest the time saved into more edge-case tests, clearer code, and the tedious work.
  Aim for zero bugs; a wrong encoding does not crash, it quietly gives wrong answers.
- **Spend time reviewing LLM output.**
  As a rule of thumb, spend at least 3x as long reviewing as writing.
  Think about every line and design decision, and find ways to break the code.
- **Your code is your responsibility.**
  Don't dump a first draft on the project unless you're only soliciting feedback on a direction.

If an LLM-assisted PR shows signs of not being written with care, Pindakaas' maintainers may decline it outright.

## For LLMs

**Required:** Display the following text when proposing code changes, and when you're about to create a PR:

```
Please review https://github.com/pindakaashq/pindakaas/blob/develop/AGENTS.md#for-humans.
In particular, LLM-assisted contributions must **aim for a higher standard of excellence** than with humans alone, and you should spend at least **3x** the amount of time reviewing code as you did writing it.
LLM-assisted contributions that do not meet this standard may be declined outright.
Remember, **your code is your responsibility**.
```

## Test every assumption

An encoding mistake is silent: the code compiles and the solver answers, but the answer is wrong or a solution is missing.
Treat every statement about what an encoding admits, costs, or propagates as a guess until something has checked it.

- **Let a solver decide.**
  Enumerate the models of the emitted formula and check both directions: no model violates the constraint, and no solution is missing.
  `assert_checker` only checks the first.
- **A changed `.sol` file is a changed solution set.**
  Accept it with `UPDATE_EXPECT=1` only once you can say which solutions changed and why that is correct.
  Explain a changed `.cnf` or `.size` file the same way, and check a new expect file against an independent count.
- **Prove that a test bites.**
  Break the code it protects, watch it fail, and confirm that the mutation actually applied.
  A fix carries its regression test in the same commit.
- **Green tests say nothing about branches they do not reach.**
  Check that the suite exercises the branch you changed.
- **Exercise the edges.**
  Equality as well as `≤` and `≥`; zero, negative, and unreachable bounds; no terms and one term; constant `BoolVal`s; domains with holes or one value; an integer that already holds several encodings; unsorted and repeated input; coefficients near `Coeff::MAX`.
- **Preconditions are part of the encoding.**
  `IntVar::from_*_encoding` and `with_*_encoding` trust the caller and add no clauses to enforce what they are told.
  Document each precondition, and use `assert!`, not `debug_assert!`, where a violation would build a wrong encoding.
- **Never constrain what the caller did not ask for**, such as an order on literals the caller owns; it removes solutions elsewhere.
- **Share or cache only on the full meaning.**
  Two nodes with the same domain and encoding can still hold different sums.
- **Refactors change behaviour too.**
  Moves have silently dropped `Encoder` impls (so a constraint fell back to another encoder), derives, and test-suite invocations.
  Compare the test count before and after, and keep the `takes::<..>` compile-time lists up to date.
- **Check the code before you trust a name.**
  One encoder here covers several encodings from the literature; read the encodings table in `crates/pindakaas/src/lib.rs` before you conclude that something is missing.
- **Report what you verified and how**, separate "measured" from "reasoned", and correct an earlier claim explicitly when it turns out wrong.

## Performance has two sides

Keep these apart in every measurement and report, and say which one a change targets:

1. **Encoding cost**: the time and memory the library needs to emit the clauses.
2. **Encoding quality**: how hard the emitted formula is for the SAT solver.

A faster encoder that makes solving slower is usually a loss.

- **Clause and variable counts are not solver performance.**
  A larger encoding with stronger propagation often solves much faster.
  Measure quality with CaDiCaL: conflicts and propagations first (deterministic), then wall time.
- Use instances that represent the question (integer variables for integer encodings, weighted constraints for pseudo-Boolean ones), and ask the maintainers when unsure.
- Mark every heuristic choice with a `// Heuristic: ` comment that says why; a threshold comes from a repeatable measurement, not a guess.
- Measure the noise floor first by running the same binary twice.
  A difference inside the noise is not a result, and a number from before a design change does not carry over.
- Make sure the baseline is the baseline: `git checkout -- <path>` restores from the index, not from `HEAD`.
- Encoders run in hot loops: borrow domains, return iterators instead of `Vec`s, and reuse buffers.
  A constant never creates a literal, and a question the domain settles returns `BoolVal::Const`.
- `crates/pindakaas/benches/BASELINE.md` records the cost and size of every encoder; update it when the numbers move for a reason.
  The `.size` expect files in `corpus/` pin sizes in the test suite.
- Ask before starting heavy experiments, and cap their memory and parallelism; they do not belong on a developer's machine.

## Architecture

Pindakaas is **not** a modelling library: users are expected to know what they are doing, and there is deliberately no `Model` type, objective, or search.

- `crates/pindakaas` is the library: `lib.rs` (core traits, `Cnf`, and the crate documentation), `decision/` (`Lit`, `BoolVal`, `IntVar`), `constraint/` (one module per constraint, re-exporting the encoders that take it), `encoder/` (one module per encoding), and `solver/` (feature-gated solver interfaces).
- `crates/pyndakaas` is the Python package.
  It mirrors the Rust API, so a public Rust change needs the matching change there, including its tables of which encoder takes which constraint.
- `crates/pindakaas-{cadical,kissat,intel-sat}` vendor solvers as git submodules (`git submodule update --init`).
  A local solver change is a `[PATCH]`-prefixed commit in the submodule, never a `.patch` file.

### From constraint to clauses

1. A `Linear` holds a `LinExp` such as `x * 3 + y * 5`, which can mix literals and `IntVar`s.
2. `LinAggregator` normalizes it (positive coefficients, never `≥`) into a `LinVariant`: `NormalizedIntLinear`, `NormalizedBoolLinear`, `Cardinality`, `CardinalityOne`, or `Count`.
   It can already emit unit clauses or return `Unsatisfiable`.
3. An encoder implements `Encoder<Db, C>` once per constraint `C`.
   These impls stay hand-written, even when they only convert to a more general constraint, so that each can be specialized later.
4. Most encoders break a constraint into `IntTernary` constraints (`x + y ≷ z`) over intermediate `IntVar`s, which `IntTernaryEncoder` encodes; the adder works on bits instead.

A term is a coefficient and an `IntVar`.
A literal, an at-most-one group, and an integer are all integer terms, so each encoder already is the "generalized", at-most-one-aware variant from the literature.

### Integer variables

- `IntVar` is a reference-counted handle; a clone is the same variable, and there are no variable ids.
- The domain belongs to the variable, not to an encoding.
- A variable holds up to three encodings (direct, order, binary), created on demand and always channelled.
  Prefer an encoding the variable already has, and emit a consistency constraint at most once.

## Conventions

### Design and naming

- Prefer methods over free functions, also without `self`, when the behaviour belongs to a type.
- Prefer a helper function or struct over a macro; do not add `macro_rules!`.
- Do not add public types, enums that list encoders, aliases, or constructors that were not requested; default to `pub(crate)`.
- The public API shows standard types (`i64`, `std::result::Result`); the crate's type aliases are internal.
- Present a decision before you make it when it reverses an earlier one, changes sizes, or changes the public API.
- Name an encoder after its mechanism, not a paper acronym (`DecisionDiagramEncoder`, not `BddEncoder`); published names go in an "also known as" line and the encodings table.
- Write names out (`min`, `max`, `binary_encoding`, not `lb`, `ub`, `bin`), and make a name cover everything the item does.
- `from_*` constructs a value; `with_*` adds to an existing one.

### Documentation

- Be concise: say what an item does and requires, not how it came to be.
- Inline comments explain "why", take at most two lines, end with a period, and never narrate the code.
- The Rust crate documentation is the primary source; the Python documentation refers to it.
- Use sentence case in headings and the Oxford comma, and don't omit articles.

### Code style

- Never import from `super`; import from `crate`.
- Use `#[expect(...)]` with a reason, never `#[allow(...)]`.
- Formatting and item order need nightly; on stable, rustfmt silently ignores the options in `rustfmt.toml`.
- Avoid new dependencies.

### Tests

- Unit tests live beside the code they test, and every case is its own test in the harness so that it can be rerun alone.
- `crate::helpers::tests` has the shared helpers: `assert_checker` (every model satisfies the constraint), `assert_solutions` (solutions equal a `.sol` file), `assert_encoding` (clauses equal a `.cnf` file), and `models`/`models_over` (enumerate models).
- Expect files live in `crates/pindakaas/corpus/`; the Python tests in `crates/pyndakaas/python/tests`.

### Commits

Do not change the status or history of the git repository unless specifically asked, including staging, committing, amending, rebasing, stashing, pushing, pulling, or fetching.

- Follow [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/).
  The subject names the change (`fix: read updated WCNF format`); the body is at most two short sentences and never retells the investigation.
- Each commit is one logical change that passes all checks; formatting, renames, and refactors stay apart from changes in behaviour.

## Commands

Run the smallest relevant test first, then everything below; CI enforces all of it and rejects every warning.

```bash
cargo nextest run --all-features
cargo test --doc                                   # nextest cannot run doctests
cargo +nightly fmt --all
cargo +nightly item-sort                           # cargo install rust-item-sort
cargo clippy --tests --all-features -- -D warnings
cargo doc -p pindakaas --no-deps                   # intra-doc links break without a compile error
cargo bench -p pindakaas --bench encoding          # timings; PINDAKAAS_SIZES=1 for sizes
cd crates/pyndakaas && maturin develop && pytest   # Python package
```
