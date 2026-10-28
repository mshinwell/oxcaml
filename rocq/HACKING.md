# Modelling compiler passes in Rocq

Some analyses in the compiler are written as Rocq models: the analysis is
defined in Rocq, its intended meaning is stated alongside, the theorems
connecting the two are proved, and the OCaml that the compiler builds is
*extracted* from the Rocq definitions. The extracted `.ml`/`.mli` files are
committed and are the implementation; the compiler's build does not run
Rocq. This page is for anyone (a person or a coding agent) adding to or
changing such a model. It records how the models are laid out, what is
trusted, and what was learned writing the first ones.

The first models are the loop analyses behind `-ssa-delete-empty-loops`
(`backend/ssa/loop/rocq/`); read them as worked examples, starting with
the reading guide at the top of `LoopComparisons.v`.

The pass currently accepts only integer constants, additions, subtractions
and comparisons, with Goto/Switch control flow. `SsaSemantics.v` gives
instruction-by-instruction execution for that fragment and the extracted
whitelist. `SsaExecution.v` derives operation equations for available
values from execution and structural SSA well-formedness.
`LoopExecution.v` connects execution to header revisits and back-edge
parameter passing. Composition into the termination argument and proof of
the graph rewrite remain unfinished: `find_deletions_spec` is still an
analysis-certificate theorem, not a behavior-preservation theorem.

## The directories

Each directory is a Rocq library (`rocq/Makefile` maps them):

| Directory                | Library        | Contents                                      |
|--------------------------|----------------|-----------------------------------------------|
| `rocq/`                  | `OxCamlStdlib` | Models of OxCaml's own types (`int`, `Int64`, lists, exceptions as options), generic arithmetic (`IntArith.v`), proof helpers, and the extraction directives mapping them onto OxCaml's functions (`OxCamlExtract.v`) |
| `backend/rocq/`          | `OxCamlBackend`| Backend-wide definitions: the semantics of `Cmm.integer_comparison`, the model's copy of `Operation.t` |
| `backend/ssa/rocq/`      | `OxCamlSsa`    | The SSA graph as the models see it: `SsaModel.v` (the abstract interface), `SsaGraph.v` (properties of blocks, terminators and uses that any pass may need), `SsaDominance.v`, `SsaSemantics.v` (execution of the restricted integer fragment), `SsaExecution.v` (well-formedness and available-value equations) |
| `backend/ssa/loop/rocq/` | `OxCamlLoop`   | The loop analyses, the operational bridge in `LoopExecution.v`, and `Extract.v`, which extracts the implementation |

Put a definition or lemma where its OxCaml counterpart would live. A fact
about lists goes in `OxCamlList.v`, about machine integers in
`OxCamlInt.v`, `OxCamlInt64.v` or `IntArith.v`, about terminators or
values of any SSA graph in `SsaGraph.v`, about dominance in
`SsaDominance.v`; only what is specific to a pass stays in its file. The
same question one asks of an OxCaml module ("is this really about loops?")
applies.

## The workflow

With Rocq and the repository's `ocamlformat` on `PATH`:

1. Edit the `.v` files.
2. `make -C rocq all` checks every proof and regenerates the extracted
   files (about ten seconds from scratch). It fails if a proof breaks, and
   it refuses an extraction that produces a module it does not expect
   (see "Adding a module" below).
3. Review `git diff` of the extracted `.ml`/`.mli`: it should show exactly
   the change you meant. Never edit those files by hand; change the `.v`
   and regenerate.
4. `make -s boot-compiler`, then the tests of the pass (for the loop
   passes, `testsuite/tests/backend/ssa/loop/` and the unit test alias
   `dune build @oxcaml/tests/backend/ssa/runtest`), then `make -s fmt`.
5. Commit the `.v` files and the regenerated `.ml`/`.mli` together.

After renaming or moving `.v` files, stale `.vo` files can shadow the new
ones: `touch` the sources (or `make -C rocq clean`) before rebuilding.

### Adding a module

A new `.v` file goes in the library's list in `rocq/Makefile` (`STDLIB`,
`BACKEND`, `SSA` or `LOOP`). If it is extracted (it defines functions the
compiler runs, as opposed to only lemmas), also add its `.ml`/`.mli` to
`SSA_MODULES` or `LOOP_EXTRACTED` there, add the module to the list in the
root `dune` file next to the other extracted modules, and mention it in
the header of `Extract.v`. Extraction writes every file into
`backend/ssa/loop/rocq/`; the Makefile moves the `OxCamlSsa` ones next to
their sources. A module whose every definition is mapped onto OxCaml's own
functions extracts to an empty file, which the Makefile deletes.

## The layout of a model file

Every model file has a header and four parts, marked by banners:

1. **The definitions.** The analysis itself, written to mirror the shape
   of the OxCaml it replaces: same decomposition into functions, same
   names where possible, booleans for checks. This is what is extracted.
2. **The intended meaning.** `Prop`s saying what the analysis's answers
   are supposed to mean, in terms of the model's observations of the
   graph and of mathematical integers (`Z`). Each conjunct of a
   specification is a named predicate (`exits_only_to`,
   `no_infinite_header_run`, `params_are_dead_bivs`, ...), so that the
   specification reads as a sentence and needs no comment explaining its
   parts. Hypotheses about the compiler that the model cannot prove (what
   an operation computes, what dominance means, how a run of a loop goes)
   are stated here too, as `Hypothesis` in a `Section` or as the fields
   of a `Record` such as `infinite_header_run`. A `Remark` showing that
   such a hypothesis is satisfiable (`op_semantics_lsr_zero`) sits right
   after it: it documents the statement rather than serving a proof.
3. **Lemmas used by the proofs.** Stepping stones. Each non-trivial one
   has a comment before it saying, in plain words, what it states.
4. **The theorems.** The correctness claims, each with a comment before
   it. Their statements mention only parts 1 and 2.

The header says what the file models, where its extraction lives, which
files to read first, what the main theorems establish, and what is
trusted. Parts 1 and 2 are what a reviewer checks by eye; Rocq checks the
rest. The theorems only ever go one way: a boolean check answering `true`
implies its meaning. Nothing is claimed about `false` answers, so the
analyses may be conservative wherever that is convenient (size limits,
overflow, unrecognised shapes).

## Modelling OxCaml

- **`int`** is Rocq's primitive signed 63-bit integer (`Sint63`), which is
  OxCaml's `int` exactly; `to_Z` reads it as a `Z`. Literals are named
  (`zero`, `one`, `minus_one`, `two` in `OxCamlInt.v`) so that extraction
  prints OxCaml literals; a new literal needs an
  `Extract Inlined Constant ... => "..."` line in the `*Extract.v` file,
  and the two must be kept in step (see `FourierMotzkinExtract.v`).
  Arithmetic wraps: `Sint63.add_spec` and friends give the result modulo
  `2^63` as `cmod`; `OxCamlInt.v` has the lemmas that let `lia` work on
  such sums.
- **`Int64`** is a `Parameter` type with axioms (`OxCamlInt64.v`), each the
  documented behaviour of one OxCaml operation. Do not put `Definition`s
  inside `Module Int64` there: they would be extracted into a module
  shadowing OxCaml's `Int64`.
- **Exceptions** become `option`: a function that may raise returns `None`
  instead, and `let* x := m in k` (`OxCamlOption.v`) propagates it.
  `map_opt` and `filter_map_opt` are `List.map` and `List.filter_map`
  with such callbacks.
- **Arrays** are lists, indexed with `nth_int` (`None` where OxCaml would
  raise), compared in length with `same_length`. `OxCamlList.fold_left`
  has OxCaml's argument order.
- **The compiler's data**: blocks are a `Parameter` type in
  `SsaModel.v`, with the few observations the models make of them
  (`terminator`, `params`, `predecessors`, ...) also as `Parameter`s,
  each realised at extraction by a function of `Ssa`, at most wrapped
  with `Array.to_list`. Values, instructions and terminators are
  `Inductive` types there, copying the compiler's with the fields the
  models read, and `Extract Inductive` maps each back onto the
  compiler's type with a match function (its last argument) that reads
  the compiler's data; so the models match on the compiler's values
  directly, and the operation defining a value is `Operation.v`'s copy of
  `Operation.t` (`backend/rocq/`), kept in step with
  `backend/operation.mli`. To observe something new about a block: add
  the `Parameter` and its `Extract` directive in `SsaModelExtract.v`.
  `SsaModel.v` proves nothing; what the proofs rely on about an
  observation is a hypothesis of the theorem using it.
- **Extracted inductives standing for compiler types** must list their
  constructors in the same order as the OxCaml type
  (`Extract Inductive ... [ ... ]`), and a comment must say which type to
  compare with.
- **Recursion** that Rocq cannot see terminates is written either with
  `Function ... {measure ...}` and a decreasing measure (`gcd64`), or with
  an explicit "fuel" list and a completeness theorem showing that the
  fuel the caller passes is enough (`NaturalLoop.walk`).
- **Mutable state** is threaded explicitly: a context is passed in and
  returned, so that each function is a pure function of its arguments
  (`AffineSsa.ctx`).

### What is trusted

The trusted base is small and must stay listed in the headers:

- the axioms about `int`, `Int64` and the list functions mapped onto
  OxCaml's (`OxCamlInt64.v`, `OxCamlList.v`);
- the `Parameter`s with axioms standing for a few lines of OxCaml that
  are easier to review than to model (`IntArith.v`'s overflow tests);
- the extraction directives, which say which OxCaml value realises each
  model definition (`*Extract.v`), including the match functions written
  in them;
- the hypotheses the theorems take about the graph.

Everything else is proved. Never `Admitted`. When something cannot be
proved, state it as a hypothesis where it is used and say so in the
header.

## Extraction pitfalls

- `&&` is extracted to OxCaml's short-circuiting `( && )`, but a `let` is
  evaluated eagerly: bind an expensive check inside the `if` or `&&`
  that needs it, not in a `let` before it (`find_deletions` runs the
  termination analysis last for this reason).
- An extracted module may depend on compiler modules, but a compiler
  module that the extraction maps onto (such as `Ssa`) must not depend
  on an extracted one, or dune reports a dependency cycle.
- Extraction puts the same `open` lines at the top of a `.ml` and its
  `.mli`; the Makefile strips the unused ones from the `.mli`, where only
  types can be referred to.
- `Separate Extraction` extracts only what the listed entry points use;
  an unused definition silently disappears from the `.ml`. Keep the entry
  points in `Extract.v` to what the compiler calls.
- Everything extracted is run through `ocamlformat` by the Makefile, so
  `make fmt` passes without touching the generated files.

## Writing the statements

- Say what the booleans mean with `Prop`s over the observations of
  `SsaModel.v`, not over the compiler's data.
- Use the notations `SsaModel.v` defines (`a --dom--> b` for `a`
  dominating `b`) in parts 2 to 4, where a statement is read by eye.
  Part 1 is code and calls the primitives as the compiler does.
- Prefer a per-element statement to a counting one: "every parameter at
  position `k` has a dead induction variable with `param_index = k`" is
  checkable; "there are as many as parameters" is not what the pass
  relies on.
- The existential witnesses in a specification should be things the
  analysis actually computes (`exists args, goto_args ... = Some args`),
  so that the proof is a reading-back of the code.
- Hypotheses about machine semantics are stated once, in one place
  (`op_semantics`, `infinite_header_run`), and every file that needs them takes
  them as hypotheses rather than restating them.
- A part-1 definition may be sound only for inputs with a property it
  does not check: `LoopTermination.analyze` is sound only for the basic
  induction variables of one loop. Such a precondition is a named part-2
  predicate (`bivs_of_loop`), is a hypothesis of the part-4 theorem, and
  is named in the comment before the definition. It never goes into the
  definition's type (a subset type would put proofs into part 1 and tie
  the extracted code to the meaning), and it is never assumed of the
  program: where the definitions are composed, the producer's theorem
  discharges it (`InductionVar.analyze_spec`), so that the top-level
  theorem `find_deletions_spec` has no hypothesis but the trusted
  meaning of the primitives.
- The meaning of a run (`infinite_header_run`) mentions no part-1
  function beyond the primitives of SsaModel.v and the fields of the loop
  record: a hypothesis stated through an analysis function would silently
  trust that function. A property of an analysis result is stated as
  what it means (`loop_invariant_value`) and tied to the function by a
  read-back theorem (`is_loop_invariant_spec`).

## Proof style

- Statements and proofs stay under 80 columns.
- Case splits that the reader does not need to follow are written inline
  with `[ ... | ... ]`; those that carry an argument use bullets
  (`-`, `+`, `*`), with a comment when the case is not evident from the
  pattern.
- To read a boolean check back: `unfold` it, `destruct (f x) eqn:H;
  [ | discriminate ]` on each test, `apply andb_true_iff in H` on each
  `&&`, `rewrite forallb_forall in H` on each `forallb`, `cbv zeta` and
  `cbv iota` to step a `let` or a `match` on a known constructor,
  `injection H as <-` to read a `Some`.
- Equations on `int` go through `to_Z` and `lia`; `case_int_tests`
  (`OxCamlInt.v`) and `case_zcmp` (`ZTactics.v`) split on the boolean
  comparisons in a goal first.
- `Opaque helper` keeps a helper folded while the function calling it is
  unfolded; `Transparent` it afterwards.
- `functional induction` proves properties of a `Function`; the
  decreasing measure is proved once, at the definition.
- A `Section` with `Variable`s and `Hypothesis`es shares the setting of
  many lemmas (the run of a loop in `LoopTermination.v`); the lemmas are
  generalised over them at `End`.
- Name hypotheses after what they say (`Hexit`, `Hwf`), not `H0`, `H1`.
- Do not comment what a named predicate already says; do comment every
  non-trivial lemma, and every case of a long proof that is not evident.

## Checklist before pushing

- `make -C rocq all` passes and the extracted diff is the intended one.
- `make -s boot-compiler`, the pass's tests and `make -s fmt` pass.
- New definitions sit in the most generic file that fits; new modules are
  registered in `rocq/Makefile`, `dune` and `Extract.v`.
- Every non-trivial lemma and theorem has a comment; no comment restates
  a named predicate.
- The headers list what is trusted, and nothing is `Admitted`.
