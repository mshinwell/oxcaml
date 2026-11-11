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
and `-ssa-bounds-check-elim` (`backend/ssa/loop/rocq/`); read them as
worked examples. `DeleteEmptyLoops.v`, `DeleteEmptyLoopsProofs.v` and
`DeleteEmptyLoopsSpec.v` show the three files of a model.

Start review of empty-loop deletion at `LoopEligibilitySpec.v`: read
`eligible_entry` and `find_deletions_eligible_statement`, then their
imported semantics and contracts. The statement says, for every header/exit pair
the pass reports, that the execution from the header first arrives at
the exit after finitely many steps (`SsaSemanticsSpec.steps_until`) and
agrees with the first header execution on every register read before
its next definition. Its premises are two records, `finished_graph`
(`SsaProgressSpec.v`: what the SSA builder guarantees) and
`reached_header` (`SsaContextSpec.v`: bound inputs and an observed prefix
to the header). It assumes no recurrence, invariant bound, guard outcome,
progress or finite exit, and the discovered loop does not appear in the
statement. The mechanically rewritten graph, renaming and cleanup are
deliberately outside this proof's scope.

Start review of bounds-check elimination at `BoundsCheckExecutionSpec.v`:
`find_eliminations_sound_statement` says, and `BoundsCheckExecutionProofs.v`
proves, for every block/target pair the pass reports, that every run of
the observation semantics (`SsaContextSpec.context_steps`) from the entry
to the end of the block steps to the target, so the block's two-way branch
on an unsigned comparison may become a jump. The decision is
`BoundsCheckElim.v`, over the guard facts of `AffineSsa.v` (with the index
linearized modulo 2^64, `linearize_goal`) and the bounds of loop counters
certified in `InductionRange.v`, whose meaning is `InductionRangeProofs.v`
and whose operational meaning is
`InductionRangeExecutionProofs.counter_bounded`. Its premises are
`finished_graph`, bound inputs and the observed run; nothing is skipped,
so no liveness or finite-exit argument is involved.

The loop whitelist remains integer constants, additions, subtractions and
comparisons, with Goto/Switch control flow. `SsaSemanticsSpec.v` defines
exact execution; its evaluator additionally supports immediate shifts and
or for computations before the loop, and the target-specific operations
the target itself reads as linear combinations of their arguments
(`Operation.specific_linear`, trusted), which re-tag the counters of
`for` loops. `SsaContextSpec.v` overapproximates word observations in the
unchanged prefix: opaque instructions can produce
arbitrary bounded outputs, and opaque terminators can take CFG successors
with arbitrary parameter values. Memory effects are unconstrained, not
no-ops. Trap markers step without touching a register, and the exception
handler of a Call or Raise is one of its successors, so a prefix through
a `try` is represented like any other. The extracted `graph_supported`
gate rejects any graph containing a modeled operation family with other
than one result, the one instruction shape with no rule; it checks every
block, so such code even after or beside the loop prevents deletion.
Opaque loads and calls are allowed. This avoids a full memory/call/vector
semantics; the correspondence of word observations to compiler operations
remains a review boundary. The simulation argument from `eligible_entry`
to the rewritten function is written out in ROCQ-REVIEW-GUIDE.md (section
4.7), which also says how to review the development as a whole.

`SsaExecutionProofs.v` supplies definition-site and frame facts;
`SsaContextProofs.v` proves available-value equations and execution
invariants once for both exact and opaque steps. `SsaLivenessSpec.v`
defines reads before redefinition; `SsaProgressProofs.v` derives progress
from bound operands. `LoopExecutionProofs.v` uses accessibility to construct
finite traversals to the next header or exit.
`LoopInvariantExecutionProofs.v` proves bound constancy on finite
segments; `LoopCounterExecutionProofs.v` iterates up to the arithmetic
exit witness. `LoopValueSnapshotProofs.v`, `LoopGuardExecutionProofs.v`
and `LoopRangeExecutionProofs.v` connect affine entailment to the actual
prefix, including duplicate Switch edges. `LoopLiveOutProofs.v` derives
live-out agreement. `InductionRangeExecutionProofs.v` carries a counter's
certified bounds along every observed step of its loop;
`BoundsCheckExecutionProofs.v` evaluates a removed check under the snapshot
valuation.

The public theorem's non-algorithmic premises are the fields of
`finished_graph` (structural SSA/dominance metadata, edge multiplicities,
Goto/parameter layout, the definition table) and of `reached_header`
(bounded live function inputs, the observed prefix, and defined Switch
indices from the reached header onward). Out-of-range Switch indices are
undefined behavior in SSA.
The extracted gate enforces at most $2^{32}$ graph blocks with a bounded
list walk. `find_deletions_supported` proves `graph_size_supported` and
prefix instruction coverage, so graph size is not a public theorem premise.
Finite exit is constructed directly; definedness uses classical case
splits, not new semantic axioms.

`find_deletions_spec` and `find_eliminations_spec` are the
analysis-certificate theorems.
`well_formed_ssa` formally assumes that finished graph blocks are
structurally reachable, as the OCaml builder's reachability pass ensures;
it does not assume dynamic feasibility.

## The directories

Each directory is a Rocq library (`rocq/Makefile` maps them):

| Directory                | Library        | Contents                                      |
|--------------------------|----------------|-----------------------------------------------|
| `rocq/`                  | `OxCamlStdlib` | Models of OxCaml's own types (`int`, `Int64`, lists, exceptions as options) and generic arithmetic (`IntArith.v`), each a file of definitions and axioms with its lemmas in a `*Proofs.v`; proof helpers (`ZTactics.v`); and the extraction directives mapping the models onto OxCaml's functions (`OxCamlExtract.v`) |
| `backend/rocq/`          | `OxCamlBackend`| Backend-wide definitions: the semantics of `Cmm.integer_comparison` (with `IntegerComparisonProofs.v`), the model's copy of `Operation.t` |
| `backend/ssa/rocq/`      | `OxCamlSsa`    | The SSA graph as the models see it, each model split into Spec, implementation and Proofs files (see "The layout of a model"): `SsaModel.v` (the abstract interface), `SsaGraph*` (terminators, edges and uses), `SsaDominance*` (dominance, paths and program points), `SsaSemantics*` (execution of the restricted integer fragment), `SsaExecution*` (well-formedness and available-value equations), `SsaLiveness*` (reads before redefinition), `SsaProgress*` (the `finished_graph` contract, definedness and progress), `SsaContext*` (opaque surrounding computations and the `reached_header` contract) |
| `backend/ssa/loop/rocq/` | `OxCamlLoop`   | The loop analyses, each an implementation file and a `*Proofs.v`; the operational proofs in `LoopExecutionProofs.v`, `LoopInvariantExecutionProofs.v`, `LoopCounterExecutionProofs.v`, `LoopValueSnapshotProofs.v`, `LoopGuardExecutionProofs.v`, `LoopRangeExecutionProofs.v`, `LoopLiveOutProofs.v` and `InductionRangeExecutionProofs.v`; the statements to review in `LoopEligibilitySpec.v`, `DeleteEmptyLoopsSpec.v` and `BoundsCheckExecutionSpec.v`, proved in `LoopEligibilityProofs.v`, `DeleteEmptyLoopsProofs.v` and `BoundsCheckExecutionProofs.v`; and `Extract.v`, which extracts the implementation |
| `middle_end/flambda2/rocq/` | `OxCamlFlambda2` | The beginning of a semantics of Flambda 2, with nothing extracted: `FlambdaMap*` (finite maps and sets keyed by names, the one representation of environments), `FlambdaModel.v` (the terms of the fragment covered so far), `FlambdaSemantics*` (execution, behaviours, equivalence and refinement), `FlambdaWellFormed*` (static bindings at toplevel only, the well-formedness of a unit; and that what a static name is bound to never changes in a run), `FlambdaControlFlow*` (rewrites of control flow stated and proved against the semantics), `FlambdaContext*` (contexts, and that refinement and equivalence are preserved under them), `FlambdaNominal*` (renamings, free names, and binders as name abstractions), `FlambdaAlpha*` (the group action, equivariance, and alpha-equivalence with its soundness), `FlambdaApply*` (function calls and inlining), `FlambdaStatic*` (first facts about `Let_static`), `FlambdaCompare*` (a decision that two expressions are the same up to bound names, proved sound), `FlambdaNormalise*` (normalising a term by proved rewrites: inlining direct calls of known code, removing unused `Let`s, folding constants), `FlambdaUnusedStatics*` (removing unused static bindings, under environments in which their names do not occur), `FlambdaValidate*` (the whole check of a unit before and after Simplify, and that what it accepts is correct for the unit run on its own); see "The semantics of Flambda 2" below |
| `middle_end/flambda2/types/rocq/` | `OxCamlFlambda2Types` | A first, naive model of Flambda types and typing environments, with nothing extracted: `FlambdaTypes*` (types, what it means to satisfy a typing environment, refinement relative to one, following aliases, going under a `Let`), `FlambdaAliases*` (following aliases through a whole term, an equivalence) |

Put a definition or lemma where its OxCaml counterpart would live. A fact
about lists goes in `OxCamlListProofs.v`, about machine integers in
`OxCamlIntProofs.v`, `OxCamlInt64Proofs.v` or `IntArithProofs.v` (a
definition, in the file without the suffix), about terminators or values
of any SSA graph in the `SsaGraph` files, about dominance in the
`SsaDominance` files; only what is specific to a pass stays in its files.
The same question one asks of an OxCaml module ("is this really about
loops?") applies, and then the question of "The layout of a model" below
("does a statement to be reviewed need it?") picks the file.

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
   passes, the `expect.opt` tests in `testsuite/tests/backend/ssa/loop/`,
   whose `[%%expect_ssa]` blocks show the SSA each function ends up with
   and how many loops were deleted or checks removed from it, and the
   unit test alias
   `dune build @oxcaml/tests/backend/ssa/runtest`), then `make -s fmt`.
5. Commit the `.v` files and the regenerated `.ml`/`.mli` together. (Not
   so for the Flambda 2 semantics on a workstream branch: see "Who commits
   the extracted files" under "Testing Simplify against the semantics".)

After renaming or moving `.v` files, stale `.vo` files can shadow the new
ones: `touch` the sources (or `make -C rocq clean`) before rebuilding.

### Printing the review obligations

Run `make -s -C rocq assumptions > assumptions.txt` to build and audit every
module listed in this Makefile. The report has two parts:

1. `rocq check -o` rechecks the compiled modules and lists global axioms and
   abstract constants, including those in imported libraries. It also
   reports unsafe typing assumptions. This is a whole-context inventory,
   not the minimal dependencies of one theorem.
2. `Print Namespace` prints constant types for each project module,
   including nested modules, theorem premises generalized from `Section`s,
   and the projections of contract records. Unlike `Search`, it does not
   hide names through a search blacklist. This part includes proved
   theorems too; it is not another list of axioms.

Between the two parts the target checks the axioms against the trust
ledger, `rocq/TRUST-LEDGER.md`, and fails if they differ. Every axiom of
the first part must be listed there, with its reason; every axiom listed
there must be in the first part; and the statements of the Flambda 2
libraries must depend only on the axioms of the ledger's section
"Flambda 2" (so that, for one, none comes to use classical logic). An
axiom or a `Parameter` added to a model is therefore added to the ledger
in the same change. For the Flambda 2 work that needs a reviewer's
sign-off, and the aim is for the ledger to shrink.

For a particular theorem, `Check @find_deletions_eligible.` (or
`Check @find_eliminations_sound.`) shows its full premises and
`Print Assumptions find_deletions_eligible.` gives its global axiom
dependencies. Named predicates still need inspection in the source:
declaration types do not print definition bodies, and an assumption audit
cannot check that the semantics or extraction match the compiler.

The target derives its module list from the build lists, so newly added
modules are included automatically. It prints to standard output and does
not leave generated audit sources in the workspace.

### The review document

`make -C rocq review` typesets what a reviewer reads as one PDF,
`rocq/review.pdf`, in parts: the shared models (the sections of
`ROCQ-REVIEW-GUIDE.md` about every pass, then every reviewed `.v` file of
`rocq/`, `backend/rocq/` and `backend/ssa/rocq/`: the Spec, Model and
definition files; implementation and Proofs files are left out), then one
part for what the loop passes share and one per pass, each a top-level
section of the guide promoted to a part, with the pass's Spec files at
the end, then the extraction directives and the axioms each statement
rests on. Which guide sections make a part, or open the first one, and
which Spec files belong to a pass is set at the top of
`rocq/review-pdf.pl`; a new Spec file or top-level guide section must be
assigned to a part there, or the script stops. The files of a library are
shown in the order of its list in `rocq/Makefile`, which is a dependency
order; the Flambda 2 lists are in alphabetical order instead (see "Adding
a module"), so for them the script works out a dependency order itself,
preferring the reading order written at the top of the script (`order`),
and a new file needs no entry there. The sources are typeset by
`rocq doc` with every identifier linked to its definition, so the target
needs the `.glob` files of a complete build, and LuaLaTeX with `fontspec`
(Libertinus and DejaVu Sans Mono are used when installed).
The layout of a file carries over: its header comment opens its section, a
banner comment (`(* --- Title --- *)`, or a title between two `(* === *)`
lines) becomes a heading, and `[ident]` in a comment is typeset as code
and linked, as are a file name and a `Module.ident` written without
brackets. The script is `rocq/review-pdf.pl`.

### Adding a module

A new `.v` file goes in the library's list in `rocq/Makefile` (`STDLIB`,
`BACKEND`, `SSA` or `LOOP`); the Spec, implementation and Proofs files of
a model are three such entries, and `make claims` finds the Spec files in
the `SSA` and `LOOP` lists by their suffix. If a file is extracted (it
defines functions the compiler runs, as opposed to only lemmas), also add
its `.ml`/`.mli` to `SSA_MODULES` or `LOOP_EXTRACTED` there, add the
module to the list in the root `dune` file next to the other extracted
modules, and mention it in the header of `Extract.v`. Extraction writes
every file into `backend/ssa/loop/rocq/`; the Makefile moves the
`OxCamlSsa` ones next to their sources. A module whose every definition is
mapped onto OxCaml's own functions extracts to an empty file, which the
Makefile deletes.

The Flambda 2 libraries are worked on by several people and agents at
once, and their lists are laid out so that two branches that each add
something merge without a conflict: `FLAMBDA2` and `FLAMBDA2_TYPES` in
`rocq/Makefile`, and the `Separate Extraction` list of `FlambdaExtract.v`,
have one name to a line, in alphabetical order. Put a new name in its
place in that order. The order means nothing: make takes the dependencies
between the files from `rocq dep`, the review document orders the files
itself, and what is extracted does not depend on the order of the names.
`make claims` finds the Spec files of these lists by their suffix too.

These lists are the integrator's (`middle_end/flambda2/rocq/OWNERS.md`),
but a workstream cannot build a new file without its line, nor can whoever
reviews the branch. So a workstream asks for its lines with a commit:

- The lines go in one commit of their own, the last on the branch, with
  the subject `Flambda 2 Rocq: <stream>: lines for the shared lists`. It
  touches nothing but these lists, and adds only lines for that stream's
  own files, each in its place in the order. No other commit of the
  branch touches the lists.
- To add a line later, amend that commit if it is still the last. If
  other commits have followed it, move it back to the end before asking
  for a merge: `git rebase --onto <it>^ <it>` takes it out of the branch
  and `git cherry-pick <it>` puts it on top. Neither runs the commit
  hooks, so reread the messages.
- The integrator checks the commit at the merge, and refuses a branch
  whose lists differ from the integration branch's in any other way.

## The layout of a model

A model is split over up to three files, so that a reviewer knows from a
file's name whether to read it:

- **`XSpec.v`: what is claimed.** Everything a reviewer has to read about
  the model and nothing else: the definitions its statements are made with
  (a semantics such as `SsaSemanticsSpec.step`, a contract such as
  `finished_graph`, the meaning of a decision such as `eligible_entry`),
  and the statements of its theorems, each bound as a proposition
  (`Definition step_deterministic_statement : Prop := ...`). A Spec file
  imports Model, Spec and implementation files only, so nothing in a Proofs
  file can change what it says; it mentions an implementation function by
  name (`find_deletions` in a statement), never its body. The header says
  what is trusted and what to check the definitions against.
- **`X.v`: the implementation.** The analysis itself, written to mirror the
  shape of the OxCaml it replaces: same decomposition into functions, same
  names where possible, booleans for checks. This is what is extracted
  (`X.ml`). It needs no review: the Spec says what its answers mean and the
  Proofs show that they do.
- **`XProofs.v`: the proofs.** Each theorem proves a statement of the Spec
  under the statement's name without its suffix
  (`Theorem step_deterministic : step_deterministic_statement`), with the
  stepping-stone lemmas and the intermediate specifications they go through
  (the meaning of a helper check such as `uses_only`, an invariant of
  execution such as `valid_position`). Nothing here needs review, and
  `make -C rocq claims` (run by `make -C rocq all`) checks that every
  statement a Spec binds is proved.

A model with nothing to extract has no `X.v`; one whose meaning appears in
no reviewed statement has no `XSpec.v`. A Spec whose definitions the
implementation calls is extracted too (`SsaGraphSpec.ml`: the two readings
of a terminator shared by the semantics and the checks). `*Model.v` and
`*Extract.v` stand apart: they are the trusted base (below), reviewed by
inspection.

A definition goes in a Spec only if a statement that has to be read uses
it, and the test is mechanical: start from the theorems ROCQ-REVIEW-GUIDE.md
names and follow their definitions; what is reached is Spec, and what is
not, however meaningful, is a Proofs definition (`available_value` is one:
the loop proofs use it and no reviewed statement does). A lemma statement
goes in a Spec only when the reader needs it to interpret a theorem
(`step_deterministic_statement` is what makes `steps_until` speak of *the*
execution from a state). Each conjunct of a specification is a named
predicate (`exits_only_to`, `params_are_dead_bivs`, ...), so that it reads
as a sentence and needs no comment explaining its parts. Local
compiler-data contracts are `Record`s of `Prop`s or `Hypothesis` in a
`Section` (`control_edges`, `parameter_layout`). Execution belongs in an
independent semantics such as `SsaSemanticsSpec.step`; the facts an
analysis needs from execution must be proved, not packaged as a trusted run
record.

A statement bound as a proposition is used by `apply`, `eapply`, `rewrite`,
`destruct` and `exact` as if it were the theorem's type; only
`rewrite ... at` and `setoid_rewrite` need it unfolded first.
Analysis-certificate theorems go one way: a boolean check answering `true`
implies its meaning. Nothing is claimed about `false` answers, so the
analyses may be conservative wherever that is convenient (size limits,
overflow, unrecognised shapes).

The models of OxCaml's own types and the backend definitions (`rocq/`,
`backend/rocq/`) are the trusted base rather than models with a Spec:
`OxCamlInt.v`, `OxCamlInt64.v`, `OxCamlList.v`, `IntArith.v`,
`IntegerComparison.v` and `Operation.v` hold definitions and axioms only,
read by inspection against their `*Extract.v` like `SsaModel.v`, and their
lemmas are in `*Proofs.v` files. A proof-only module, with nothing
extracted and no reviewed statement, is a single `XProofs.v`
(`LoopExecutionProofs.v`). In the loop library only two statements are
reviewed: `LoopEligibilitySpec.find_deletions_eligible_statement`, the
result, and the two facts of `DeleteEmptyLoopsSpec.v` that the arguments
outside Rocq rely on; the certificates of the analyses
(`InductionVarProofs.biv_spec`, `DeleteEmptyLoopsProofs.deletion_certificate`)
are reached by no reviewed statement and are Proofs definitions.

## Modelling OxCaml

- **`int`** is Rocq's primitive signed 63-bit integer (`Sint63`), which is
  OxCaml's `int` exactly; `to_Z` reads it as a `Z`. Literals are named
  (`zero`, `one`, `minus_one`, `two` in `OxCamlInt.v`) so that extraction
  prints OxCaml literals; a new literal needs an
  `Extract Inlined Constant ... => "..."` line in the `*Extract.v` file,
  and the two must be kept in step (see `FourierMotzkinExtract.v`).
  Arithmetic wraps: `Sint63.add_spec` and friends give the result modulo
  `2^63` as `cmod`; `OxCamlIntProofs.v` has the lemmas that let `lia` work
  on such sums.
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
  fuel the caller passes is enough (`NaturalLoop.walk_predecessors`).
- **Mutable state** is threaded explicitly: a context is passed in and
  returned, so that each function is a pure function of its arguments
  (`AffineSsa.ctx`).

### What is trusted

The trusted base is small and must stay listed in the headers, and in
`rocq/TRUST-LEDGER.md`, which has every axiom and, for the Flambda 2
semantics, every piece of trusted OCaml, each with its reason
(`make -C rocq assumptions` checks the axioms against it):

- the axioms about `int`, `Int64` and the list functions mapped onto
  OxCaml's (`OxCamlInt64.v`, `OxCamlList.v`);
- the `Parameter`s with axioms standing for a few lines of OxCaml that
  are easier to review than to model (`IntArith.v`'s overflow tests);
- the target's reading of its specific operations as linear combinations
  of their arguments (`Operation.specific_linear`, realised by
  `Arch.linear_specific_operation`), the one thing the models take on
  trust about a target's semantics;
- the extraction directives, which say which OxCaml value realises each
  model definition (`*Extract.v`), including the match functions written
  in them;
- the hypotheses the theorems take about the graph.

Everything else is proved. Never `Admitted`. When something cannot be
proved, state it as a hypothesis where it is used and say so in the
header.

## The semantics of Flambda 2

`middle_end/flambda2/rocq/` is separate from the SSA models: it extracts
nothing and no pass depends on it. Its aim is a semantics of Flambda 2
against which the simplifier's transformations can be proved correct, built
a fragment at a time. The files follow the same Spec/Proofs split, and
`make claims` checks its statements too.

- The work is planned for many people and agents at once:
  `middle_end/flambda2/rocq/PARALLEL-PLAN.md` is the plan and its rules,
  and `OWNERS.md` beside it says who owns which file. Edit only files you
  own.
- `FlambdaModel.v` is the model's copy of the terms (`flambda.mli`), for
  the fragment covered; its header lists what is left out and how the
  presentation differs from the compiler's (plain names in place of name
  abstractions, in particular). Extend the fragment there first.
- `FlambdaSemanticsSpec.v` defines execution as a step *function* on states
  of an abstract machine (an expression, an environment of values and one
  of continuation closures), so determinism holds by construction and
  a term can be run (by `vm_compute`: `step` is opaque to `simpl` once
  `FlambdaSemanticsProofs.v` is loaded, see below). A state's behaviour
  is to exit through an unbound continuation with values, to go wrong, or
  to diverge. A transformation is correct when its result `refines` its
  source (anything may be done to a term that goes wrong); `equivalent`
  is the symmetric notion. `refines` is stated of the behaviours that
  end, so that no proof needs the excluded middle: to prove an
  equivalence or a refinement, divergence never has to be considered
  (`equivalent_of_terminating`).
- A function call has no stack (`call_function`): the body of the code
  runs with the code's return and exception continuations standing for
  the caller's, so returning is applying a continuation. A continuation
  name stands for a handler closure or, unbound, for a way out of the
  term (`resolve`).
- "Let symbol" is `Let_static`: a group of bindings of code ids to code
  and of symbols to static constants. It extends the static environment,
  a fourth component of the machine state that is global (closures do not
  keep it) and only grows. A symbol is a value by itself, a pointer
  (`Value_symbol`), and what it points to is looked up where it is used
  (`closure_of`), so groups may be recursive and static data cyclic.
  Renaming does not touch symbols, code ids or code.
- The body of code bound by a `Let_static` may be rewritten: a context may
  have its hole in code (`Let_static_code`), and `plug_refines` covers it
  (`FlambdaStaticSpec.v`: `let_static_code_refines`). The proof relates
  the static environments of the two runs (`statics_related`: the same
  values, related code); values hold code ids and not code, so they stay
  equal. The renaming bisimulation still keeps the static environments
  equal, as renaming does not reach into code.
- Inlining a direct call is a refinement (`FlambdaApplySpec.v`:
  `inline`), given that the code is closed and that binding the
  parameters captures nothing. `inline_identity`
  (`middle_end/flambda2/types/rocq/`) is a worked example of chaining
  inlining, rewriting under a context, following an alias and removing
  unused bindings.
- Environments, and whatever else maps names to things or collects
  names, are the finite maps and sets of `FlambdaMapSpec.v`: association
  lists in which the first binding of a name counts (`lookup`), and lists
  of names (`among`). Its header says why lists, and what was rejected.
  To bind is to cons. For the rest use its operations (`is_bound`,
  `unbind`, `map_values`, `domain`, `compact`, `filter_bindings`, `merge`,
  `union_with`, `inter_with`; `all_among`, `without`, `inter`, `distinct`,
  `dedup`), each with a statement of what it does to `lookup` or `among`,
  and say what a new function over maps does in the same way. Two maps
  are the same when `map_equal`, not when equal. Do not write another
  lookup, membership test or merge; a lemma about these that is not about
  the terms goes in `FlambdaMapProofs.v`, so that there is one place to
  look.
- Maps and sets keyed by something that is not a name (tags and numbers,
  which are integers; the names of the types) are the same definitions
  again, in the module `Keyed` of `FlambdaMapSpec.v`. Those that compare
  keys take the equality test of the keys as their first argument:
  `Keyed.lookup Z.eqb tag cases`, `Keyed.inter Z.eqb`, `Keyed.merge Z.eqb`.
  Those that compare none take none (`Keyed.finite_map`,
  `Keyed.map_values`, `Keyed.tabulate`, `Keyed.is_empty`). Use one test
  for each type of key, always the same: `Pos.eqb` for names, `Z.eqb` for
  integers, and for another type of key one defined beside the type with
  its proof of `decides_equality`.
  Their lemmas are the `keyed_...` of `FlambdaMapProofs.v`; one that
  depends on the test takes a proof that it decides equality (`Z.eqb_eq`,
  `Pos.eqb_eq`). The definitions on names are those of `Keyed` at
  `Pos.eqb` by computation, so a `keyed_...` lemma applies to them as it
  stands. A new operation goes in `Keyed` only, with a statement for any
  key.
- To define something by recursion on a type that holds lists or maps of
  itself (the meaning of a type, a check of one), go through them with
  `every`, `Keyed.for_all_bindings` and `Keyed.at_binding`, or the tests
  `every_b`, `Keyed.for_all_bindings_b` and `Keyed.at_binding_b`; on
  names the last four are written `for_all_bindings`, `at_binding`,
  `for_all_bindings_b` and `at_binding_b`. Rocq refuses a recursive call
  on what `lookup` returns, and accepts one made by the predicate or the
  test given to these.
- A state is a record with the fields `state_expr`, `state_vars`,
  `state_conts` and `state_statics`. Say what a property is about with
  the projections, and never destruct a state by position: a field added
  later must break nothing that does not mention it. For a proof by cases
  on any state `s`, `rewrite (state_eta s)` and destruct `state_expr s`;
  `simpl_state` reduces the projections of a state given by its
  components (both are in `FlambdaSemanticsProofs.v`).
- A proof never unfolds or simplifies `step`. `FlambdaSemanticsProofs.v`
  has one lemma for each construct (`step_let`, `step_let_static`,
  `step_let_cont_non_recursive`, `step_let_cont_recursive`, `step_apply`,
  `step_apply_cont`, `step_switch`, `step_invalid`), an equation saying
  what a state at that construct steps to and under which conditions, and
  `step` is opaque after them. Rewrite with the lemma of the construct at
  hand; in a proof by cases on the construct, `autorewrite with step`
  rewrites every case. `step_apply_cont_handler`, `step_apply_cont_exit`
  and `step_switch_cases` say the same of the ways in which an
  `Apply_cont` and a `Switch` do not go wrong.
- To go under a binder that both sides have, use the lemmas ending in
  `_equivalent_step` and `_refines_step` (`let_refines_step`,
  `let_static_equivalent_step`, `let_cont_non_recursive_refines_step`,
  `let_cont_recursive_equivalent_step`, ...): the two states take the
  same step, and what is left is to relate the bodies. A proof written
  with them does not depend on what the step of the binder is.
- A change to `step` is then a change to these lemmas, and to the proofs
  that use the lemma of the case that changed. To check that nothing else
  has come to depend on the definition, replace it for one build by a
  `Parameter step` with an axiom `step s = step_impl s`, `step_impl` being
  the definition, and prove the eight lemmas by `rewrite` with the axiom:
  everything else must still build. (Do not commit that.)
- To prove a local rewrite, step both sides until they meet:
  `step_equivalent` for a step of one side, `equivalent_step` and
  `refines_step` for one of each, `step_eq_equivalent` where the two
  first steps come to the same thing, `step_undefined_refines` where the
  source is undefined. `FlambdaControlFlowProofs.v` has the worked
  examples.
- Primitives are abstract (`prim`, `eval_prim`), with no axioms. A law of a
  primitive is to be stated about `eval_prim`: as an axiom, listed in the
  header of the file stating it, or as a lemma once the primitive has a
  definition.

- A rewrite between expressions applies inside any term
  (`FlambdaContextSpec.v`: `plug_refines`, `plug_equivalent`). The proof
  (`FlambdaContextProofs.transfer`) is the pattern for any argument where
  two runs differ in what their continuation closures hold: relate the
  environments, and go by induction on the length of one run.

- Names follow the compiler's `nominal/` directory, as a partial theory of
  nominal sets (`FlambdaNominalSpec.v`). Terms keep their named binders,
  which shadow, and there is no type of alpha-equivalence classes: a
  renaming is a pair of permutations given as lists of swaps, it acts on
  terms without capture (`rename_expr`), and `expr_equivalent` stands in
  for equality of classes. The statements say that a renaming fixing the
  free names of a binder with its scope may be applied to it (what
  `Name_abstraction.pattern_match` relies on), and that an unused binding
  may be removed. A fresh name is any name not free where it matters;
  nothing generates one.
- An expression stands for its alpha-equivalence class in this sense
  (`FlambdaAlphaSpec.v`): `alpha_equivalent` is the congruence generated
  by renaming bound names; it is equivariant and preserves the free names;
  and alpha-equivalent expressions are `expr_equivalent`
  (`alpha_equivalent_sound`), so everything said with `expr_equivalent`
  or `expr_refines` is said of classes. To carry a rule about a renaming
  `s` across another renaming `r`, use the conjugate
  (`FlambdaAlphaProofs.conjugate`).
- Two runs that stay in step are related by a bisimulation
  (`FlambdaSemanticsProofs.bisimulation_equivalent`), as a state and its
  renaming are (`FlambdaNominalProofs.renamed_equivalent`, from which
  `coincide_equivalent`: behaviour depends only on the free names). In
  it a closure of a recursive group is related to its renaming with a
  renaming chosen per handler (`closure_renamed`, `handler_agrees`), so
  that the handlers of a group can be renamed one at a time. Two
  runs of different lengths need the induction of
  `FlambdaContextProofs.transfer`.

- A rewrite that depends on what is known of the variables in scope is
  stated relative to a typing environment
  (`middle_end/flambda2/types/rocq/FlambdaTypesSpec.v`: `expr_refines_in`,
  over `env_satisfies`). The model of types there is naive on purpose (a
  type is unknown, bottom, an alias to a `Simple`, or that of the closures
  of given code with given value slots); a richer grammar is to add cases
  to `type_satisfied`. `follow_aliases` uses the closure types to make a
  call of a known closure direct and to replace the projection of a value
  slot from one by what the slot holds. A binder gone under must not occur in
  the typing environment, which is the simplifier's freshness invariant.
  There is no substitution: as in the simplifier, a variable is replaced
  at its uses by following its alias, and its `Let` is then unused.

  Into a handler, what is known at the `Let_cont` stays known and the
  parameters are added (`let_cont_handler_refines_in`); underneath,
  `FlambdaContextProofs.handler_refines_at` says that a handler refines
  another where it runs, under the variables of its closure.

Not yet there: the types of a continuation's parameters, joined over its
uses; types beyond aliases, with meet and join; that the generated alpha-equivalence is contained in the
one defined by recursion on two expressions (`alpha_structural`; the other
containment is proved); equivariance of execution in the continuations
(renaming closures and observed exits; there is a CR in
`FlambdaAlphaSpec.v`); the simplifier's
invariant that bound names are distinct from those in scope;
removing an unused static binding (which needs the free symbols and code
ids of terms, code and values); rewriting the body of code by what is
known of the static environment; sets of closures of several functions; kinds on
parameters and well-kindedness; mutable memory and effects, trap actions,
and any link to the simplifier's code.

### Testing Simplify against the semantics

`middle_end/flambda2/tests/semantics/` checks the real simplifier against
the model on small examples written in the fexpr language. For each `.fl`
file, `flsemantics` (`middle_end/flambda2/tests/tools/flsemantics.ml`)
parses it to a Flambda unit, runs Simplify, converts the unit before and
the unit after to terms of the model, runs both on the machine extracted
from `FlambdaSemanticsSpec.v`, and compares what the two runs come to: the
continuation exited through and its arguments, followed through symbols
into static blocks. A closure is not looked into. The check passes if the
outcomes are the same, or if the run before is undefined. This is a test,
not a proof.

- Beside the test of one run, the tool reports whether the pair is
  *validated*: whether `FlambdaValidateSpec.validate_unit`, extracted,
  accepts it. That is one function with one theorem
  (`validate_unit_sound`): the term after refines the term before as a
  compilation unit is run, on its own from empty environments. The tool
  does not put the rewrites together itself; to change which are applied,
  or their order, change `normalise_before` and `normalise_after` there.
  The rest of this item is what `validate_unit` does.
  The decision is `FlambdaCompareSpec.expr_eqb`, equality up to bound
  names, after the term before has been normalised by rewrites proved to
  refine it: `inline_calls` (direct calls of code bound by an enclosing
  `Let_static`, in handlers and in the bodies of code too), `fold_constants`, `collapse_switches` (a `Switch` whose
  arms are all the same), `inline_tail_conts` (a continuation applied
  once at the end of its scope), `follow_aliases`, `remove_unused_lets`
  and `drop_deleted_code`, gone round until nothing changes as
  they enable one another. Only equivalences may be applied to the term
  after: `follow_aliases`, `inline_known_calls` (inlining where the callee
  is a symbol bound to a closure of the code called, which makes it an
  equivalence), `fold_constants`, `remove_unused_defined_lets` (an unused
  `Let` whose defining expression has a value given the variables in
  scope), `drop_deleted_code` and `merge_statics` (one group for
  `Let_static`s that follow one another, code before symbols).
  `fold_constants` asks `eval_prim` for the value of a primitive on
  constants, so it assumes nothing of the primitives. Which primitives
  are folded, and removed when unused, is the tool's to say
  (`prim_may_fold`): all but `Opaque_identity`, which Simplify leaves
  alone, so that an example can have values Simplify knows nothing of.
- A `Let_static` is permitted at the toplevel of a unit only
  (`FlambdaWellFormedSpec.well_formed_unit`, after Simplify's
  `at_unit_toplevel`). The tool checks the term before, and does not give
  one that fails to Simplify (`static_in_loop.fl`); the term after failing
  is an error. The machine enforces what keeps a static binding from
  running twice: calling code whose body binds something static is
  undefined, as is a `Let_cont_recursive` one of whose handlers does
  (`binds_statics`), and so is binding a static name twice; so static
  environments only grow (`run_extends_statics`). A rewrite of the body
  of code or of a recursive handler must therefore keep whether it binds
  something static (the premise of `plug_refines` for such a context),
  and code is inlined only if its body binds nothing static
  (`FlambdaApplySpec.inlinable`). A well-formed unit run on its own never
  meets one of these three (`well_formed_never_faults`). The invariant of
  the proof is about the names a state may still bind: they are distinct,
  none is bound, and those of a handler are not among those of the
  continuations its closure holds. A rewrite inside a handler may then
  rely on what was bound where the handler is defined: the lemmas for it
  are the ones ending in `_where` in `FlambdaContextProofs.v`, which take
  a property of the static environment that every extension keeps
  (`inline_in_handler.fl` needs them).
- Only the two inlining passes go into the bodies of code by
  themselves, as they need what is known there. The others are applied
  to the bodies by `rewrite_code`, which takes any rewrite and is proved
  to refine, or to be an equivalence, when the rewrite does under all
  environments (`inline_in_code.fl` needs both).
- `showcase.fl` is the example to read first: direct and indirect calls,
  a closure with a value slot, nested switches and a join, all inlined by
  Simplify and validated. In `switch_nested.fl` Simplify uses what a
  `Switch` arm tells it of the scrutinee in the continuation the arm goes
  to. The normalisation has one case of that, `thread_switches`: an arm
  that goes to a handler which is a `Switch` on the same scrutinee goes
  where that one's arm does. What is known at the uses of a continuation
  does not reach its handler in general.
- Removing a static binding that nothing uses is not sound under every
  environment (a value already there may be a closure of the code), only
  under those in which the names removed do not occur
  (`FlambdaUnusedStaticsSpec.drop_statics`, `envs_free_of`); a term run
  on its own is a case (`program_refines`). The tool guesses which names
  are unused and the extracted function checks the guess. An example
  that needs it is validated like any other, for the unit run on its
  own; the two other ways of being validated hold under every
  environment as well (`validate_unit_sound_everywhere`).
  Its proof is a simulation that lets the second state do anything once
  the first is undefined (`FlambdaSemanticsProofs.simulation_refines`),
  under the invariant that nothing reachable refers to a name removed;
  that needs an axiom, that the primitives introduce no symbols or code
  ids (`eval_prim_avoids`).
- Setting `FLSEMANTICS_PRINT_TERMS` makes the tool print the two
  normalised terms of an example that is not validated, which is how to
  find the rewrite that is missing.
- Code ids must be the same on the two sides, and Simplify gives a new
  one to each new version of code. The tool gives the new id the number
  of the old where the old is bound as deleted and not otherwise used;
  this is trusted, and there are CRs in `flsemantics.ml` and
  `FlambdaCompareSpec.v` on relating code ids in the comparison itself.
  An example that is the same but not validated shows what normalisation
  is missing. To add a rewrite: write it as a function in a Spec file,
  prove that its result refines (or is equivalent to) its argument, add
  it to `FlambdaExtract.v`, and chain it in `flsemantics.ml`.
- The machine is extracted by `FlambdaExtract.v` into
  `tests/semantics/extracted/` (`make -C rocq all` regenerates it; the
  files are committed; `prim_hook.ml` there is written by hand). No part
  of the compiler is built from it.
- Who commits the extracted files. Only the integrator commits
  `tests/semantics/extracted/`, on the integration branch. They are
  generated, one file from many sources, so two workstream branches that
  each committed them would conflict at every merge, in files nobody
  wrote. On a workstream branch, run `make -C rocq all` before the tests,
  which regenerates the files where the tests find them, and leave them
  out of your commits: stage the files you changed by name, not with
  `git add -A`. `git status` will go on showing them as modified;
  `git checkout -- middle_end/flambda2/tests/semantics/extracted` puts
  them back, which a rebase needs first. When a branch is merged, the
  integrator runs `make -C rocq all` on the result and commits what it
  regenerates, on top of the branch. `prim_hook.ml`, written by hand, is
  the integrator's like the rest of the directory.
- Trusted and unverified: the conversion from Flambda terms to model
  terms, and the meaning the tool gives to the few primitives it knows,
  which the model leaves abstract. Read both in `flsemantics.ml`. The
  whole list, with the axioms about the primitives, is the section
  "Flambda 2" of `rocq/TRUST-LEDGER.md`.
- A construct or primitive the conversion does not know makes the example
  "not checked"; it is never run as if undefined, which would pass for
  nothing. When the model gains a construct, teach the conversion and add
  an example.
- To run:
  `dune build --root=. --workspace=duneconf/main.ws
  @middle_end/flambda2/tests/semantics/runtest` (after
  `make -s boot-compiler`). The expected output of `X.fl` is
  `X.expected`, beside it.
- To add an example, add `X.fl`, whose module symbol must match its name,
  and `X.expected`; `dune promote` writes the latter from what the tool
  printed. Nothing else is to be touched: there is no list of examples.
  The dune rules are generated from the `.fl` files that are there
  (`gen_rules.sh`, included by `run/dune`; the `dune` file says why it
  takes two directories), so two branches that each add an example do not
  meet in any file.

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
- Use the notations `SsaModel.v` defines (`a ▷ b` for `a`
  dominating `b`) in Spec and Proofs files, where a statement is read by
  eye. Implementation files are code and call the primitives as the
  compiler does.
- Use `∀` and `∃` for quantifiers and `∧` and `∨` for conjunction and
  disjunction, importing `OxCamlLogic.v`. Keep the default `->` and `<->`
  arrows, and `exists` for the tactic.
- Use `∈` and `∉` for list membership and non-membership; `OxCamlList.v`
  defines these notations for `List.In` and its negation.
- Prefer a per-element statement to a counting one: "every parameter at
  position `k` has a dead induction variable with `param_index = k`" is
  checkable; "there are as many as parameters" is not what the pass
  relies on.
- The existential witnesses in a specification should be things the
  analysis actually computes (`∃ args, goto_args ... = Some args`),
  so that the proof is a reading-back of the code.
- Define machine execution once (`SsaSemanticsSpec.v`). Derive operation
  equations only for available, canonical definitions
  (`SsaExecutionProofs.v` and `SsaContextProofs.v`). An abstract
  arithmetic valuation such as
  `AffineSsa.value_words` is constrained by `SsaSemanticsSpec.eval_operation`
  (`AffineSsaProofs.op_semantics`), not by a second statement of the
  arithmetic, and needs a proved connection to execution
  (`LoopValueSnapshotProofs.v`) before it can justify optimization.
- Keep analysis preconditions in named propositions, not in executable
  types. For example, the counter proof needs `biv_spec`, which
  `InductionVarProofs.analyze_spec` establishes for the discovered variables.
  Composing the analyses must discharge these preconditions, rather than
  turn them into trusted assumptions about the program.
- Execution must not depend on the analysis being verified. For example,
  `LoopExecutionProofs.region_steps` is a sequence of instruction steps,
  not a record assuming counter recurrence or invariant bounds. A
  property of an analysis result is stated as what it means
  (`loop_invariant_value`), tied to the function by a read-back theorem
  (`is_loop_invariant_spec`), and then justified operationally
  (`LoopInvariantExecutionProofs.loop_invariant_value_same`).

## Proof style

- Statements and proofs stay under 80 columns. Give explicit types to
  statement binders and use `insn` for instruction variables.
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
  many lemmas (the graph in `LoopCounterExecutionProofs.v`); the lemmas are
  generalised over them at `End`.
- Name hypotheses after what they say (`Hexit`, `Hwf`), not `H0`, `H1`.
- Do not comment what a named predicate already says; do comment every
  non-trivial lemma, and every case of a long proof that is not evident.

## Checklist before pushing

- `make -C rocq all` passes and the extracted diff is the intended one.
- `make -s boot-compiler`, the pass's tests and `make -s fmt` pass.
- New definitions sit in the most generic file that fits, and in a Spec
  only if a reviewed statement needs them; new modules are registered in
  `rocq/Makefile`, `dune` and `Extract.v`.
- Every non-trivial lemma and theorem has a comment; no comment restates
  a named predicate.
- The headers list what is trusted, and nothing is `Admitted`;
  `make -s -C rocq assumptions` passes, so there is no axiom that
  `rocq/TRUST-LEDGER.md` does not list.
