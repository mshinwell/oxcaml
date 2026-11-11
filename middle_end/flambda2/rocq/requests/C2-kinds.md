# Core change request C2: kinds and well-formed terms

Owner: C2. Branch `flambda2-rocq/C2-epoch`: the whole repair, as a series
that C0 can apply. This is the third version of the request and replaces
the two before it (on `flambda2-rocq/C2-kinds`, which keeps the
prototype and the experiments on the compiler). The series is rebased
over C3's epoch (sets of closures of several functions) and has the
cases for its forms; the text is revised for that, and for the review of
the series (section 10).

## In short

Terms gain kinds where the compiler has them. A `Let` gives the kind of
its variable; a handler gives the kinds of its parameters; code gives
the arity of its parameters and that of its results; an `Apply` gives
the two arities it is made at. An arity is the compiler's
`Flambda_arity.t` without subkinds, unboxed products included.

The machine looks at one thing only: a call is undefined unless it
agrees with the code it calls, by the three tests that Simplify makes
before it replaces a call by `Invalid`. Everything that a well-typed
program with GADTs and layout `any` is known to put into Flambda 2 is
then undefined on the machine, with no premise (section 4).

A new pair of files, `FlambdaWellKinded*`, has a check of the kinds of a
term as a boolean function, the same for a state, and nine statements,
all proved. The check is a sufficient condition and a diagnostic. It is
not a condition that the compiler's terms are known to meet, and no
statement about those terms takes it as a premise (section 3).

What the human has ruled, and where it is applied:

- A call at arities that are not those of its code is undefined, and so
  is any mismatch of kinds where it is executed ("For D9 and D10 for
  the moment, I think we should assume these produce Invalid"). Step B,
  section 1.
- A check may not be stricter than the compiler ("We cannot be more
  strict on kind checks than the compiler"), and the compiler is the
  compiler without `-flambda2-kind-checks` ("Treat everything as if this
  is not specified"). So nothing here is described by what that flag
  does, the check looks at no argument of a call or of a primitive, and
  it is a gate for nothing.
- What GADTs and `any` can produce must be undefined ("those cases MUST
  produce Invalid"). Section 4.
- Where something is undefined, or refused, and neither a ruling nor a
  GADT forces it, the `Spec` file has a comment for the human, marked as
  a review comment addressed to mshinwell, with the number of the
  decision. There are two, both for D10 (section 9).

What the human is asked to decide is in section 9: one question about
binders (D10), with what each answer costs. What the test tool does
with the check's answer (D11) is settled: as built.

## 1. The change to the terms and the machine

The series has the change in two steps, as C0 asked. Step A is the
annotations with the machine as it was. Step B is the tests at a call.

### Step A: the annotations

`FlambdaModel.v`:

    Inductive arity_component : Type :=
      | Singleton (k : flambda_kind)
      | Unboxed_product (components : list arity_component).
    Definition arity : Type := list arity_component.

with `unarize`, `unarize_per_parameter`, `arity_of_kinds`, `arity_eqb`,
each named after the function of `kinds/flambda_arity.ml` that it is.
Parameters and arguments stay unarized, as in the compiler: an unboxed
pair is two variables, and void is none.

    Let (x : variable) (kind : flambda_kind) (defining_expr : named)
        (body : expr)
    Handler (params : list variable) (metadata : handler_metadata)
        (handler : expr)
    Code (params : list variable) (my_closure : variable)
        (return_continuation exn_continuation : continuation)
        (metadata : code_metadata) (body : expr)

    Record handler_metadata := { hm_params_kinds : list flambda_kind }.
    Record code_metadata :=
      { cm_params_arity : arity; cm_result_arity : arity }.

and `apply_expr` gains `ap_args_arity` and `ap_return_arity`. The two
records are made by `make_handler_metadata` and `make_code_metadata` and
are bound whole in patterns, so that a later annotation (C5 asks for
`hm_is_exn_handler`) is a field and no term changes shape for it.

A handler keeps a list of kinds beside its parameters, as the compiler
pairs each parameter with a kind. Code has no such list: the kinds of
its parameters are its parameter arity unarized (`code_params_kinds`),
and those of the parameters of its return continuation its result arity
unarized.

The machine ignores all of it in step A. Every statement about a `Let`,
a handler, code or a call now holds whatever these are annotated with:
twenty-four statements gain a quantified kind, metadata or arity
(section 6 names them), and none changes its meaning. Renaming leaves the
annotations as they are; alpha-equivalent terms have the same ones (the
rules of `alpha_equivalent` and `alpha_structural` say so); `expr_eqb`
compares them. `let_params` takes the kinds of the parameters and binds
every parameter that has an argument, also where the list of kinds is
too short, so that the bindings are those the call makes whatever a
term is annotated with (the reviewer's point N1). The `Let`s that
`let_closures` and `let_projections` make (C3's) are at kind `Value`.

### Step B: a call agrees with its code, or is undefined

`call_function` takes the two arities of the call and has no step unless
three things hold. Each is what Simplify tests before it replaces a call
by `Invalid`; the functions named are in
`simplify/simplify_apply_expr.ml`.

| The test in `call_function` | The compiler | The reason it gives |
|---|---|---|
| `map kind_of_value vs = unarize args_arity` | `simplify_apply_shared`: the kinds of the arguments against `Flambda_arity.unarize (Apply.args_arity apply)` | `Application_argument_kind_mismatch` |
| `unarize_per_parameter args_arity = unarize_per_parameter (code_params_arity c)` | `arity_mismatch`, on `Flambda_arity.unarize_per_parameter` of the two | `Direct_application_parameter_kind_mismatch` |
| `return_arity = code_result_arity c` | `simplify_direct_function_call`: `Flambda_arity.equal_ignoring_subkinds` | `Application_result_kind_mismatch` |

The first is the one place where the machine looks at the kind of a
value. Poison has the kind it carries, and an allocated value or a
symbol, bound or not, has kind `Value`, so poison of the right kind
passes; that is intended and the comment says so.

Why the arities are trees. The second version had flat lists of kinds.
The review (B1) showed that this erases what decides `Invalid`. Each of
these is an example in `FlambdaWellKindedProofs.v` that a flat arity
would have run and that is now undefined:

- arguments: code with one parameter that is an unboxed pair of values,
  called at an arity of two parameters, each a value
  (`product_two_parameters_undefined`). An OCaml program of the
  reviewer's produces it: a GADT indexed by `#(int * int) -> int` and
  `int -> int -> int`;
- results: code that returns `#(a * #(b * c))`, called by a call that
  expects `#(#(a * b) * c)` (`product_result_nesting_undefined`). A list
  of lists of kinds would not do here: the compiler compares result
  arities as they are nested.

And the one that shows the two tests differ: arguments nested
differently inside one parameter run (`product_argument_nesting_runs`),
as the compiler compares arguments parameter by parameter after
unarizing each.

What else changes in step B:

- `inline_known_calls`, whose statement is an equivalence, inlines a
  call only where it is sure to agree with the code (`call_agrees_b`):
  its arities are those of the code, and each argument is a constant or
  a symbol of the kind the call gives it. The inlined body does not test
  the kind of what a variable holds, and the call does. The text of
  `inline_known_calls_equivalent_statement` is unchanged. Section 7 says
  what this costs the validation.
- `inline_calls`, a refinement, is unchanged: a call that does not agree
  is undefined, and anything refines it.
- `expr_eqb` already compares the arities of calls and the metadata of
  code, from step A.
- `call_function_step`, a step lemma of `FlambdaSemanticsProofs.v`,
  gains the three facts, and `step_apply_closure` (C3's: the way in
  which an `Apply` does not go wrong) the three as premises.

What the tests do not cover. They are about the values of the arguments
and about two pairs of annotations. Nothing is tested when the body
returns: the third test is that the return arity of the call is the
result arity of the code, an equality of two annotations, and the values
that the body then gives its return continuation are not looked at.

## 2. Kinds of values

Every value has a kind (`FlambdaValueSpec.kind_of_value`, C1's): that of
its constant, and `Value` for everything allocated and for a symbol.
The model has no subkinds.

## 3. The check, and what it is not

`FlambdaWellKindedSpec.well_kinded slots kinds conts e` is a boolean
function. What it checks:

1. every variable and continuation used is in scope;
2. the kind of a `Let` is that of its defining expression; for a
   primitive, the kind of its result (`prim_result_kind`, C1's);
3. the arguments of an `Apply_cont` have the kinds of the parameters of
   the continuation;
4. the scrutinee of a `Switch` is a naked immediate;
5. the return continuation of an `Apply` takes what the call says it
   returns, unarized, and the exception continuation one `Value`;
6. a handler has as many kinds as parameters, and its parameters are
   distinct, as are those of code with `my_closure`;
7. the body of code is well-kinded on its own, under its parameters at
   the kinds of its parameter arity;
8. a value slot holds a `Simple` of the kind of the slot (a table given
   to the check), where a closure is made, by a `Let` or statically, of
   a set of one function or of several; and its projection has that
   kind;
9. the fields of a static block are values, and the contents of a
   static boxed number are a number that can be boxed;
10. a variable bound to a closure, or to the projection of a function
    slot, is a `Value`.

What it does not look at, each being undefined where it is executed: the
kinds of the arguments of a primitive; the kind of the callee of a call,
and of what a value slot or a function slot is projected from, and the
function slot that a projection names (D3); whether a call agrees with
its code (the three tests).

It is a sufficient condition and a diagnostic. The reasons it is not
more, which the header of the file gives:

- Each condition is one the compiler has a check of its own for, which
  stops it. But it checks only where Simplify visits. A `Switch` on a
  constant, whose arm that is not taken applies a continuation to an
  argument of another kind, compiles: Simplify removes the arm first.
  The check here looks at every branch and answers no (the reviewer's
  term, here as `tests/semantics/kinds_dead_cont.fl`;
  `example_dead_arm_refused` and `example_dead_arm_runs` in the Proofs
  file; discrepancy R2-11). So as a gate it would be stricter than the
  compiler.
- That what closure conversion builds passes the check is known by
  experiment only (section 4).

So the check is not proposed as a condition of `well_formed_unit`. C0's
note `requests/C0-well-formed.md` says the same, and has the three of
its conditions that a dead branch cannot break (names in scope, distinct
parameters, annotations of the right length) as rows of its own.

The statements (all proved; `make claims` checks them):

| Statement | What it says |
|---|---|
| `call_at_wrong_kinds_undefined` | A call that fails one of the three tests has no step, whatever the state. |
| `partial_or_over_application_undefined` | A call whose arguments have the kinds of its arity and whose arities pass the compiler's test for a partial application or an over-application has no step (an omission; section 8). |
| `well_kinded_unit_state` | A unit that passes the check starts in a well-kinded state. |
| `step_well_kinded`, `run_well_kinded` | A step, and a run, keep a state well-kinded. |
| `well_kinded_no_kind_fault` | A well-kinded state reads no unbound variable, applies no handler to the wrong number of arguments, and switches on a naked immediate. |
| `well_kinded_exit` | A well-kinded state exits only through the interface, with values of its kinds. |
| `well_kinded_unit_never_faults`, `well_kinded_unit_exits` | The same for a unit run on its own. |

None has a premise about the primitives: the two laws used are C1's
`eval_prim_kinds_statement` (a primitive that has a value has one of its
result kind) and `eval_prim_preserves_statement` (a primitive makes its
value out of its arguments), which replace the two hypotheses of the
prototype. None is about progress. And for the types: the predicate on
states takes the kinds of the values held now; it does not remember what
a binder said. What a consumer may use is the fact at the step: a
well-kinded state that binds a variable binds a value of the kind the
binder gives.

With no premise at all, the machine gives less, and it is to be read
exactly. At a call that steps, the values of the arguments have, in
order, the kinds of the parameter arity of the code, unarized, and the
callee is a `Value`. That is a fact about the values that are bound. It
is a fact about what a parameter, looked up in the body, holds only
where the parameters and `my_closure` are distinct names, which the
machine does not test: code with one parameter `x` and `my_closure` also
`x` binds the argument over the closure. The check asks for distinct
names (item 6), and so do C0's conditions on binders. And nothing is
given for what the body returns (section 1, the end of step B).

## 4. What GADTs and layout `any` put into Flambda 2

The experiments are X2's, on the branch `flambda2-rocq/X2-repro` (the
programs, a script that compiles each at six settings, what it printed,
and a note on each), with three programs of mine and one of the
reviewer's on the prototype branch `flambda2-rocq/C2-kinds`. None of
this is in the tree: the table says what the programs show. Every
program is accepted by the type checker and compiled by the real
compiler with its default flags and five other settings; none stops the
compiler.

Two ways of making the mismatch: a GADT indexed at layout `any`, matched
in a function that is inlined where the index is known; and an equality
witness between two value types of different representation, with an
inlined `cast`. In both, the term before Simplify is consistent: every
variable has one kind and every call is an indirect call at the arity of
its own arguments. The mismatch appears when Simplify brings together
two things that the source kept apart by an indirection.

| Form | Programs | Simplify | The machine |
|---|---|---|---|
| A call whose argument arity is not the code's parameter arity | one of X2's, one of mine | `Invalid` | undefined: test 2 |
| A call whose result arity is not the code's | one of X2's, one of mine | `Invalid` | undefined: test 3 |
| A call with another number of unarized arguments or results (an unboxed pair against one value) | one of X2's, the reviewer's | `Invalid` | undefined: tests 2 and 3, on the trees |
| An over-application whose callee does not return one value; a partial application whose result is not one value, or whose argument is of another kind | one of X2's | `Invalid` | undefined: test 2 (another number of parameters) |
| A load that does not agree with the block (a value from a mixed block, a naked float from a block of values, a field beyond the end) | two of X2's, one of mine | `Invalid`, by the types | the argument is a `Value`, so this is not a mismatch of kinds: C1's `Block_load` has no value on a field that is not there or not a value; mixed blocks are not in the fragment |
| Unboxing or untagging another sort of number; `Is_int`, `Get_tag` on a boxed float or a closure | two of X2's | `Invalid`, by the types | as above: C1's primitives have no value on what they are not for |
| An array primitive at another array kind | one of X2's | a load from an immutable array: `Invalid`; a load or store of immediates on an array of naked floats: kept; `Array_length`: folded with the primitive's own kind | arrays are not in the fragment; recorded for C1 as discrepancy C2-8 |

Not produced, in any program tried: a call whose argument is not of the
kind its own arity gives (test 1; the conversion from Lambda takes the
arity from the arguments); a primitive given an argument of another
kind; a `Let`, a continuation parameter, an `Apply_cont` argument, a
`Switch` scrutinee, a block field or a value slot at another kind. For
the last group the type checker refused each of eight attempts (X2
kept the programs and the messages).

So every form found is undefined on the machine, by the three tests or
by C1's primitives, and the forms that the check answers no to were not
found. This is experiment and an argument (a value crosses from one
piece of code to another only through a call, a block or closure, or a
continuation of the same function), not a proof. A corpus of the
compiler's own units through the check would be the test of it. The
start of one is V2's fifteen units made from small OCaml sources: each
passes the check before Simplify and after.

If a program is found that the machine runs and Simplify makes
`Invalid`, that is a blocking error of the model.

## 5. The layers

- Undefined where executed, in the machine, with no premise: a call that
  does not agree with its code; a primitive on an argument of another
  kind (C1). Ruled.
- Well-formedness (C0's one definition): a condition that the
  compiler's terms always meet and that a dead branch cannot break. Of
  mine: names in scope, distinct parameters, annotations of the right
  length. They are rows 3, 5 and 9 of C0's note; my series does not
  touch `well_formed_unit`.
- The diagnostic: everything else that `well_kinded` asks. A unit that
  passes has the guarantees of section 3. A unit that fails may be a
  unit the compiler accepts.

What an executed mismatch does where the machine has no test (a value of
another kind bound by a `Let` or as a parameter of a handler; a block
field; a value slot) is the open question of section 9.

## 6. Which statements change

Step A, text only (a kind, a metadata or an arity is now quantified;
the meaning is that the statement holds whatever the annotation):
`apply_indirect_known`; `let_cont_apply_cont`,
`let_cont_apply_cont_one_param`, `let_cont_recursive_apply_cont`;
`rename_let`, `freshen_let`, `rename_handler_params`,
`rename_recursive_handler_params`, `unused_let`;
`project_static_closure`, `let_static_code_refines`;
`project_function_slot_let_closures`, `apply_sibling`,
`project_function_slot_static`, `project_value_slot_static` (C3's);
`step_values_all` (N1's: its premise about a `Let`);
`let_simple_canonical`, `let_refines_in`, `let_simple_refines_in`,
`let_cont_handler_refines_in`, `let_cont_recursive_handler_refines_in`,
`let_const_apply_cont`, `let_simple_apply_cont`, `inline_identity`.
That is twenty-four. C3's example of two functions that call each
other (`parity_code` and what uses it) is annotated at naked immediates,
so that its two statements about runs hold after step B as before.
The rules of `alpha_equivalent` and `alpha_structural` for a `Let` and a
handler carry the kind and the metadata, the same on the two sides.

Step B, meaning: every statement about `step`, `run`, `refines` and
`equivalent` is now about a machine on which more calls are undefined.
For a refinement, "the term before is undefined" covers more. One text
changes: `call_binds_my_closure` (C3's) names `call_function`, and so
quantifies the two arities of the call. Two functions change so that
their statements stay true as written: `inline_known_apply` (the guard
`call_agrees_b`) and the comparison, which was already changed in
step A.

`validate_unit_sound` is as it was: its statement has no premise about
kinds.

## 7. Fallout, measured

Step A: 44 files, 1306 lines added and 804 removed, all mechanical; the
largest are `FlambdaNormaliseProofs.v` and the files of the nominal
part. Step B: 15 files, 327 added and 93 removed; the proofs that
unfold `call_function` each gain a case split on the tests.
`FlambdaWellKinded*`: 809 and 1679 lines.

Validation. There were 54 examples: 38 in `tests/semantics/` (C3's
eleven included) and V2's 16 units made from OCaml sources, in
`tests/semantics/ocaml/`. 47 are converted (the other seven have what
the model has not got, or are not well-formed, as before). Each of the
47 prints what it printed, and one new line, "the check of kinds: passes
before, passes after". So every example passes the check on both sides,
the fifteen units that the compiler made from OCaml sources among them,
and none loses its validation: the counts of "validated" are what they
were (in `tests/semantics/`, 2 up to bound names, 16 once normalised, 5
with unused static bindings removed; of the units from OCaml sources,
9).

What the guard on `inline_known_calls` costs: nothing, on the examples
there are. I ran every example, the new ones included, with the guard
taken out of the extracted function, and none prints anything
different: in none does the term after Simplify keep a direct call of a
symbol whose arguments are not all constants or symbols. It will cost on
larger units. C0's list of variables of known kind is the repair, and is
a follow-up.

Ten examples are new:

| Example | What it shows | What the tool prints |
|---|---|---|
| `kinds_gadt.fl` | the shape of the GADT program: a call in a branch that is not run meets code of another arity once inlined | returns `[0: 5]` before and after; passes, passes |
| `kinds_wrong_arity.fl` | a call at an arity that is not the code's | undefined before (3 steps) and after; passes, passes |
| `kinds_naked.fl` | a call at naked immediates | returns `[0: 7]` before and after; passes, passes |
| `kinds_dead_prim.fl` | a primitive on an argument of another kind, in a branch that is not run | returns `[0: 5]` before and after; passes, passes |
| `kinds_opaque_bad.fl`, `kinds_is_int_bad.fl` | the reviewer's two: a primitive on an argument of another kind, executed | undefined before and after; passes, passes |
| `kinds_dead_cont.fl` | the reviewer's: an `Apply_cont` of the wrong kind in an arm that Simplify removes | returns `[0: 5]` before and after; fails before, passes after; validated once normalised (V2's removal of unused continuations takes the arm away) |
| `kinds_partial_application.fl` | an indirect partial application | "stops at a partial application or an over-application, which the model has not got"; not decided; no validation is attempted |
| `kinds_partial_direct.fl` | a direct one | not checked: the model has not got it |
| `kinds_tupled.fl` | the reviewer's: tupled code of one parameter, called indirectly with the tuple; the arities of the call and of the code agree, and the call is still not the one the model would run | not checked: the model has not got a tupled function |

## 8. Trust

`rocq/TRUST-LEDGER.md` gains the following, in the item on the
conversion of the test tool (the last commit):

- The converter gives each call and each code its two arities. A wrong
  one makes a run undefined that should not be, or the reverse, and the
  check of kinds does not catch it: code that never returns passes with
  any result arity (the reviewer's B4). So the arities are trusted. Two
  cross-checks run at each conversion and stop the tool: the arity as
  converted, unarized by the model, has the kinds that
  `Flambda_arity.unarize` gives; the parameter arity of code, unarized,
  has the kinds of the parameters of its body (discrepancy C2-6: nothing
  in the compiler's `Code0.create_with_metadata` checks this). What is
  not cross-checked: the grouping into products, which the tool rebuilds
  through `Flambda_arity.fold_per_parameter`.
- The table of the kinds of value slots is built from
  `Value_slot.kind` as slots are met.
- The variables of a `Let` of a set of several functions get the kind
  `Value` from `let_closures`; the tool refuses the binding if the
  compiler gives one of them another kind.
- Partial applications and over-applications are not in the model. A
  direct call that the compiler takes for one, of code that the unit
  binds, is refused by the converter (reported as unsupported), by the
  compiler's test of the arities: `partial_or_over_application`, which
  is read against `simplify_direct_function_call`. It is that test and
  no more: a call that passes it and whose arguments are not of the
  kinds of its arity is `Invalid` for the compiler, and a call with no
  argument of code that has parameters, which fails it, is a fatal error
  of the compiler and not `Invalid` (the comment at the definition says
  both). An indirect one cannot be told from the term. A run that stops
  at one is reported as such (`at_partial_or_over_application`, which
  asks also that the values of the arguments are of the kinds of the
  call's arity); the tool then says "not decided", whatever the other
  run does, and does not call `validate_unit`: what that would accept is
  true of the model, where the call is undefined, and of nothing else.
  The tool of the series as first sent printed "validated" there, which
  the review showed. A unit with such a call on a path that the run does not
  take is not detected: that is an omission, and the header of
  `FlambdaWellKindedSpec.v` says so.
- Tupled functions are not in the model: a call of unknown arity gives
  one a single argument, the tuple, whatever the arity of its code (a
  direct call and a call of known arity go by the arity of the code).
  The converter refuses code that is tupled (`Code0.is_tupled`). The
  arities do not show it: the reviewer's example has code of one
  parameter, so the call and the code agree, and without the refusal the
  machine ran it and returned the tuple where the compiler returns its
  field: a wrong result, not an undefined one.

## 9. Decisions, and the comments left for the human

Ruled: D9 (a call at other arities is undefined), D10 for calls and
primitives (undefined where executed), D12 (no check stricter than the
compiler; the compiler is the compiler without
`-flambda2-kind-checks`).

Settled by the orchestrator: D11, what the test tool does with the
check's answer. It prints it for the unit before and for the unit
after, and goes on. The comment before `well_kinded_unit` says so and is
no longer a question.

Open, with a review comment addressed to mshinwell in two `Spec` files
(`FlambdaSemanticsSpec.v` before `step`, and before `well_kinded`):

**D10, the rest.** A value of another kind than the one its binder
gives, bound by a `Let` or as a parameter of a handler; a field of a
static block or a value slot of another kind. The machine does not test
these. (The fields of a block that a primitive makes are tested, as
arguments of the primitive.) The compiler has a hardcoded check for each
and stops where Simplify visits the node, so Simplify never turns one
into `Invalid`, and no well-typed program is known to produce one.

- (a) as built: the machine does not test; the check answers no. The
  statements about well-kinded units have the check as their premise;
  the statements about the compiler's terms have none and say nothing
  of the kinds of what variables hold.
- (b) the machine tests the kind of a value where a variable is bound,
  and the mismatch is undefined where executed, as for calls.

The series lands (a). The orchestrator reads the ruling ("a mismatch of
kinds is undefined where it is executed") as (b), and the types need
the fact that (b) gives, so (b) is expected as a later epoch unless the
human says otherwise. What it is and what it costs, so that the choice
can be made:

*The change.* Two tests in the machine, and nothing in the terms. A
`Let x kind d body` has no step unless the value of `d` has kind `kind`.
The application of a handler has no step unless the values have the
kinds of its metadata, which takes in the count of arguments. A call
needs nothing more (step B). A value slot and a field need no test of
their own: what is read from one is tested by the `Let` that binds it.
An exit through a continuation that is not bound is the interface of
the term and is not tested.

*What it gives.* In every run, with no premise, a variable bound by a
`Let`, or as a parameter of a handler or of code, holds a value of the
kind of its binder (the parameters being distinct). The environment of
kinds that the check computes is then right for every closed term and
not only for those that pass, and conditions 2 and 3 of the check
(section 3) stop being conditions on terms: they say what is undefined.

*Statements that change.*

- `remove_unused_total_lets_equivalent`,
  `remove_unused_defined_lets_equivalent`: the functions must test the
  kind of what they remove. For a constant or a symbol that is a test on
  the term; for a variable it needs the kinds of the variables in scope,
  in place of the list of variables that
  `remove_unused_defined_lets` carries now.
- `thread_switches_equivalent`: the handler of no parameters that is
  threaded through must have no kinds either; a test on the term.
- `inline_known_calls_equivalent` gets simpler. The `Let`s of the
  inlined body test what the call tested, so the guard keeps the
  comparison of the arities and loses its condition on the arguments.
  The list of variables of known kind for the inliner (C0's sketch) is
  then not needed.
- `kind_fault` gains the two reasons, and
  `well_kinded_no_kind_fault` with it.
- The step lemmas: `step_let`, `step_apply_cont_handler`, and C3's
  three for a `Let` of its forms.
- `let_cont_apply_cont` (a handler applied where it is defined runs
  with its parameters bound) gains a premise: the values have the kinds
  of the handler. Its two companions make a `Let` of the parameter at
  the kind of the handler, which tests the same, and are to be checked.
- The eight statements of the types files about a `Let` are to be read
  again by their owner. The two I have read hold as written:
  `let_simple_canonical` keeps its `Let`, and `inline_identity` is a
  refinement whose two sides apply the same continuation to the same
  value.
- Unchanged as written: the refinements (`unused_let`,
  `remove_unused_lets`, `inline_tail_conts`, `collapse_switches`,
  `inline_calls`), the statements about renaming and alpha-equivalence,
  `fold_constants_equivalent` and `follow_aliases_equivalent` (the
  `Let` stays, with the same value), and `validate_unit_sound`.

*Proofs.* 71 proofs in 13 files step through a `Let` or the application
of a handler (35 through a `Let`, 49 through a handler; 9 go by cases on
every construct). Step B touched about a dozen. Most gain one case
split. The work that is not mechanical is the environment of kinds in
`FlambdaNormaliseProofs.v`, and showing in `FlambdaContextProofs.v`
that related environments hold values of the same kinds.

*Estimate.* Three to four times step B: 800 to 1200 lines, as an epoch
of its own. The conversion in the test tool does not change. Every
example is run again; I expect none to lose its validation, as the one
unit that fails the check today (`kinds_dead_cont.fl`, before Simplify)
fails in an arm that is not run.

Recommendation: (a) in this series; (b) as its own epoch, after C5's,
whose forms it would otherwise have to be repaired for twice.

Not a decision but to be known: partial and over-applications are
undefined on the machine and should not be (section 8). Adding them to
the fragment is the repair; it is not in this request.

## 10. The review of the second version, answered

- B1 (flat arities erase what decides `Invalid`): arities are the
  compiler's trees; no product is rejected; examples for arguments and
  for results.
- B2 (the prototype's evaluator of primitives was wrong on
  `Opaque_identity` and `Is_int`): the series uses C1's `eval_prim`.
  The two negative cases are examples in the Proofs file
  (`example_opaque_undefined`, `example_is_int_undefined`) and in
  `tests/semantics/` (`kinds_opaque_bad.fl`, `kinds_is_int_bad.fl`):
  both pass the check and are undefined before Simplify.
- B3 (the check is stricter than the compiler on code that Simplify
  removes before it looks): the check is a diagnostic and a sufficient
  condition; headers and this text say "where it visits"; the dead-arm
  unit is an example on each side.
- B4 (the check does not certify the converter's arities): the claim is
  gone; section 8 says what is trusted.
- N1 (`let_params` total on malformed annotations): done in step A.
- N2: the comment on `kind_of_value` is C1's now; the count of
  statements with hypotheses about primitives is none; the prototype
  directory and its README are not in the series.
- For the types: section 3, last paragraph.
- C3's forms: done in the rebase over C3's epoch. The check has cases
  for `Closure_of_set` and `Project_function_slot` (a `Value`),
  `Project_value_slot_from` (the kind of the slot),
  `Static_const_closure_of_set`, and the two new closure values; a `Let`
  of `let_closures` or `let_projections` is at kind `Value`. C5's are
  to come with its epoch: the exception continuation of an `Apply` at
  `Value` followed by the kinds of its extra arguments, a case for the
  new form of `cont_value`, and `hm_is_exn_handler`.

The review of the series, as first sent (R2):

- `partial_or_over_application` is the test of arities and not all that
  the compiler asks: the comment says so, names the call with no
  argument (a fatal error of the compiler, not `Invalid`) and the
  tupled case; `at_partial_or_over_application` asks also that the
  values of the arguments are of the kinds of the call's arity, with an
  example on each side.
- The tool printed "not decided" and then "validated" for a pair whose
  runs stop at a partial application: it now attempts no validation
  there, and the ledger says what the wrapper covers.
- Tupled functions: refused by the converter; an example
  (`kinds_tupled.fl`, the reviewer's).
- The count of statements that change in step A was nineteen, not
  twenty; with C3's four and one of N1's it is twenty-four, named in
  section 6.
- The comment for D10 before `step` tells the fields of a static block
  from those of a block made by a primitive, which are tested.
- Section 3: what the machine gives with no premise needs distinct
  binders to be a fact about a lookup, and is about the arguments only;
  section 1: nothing is tested of the values returned.

## 11. The series

On `flambda2-rocq/C2-epoch`, each commit passing `make -C rocq -j16 all`
and `make -C rocq assumptions`:

1. step A: terms carry kinds and arities, and the machine ignores them;
2. step B: a call is undefined unless it agrees with the code called;
3. the check of kinds: `FlambdaWellKindedSpec.v`,
   `FlambdaWellKindedProofs.v`;
4. this request, the status file, my entry in `OWNERS.md`;
5. lines for the shared lists (`rocq/Makefile`, `FlambdaExtract.v`);
6. the test tool, the ledger, ten new examples and the expected files
   (every converted example gains a line), which C0 applies with the
   regenerated extracted files.

Step A can land without step B: it then needs the part of commit 6 that
converts the annotations, which is separable (the tests at a call and
the reports of partial applications are not).

## What is unfinished

- No large corpus of the compiler's own units has been through the
  check or the machine. The evidence is programs written for the
  purpose, and V2's fifteen small units made from OCaml sources, which
  pass.
- The compiler's hardcoded checks were exercised by hand-written terms
  on the prototype branch, kept there with what the tool printed; they
  are not in the series, as the test tool does not catch a fatal error
  of the compiler.
- The cases for C5's forms wait for its epoch.
- Partial applications, over-applications and tupled functions are not
  in the fragment (section 8).
- The list of variables of known kind for `inline_known_calls` (C0's
  sketch) is not built; section 7 says what is lost without it.
