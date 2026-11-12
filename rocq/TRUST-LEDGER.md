# Trust ledger of the Rocq developments

What the theorems rest on that no proof covers: every axiom, and every
piece of OCaml that is trusted. Each has its reason. A `Parameter` is an
axiom too: it assumes that something of its type exists.

The first part of each section is checked. `make -C rocq assumptions`
fails if

- Rocq reports an axiom that this file does not list, or this file lists
  one that Rocq no longer reports (the report is the one of `rocq check`
  on every module of `rocq/Makefile`, printed under "Global assumptions");
- a statement of a Spec file of the Flambda 2 libraries depends on an
  axiom that is not in the section "Flambda 2" below (`Print Assumptions`
  on each theorem that `make claims` checks).

The trusted OCaml cannot be checked by a tool. It is listed for the
reviewers, who read it against the compiler.

The rules, for the Flambda 2 work (`middle_end/flambda2/rocq/`
`PARALLEL-PLAN.md`, sections 4, 5 and 7):

- Nothing is `Admitted`, and there is no axiom that is not here.
- No workstream adds to this file without a reviewer's sign-off. The
  reviewers (R1, R2) own it.
- It should shrink. Each entry of the Flambda 2 section says what would
  remove it.

The format, which the check relies on: an axiom is a list item that
begins with its fully qualified name between backquotes, and nothing else
begins so. The second check takes the Flambda 2 axioms to be those
between the heading "Flambda 2" and the next heading of its level.

## Flambda 2

The libraries `OxCamlFlambda2` (`middle_end/flambda2/rocq/`) and
`OxCamlFlambda2Types` (`middle_end/flambda2/types/rocq/`).

### Axioms

None. No statement of these libraries depends on an axiom: none uses
classical logic, Rocq's primitive integers or the models of OxCaml's
types below. (There were seven, all about the primitives, which the model
left abstract. The primitives are now data,
`middle_end/flambda2/rocq/FlambdaPrimitiveModel.v`, and what they compute
is a definition, `FlambdaPrimitiveSpec.v`.)

### Trusted OCaml

None of this is used by a proof. It is what connects the proofs to the
compiler in the tests of `middle_end/flambda2/tests/semantics/`: when the
tool reports a pair of terms as validated, the theorem
(`FlambdaValidateSpec.validate_unit_sound`) is about the two model terms,
and what follows is why they stand for what Simplify was given and what
it gave back.

- **The conversion of terms**, in
  `middle_end/flambda2/tests/tools/flsemantics.ml` (`convert_expr` and
  the functions around it, about 230 lines): from the compiler's Flambda
  terms to the terms of `FlambdaModel.v`. It is trusted to give a term
  with the meaning of the one it is given, and to refuse (`Unsupported`)
  what the model has not got, never to approximate it. To be read case by
  case against `terms/`; that reading is not done. A second reading in
  the other direction is: `flmodel_to_fexpr.ml`, beside the tool, prints
  a term of the model back as fexpr, and `flsemantics.exe -round-trip`
  (`flroundtrip.ml`) converts a unit, prints it, reads the text again
  with the compiler's parser, converts that, and compares the two terms
  with the model's comparison, for the unit of each example and for the
  unit that Simplify makes of it
  (`middle_end/flambda2/tests/semantics/roundtrip/`). This finds a case
  that the conversion gets wrong in a way that is not the same both
  times (two arguments exchanged, a number changed). It does not find
  what the conversion drops and the printer does not put back, nor a
  mistake made the same way in both directions, and it does not look at
  what the conversion does to the two units of a check together. The
  printer and the round trip are OCaml and add nothing to what is
  trusted: they change no theorem and no answer of the validation. A
  mistake in them can make this check miss a mistake of the conversion,
  report a difference that is not one, or fail. Of a set of closures the
  conversion is trusted
  for three things that no statement covers. The order of the
  declarations: the functions of a set are given in the order of
  `Function_declarations.funs_in_order`, and the variables of a `Let`
  are paired with them by position. The symbols of a static set: each
  closure symbol of the compiler's pattern is given with the function
  slot it is bound at; the tool refuses a pattern whose function slots
  are not those of the set, in order, and `well_formed_unit` checks the
  result again. And the choice between the model's two presentations of
  a set: one for a whole unit, the same for the two units of a check,
  the unnamed one only where every set has one function and no function
  slot is projected. What the compiler's two patterns expand to is not
  in the OCaml: it is `let_closures` and `bind_closures`, in Rocq, with
  statements.
- **The kinds and arities that the conversion gives**, in the same file
  (`convert_arity`, `convert_params_kinds`, `convert_bound_var`,
  `find_value_slot`, and the arities in `convert_code` and
  `convert_apply`, about 70 lines). A `Let` gets the kind of its
  variable, a handler the kinds of its parameters, code and a call their
  two arities with their unboxed products, and the value slots met their
  kinds. The variables that a `Let` binds to the closures of a set of
  several functions get the kind `Value` from `let_closures`; the tool
  refuses the binding if one of the compiler's variables has another
  kind. The machine makes a call undefined that does not agree with its
  code (`FlambdaSemanticsSpec.call_function`), so a wrong arity makes a
  run undefined that should not be, or the reverse. The check of kinds
  (`FlambdaWellKindedSpec.v`) does not catch that: code that never
  returns passes it with any result arity. Trusted: that the arities of
  calls and of code, the kinds of parameters and the kinds of value
  slots are the compiler's. Cross-checked as the tool runs, and fatal to
  it: an arity as converted, unarized by the model, has the kinds of the
  compiler's `Flambda_arity.unarize`; the parameter arity of code,
  unarized, has the kinds of the parameters of its body (nothing in the
  compiler checks that where code is made). Not cross-checked: how an
  arity is grouped into unboxed products, which is rebuilt through
  `Flambda_arity.fold_per_parameter`.
- **Partial applications, over-applications and tupled functions**,
  which the model has not got: there a call with more or fewer arguments
  than the code has parameters is undefined, and code has no mark that
  it is tupled. What the tool does about them is OCaml, in the same
  file, and is trusted. The converter refuses (`Unsupported`) code that
  is tupled (`Code0.is_tupled`), whatever calls it. It refuses a direct
  call whose arities pass the compiler's test for a partial application
  or an over-application, against the arities of the code named, when
  the unit binds that code: the test is
  `FlambdaWellKindedSpec.partial_or_over_application`, a test of
  arities only, to be read against `simplify_direct_function_call` of
  `simplify/simplify_apply_expr.ml`. An indirect one cannot be told from
  the term. When the run of either unit stops at a call that passes the
  test on a state (`at_partial_or_over_application`: the arities, and
  the kinds of the values of the arguments), the tool prints "not
  decided", does not compare the two runs, and does not call
  `validate_unit`. Not covered: a unit with such a call on a path that
  the run does not take, or beyond the fuel; a direct call of code that
  the unit does not bind. Of such a unit `validate_unit` may answer yes:
  its statement then holds of the model, where the call is undefined,
  and says nothing of what the compiler makes of the unit there. This
  goes when the fragment has the three.
- **The conversion of primitives**, in the same file (the section
  "Primitives"): one function for each arity of primitive that the model
  has (`convert_unary_primitive`, `convert_binary_primitive` and, once
  the model has `Make_block`, `convert_variadic_primitive`), with the
  conversions of what a primitive carries (`convert_kind`,
  `convert_standard_int`, the signedness, the operations and the
  comparisons; later `convert_boxable_number` and `convert_or_unknown`).
  It is about 95 lines with the primitives of the first stage and 145
  with those of the third. It says which primitive of
  `FlambdaPrimitiveModel.v` stands for one of the compiler's. It is a
  renaming of constructors, with the fields the model keeps. Trusted:
  that it sends a primitive to the one of the same name, and refuses a
  primitive, or a value of a field, that the model has not got. Of the
  primitives that allocate or load, that is: an allocation that is not
  on the heap; a block that is not immutable or not of values; and, for
  `Make_block`, a kind of a field that says more than `any_value`, as
  the model has no subkinds and Simplify uses them. What a primitive
  computes is not here: it is `FlambdaPrimitiveSpec.eval_prim`, to be
  read against `terms/flambda_primitive.mli` and
  `simplify/simplify_*_primitive.ml`.
- **The conversion of numeric constants**, in the same file (the section
  "Numbers" and `convert_const`, about 75 lines; with the boxed numbers
  also `convert_float32`, `convert_float` and the boxed numbers of
  `convert_static_const`, about 105 lines in all): from the compiler's
  integers of each width, and then the bit patterns of its floats, to the
  integer that a constant of the model carries. Trusted: that each number
  is converted to itself, at every width and at its bounds. (It was not
  so: until this conversion went through `int64`, `z_of_int` converted
  the least tagged or naked immediate to -1, and what the tool reported
  before then is not made good by the repair.) Constants of the vector
  and mask kinds, and poison, are refused, so the tool does not exercise
  what the model says of boxing and unboxing at those kinds.
- **The numbering of names**, in the same file (`Numbering`, about 30
  lines): each variable, continuation, symbol, code id, value slot and
  function slot of the compiler gets a number, the same throughout a
  unit. Trusted: that the compiler's names are fresh, so that one name
  stands for one thing. A function slot of the compiler may get the
  number 1, which is also the model's `unnamed_function_slot`; the two
  are not in one unit, by the choice of presentation above.
- **The identification of names across the two terms**, in the same
  file (`convert_both` with `code_id_used`, about 70 lines). The two
  units are converted with one numbering, the return and exception
  continuations of the unit after standing for those of the unit before.
  And Simplify gives a new code id to each new version of code: the tool
  gives the new id the number of the old one where the old one is bound
  as deleted and not otherwise used. Trusted: that this identifies only
  what is the same continuation and the same function. The second part
  goes when the comparison relates code ids itself (workstream S4; there
  are notes in `flsemantics.ml` and `FlambdaCompareSpec.v`).
- **The extraction**: Rocq's extraction to OCaml, by
  `middle_end/flambda2/rocq/FlambdaExtract.v`. It has no directive that
  realises a definition of the model by hand-written OCaml. The extracted
  modules are in `middle_end/flambda2/tests/semantics/extracted/`.
- **What the tool reports**, in the same file (`check`, `run`,
  `observe`): that it calls `validate_unit` on the two terms converted,
  and prints its answer as it is. The comparison of the two runs that it
  also prints is a test of one run, and no theorem is about it.
- **The conversion of types**, in
  `middle_end/flambda2/tests/semantics/types/type_converter.ml` with
  `model_numbers.ml` and `model_names.ml`: between `Type_grammar.t` and
  `flambda_type`, both ways. Trusted: that each case is the
  correspondence its comment states; that it refuses what one side lacks
  and never approximates; that on the way to the model it drops only the
  `rec_info` of a function type, the expression of a `Rec_info` head,
  the string of `Poison`, the cache of free names, and a relation that
  the compiler's map binds to the empty set of names (so the round trip
  from the compiler is the identity only up to these); that a numbering
  is one-to-one for each sort of name; that a number is read as the file
  says (an integer by its signed value, and the bits of a float, a mask
  or a vector as an integer in two's complement of as many bits, which
  is the reading of `const_in_range` in FlambdaPrimitiveSpec.v and of
  the converter of terms) and one out of range is refused; that the
  size of a case of blocks is read
  and made faithfully through `Row_like_for_blocks.get_singleton` and
  `create`; and that the names `Flambda2_types__...` of the build are the
  modules of the types library.
  Also trusted, of the two functions that the round trip from the
  compiler uses: that `type_to_model_with_what_is_dropped` is
  `type_to_model` and gives besides the `rec_info` of every function
  type of the type, with the code id of that function type, and the
  variables that those and the expressions of the `Rec_info` heads of
  the type mention; that `type_of_model_with_rec_infos` is
  `type_of_model` but that a function type gets the first `rec_info`
  listed for its code id, if there is one; and that the two references
  through which they work are as they were when either returns or
  raises, so that `type_to_model` and `type_of_model` are the
  conversions described above.
- **The tests of types**, in the same directory (`model_type.ml`,
  `type_generator.ml`, `types_difftest.ml`). No theorem rests on them;
  what a reader of their output trusts:
  - `Model_type.normalise` and `same`: that two types of the model are
    identified only up to how maps and sets are written;
  - the comparison of what two joins give (the binary and the n-way; one
    join on arguments that are one value and on two copies), and of two
    meets with what they teach in the shared and unshared comparison:
    it is of text, not `Model_type.same`. `print_joined` (the type of
    the parameter and what the join says of each variable of its own
    that this type reaches; nothing of what the joined environment says
    of the names of the tests, so two joins that differ only there
    print alike), `print_joined_with_names` (the same with the types of
    the names of the tests and every variable of the join's own that
    any of these reaches; the shared parts use it) and
    `print_with_own_variables` (the types of an answer) print the result
    written in one way, and `rename_own_variables` names the variables
    that are not of the tests `e0`, `e1`, ... in the order in which the
    whole text mentions them, once for the whole text.
    Trusted: that the printer of `model_type.ml` shows every part of a
    type, and that the renaming touches nothing but those variables, so
    that equal text is the same type up to the names of those variables.
    Unequal text may be two writings of one type: it is then counted as
    a difference, never as agreement;
  - the adapters that call the compiler: that `call_in_the_compiler`
    calls the function named with the arguments converted; that `binary`
    and `n_way` are the two implementations; that `join_env` is the join
    at a continuation of one parameter of the kind given with one use
    for each type, each use knowing besides what `known` says and
    binding the variables of `locals`; that `joined_of_env` reads from
    the joined environment the type of the parameter and of each
    variable not of the tests that this type reaches, or that the types
    given as `reached_from` reach; that
    `types_of_names` reads what an environment says of each name; that
    `or_fatal_error` reports the first line that the compiler wrote
    before it stopped; that the structural setting of the flag for the
    sharing of joins is set before any join is run, and that
    `with_join_sharing` puts the compiler's default in its place only
    for the two runs whose titles name it; that `shared_parts` builds
    its types with the compiler's `More_type_creators.immutable_block`,
    `Type_grammar.create_variant` and `Env_extension.create` around
    parts that the converter made, and calls a case not shared only
    where the two copies are not one value;
  - the semantic checks: that they ask `type_satisfied_b` (extracted,
    proved to decide `type_satisfied`) and nothing else whether a value
    has a type; the generators of values and worlds are trusted for
    nothing;
  - the variables that a join makes of its own (`has_joined`): a value
    is said to have what a join gives only when, with the parameter
    holding the value, each such variable is given a value that has the
    type the joined environment gives it, or no value, and the value has
    the type of the parameter. The search is finite: when it finds
    nothing the case is reported as not run, never as a failure. What
    the joined environment says of other names and of aliases is not
    checked. A failure is reported only when there is no such variable;
  - the reporting: a comparison counts as agreeing only cases that were
    run and whose premise some value tried satisfies; a failure of the
    compiler or a refusal of the converter is "not run"; a disagreement
    that is recorded is shown with its label and does not fail the test;
    any other disagreement makes the test fail;
  - the chosen joins: that the values shown are tried as the lines say;
    nothing is concluded from "not for the values tried".
  - the files `type_comparisons.ml` and `types_of_compilations.ml`
    beside those named;
  - `same_text`: two printed answers are taken to be the same when
    they have the same words in the same order. Trusted: that the
    printer of `model_type.ml` brackets every part of a type and
    writes a string as its bytes, so that where its lines are broken
    says nothing;
  - the examples of the join (`examples_of_joins`): that an example
    marked with the name of a statement has the inputs and the answer
    of that statement of
    `middle_end/flambda2/types/rocq/FlambdaJoinTypesExamplesSpec.v` as
    the file was when the example was written (the variables, slots
    and code ids are those of the tests); that one marked as having
    another answer has the inputs of the statement; a difference is
    shown and does not fail the test;
  - the equality and the predicate: that `Type_equal.type_eqb` and
    `Well_formed.type_well_formed` are the extracted functions, and
    that the predicate is asked of the type with its maps written in
    one way where a map of the input may bind a key twice;
  - the round trip from the compiler: that the type which comes back
    is made with the `rec_info`s that the conversion to the model
    recorded, and only when no code id has two that differ for
    `Type_grammar.equal`; that the two types are then compared whole,
    as printed, by `Equal_types_for_debug.equal_type` and by
    `Type_grammar.equal`;
  - the free variables: that where what the converter dropped mentions
    no variable the two sets are compared as they are, and that the
    other comparison adds exactly the variables recorded as dropped;
  - the types of compilations: that `names_of` lists the variables
    that the levels of an environment define after the initial scope
    and the symbols that it defines (names of other units are not gone
    through); that the type compared is `Typing_env.find` of the name;
    that a type of a name is left out only if `Type_grammar.equal`
    says it is one already compared for that name; that Simplify
    reports to the observer where the types library says it does; and
    that the tool runs itself once for each unit listed and adds up
    what each run counted.
  - the examples of the meet (`examples_of_meets`): that an example
    has the name of a statement of FlambdaMeetMatchExamplesSpec.v,
    FlambdaMeetTagExamplesSpec.v, FlambdaMeetProjectionExamplesSpec.v
    or FlambdaMeetExamplesSpec.v
    (`middle_end/flambda2/types/rocq/`), and the steps, the two types
    and what that statement says of the type answered and of the
    variables, as the file was when the example was written; that
    where the statement speaks of two meets the example says which;
    that `scenario` numbers the variables from 1 in the order given
    and makes the environment by the calls of the steps, the
    relations by `Flambda2_types.Typing_env` with the flag that
    chooses the meet set to the implementation run; that the
    environment read through the observer is the one those calls
    made; a difference is printed and counted, and does not add to
    the disagreements of the test;
  - the chosen meets: nothing but that what is printed is what was
    seen;
  - the creation functions: that a call on which the model's function
    answers `None` is counted as agreeing when the compiler's raises
    a fatal error or `Invalid_argument`, whatever the message; that
    `kind_for_const` is compared through the unknown type of the
    kind;
  - `must_be_singleton`: that the model's outer `None` is compared
    with a fatal error of the compiler.

Not trusted, though it is OCaml: which static bindings the tool proposes
to remove as unused (`unused_statics`). The extracted `drop_statics`
checks the proposal, and `validate_unit_sound` holds whatever it is.

## The SSA loop passes

The libraries `OxCamlStdlib` (`rocq/`), `OxCamlBackend` (`backend/rocq/`),
`OxCamlSsa` (`backend/ssa/rocq/`) and `OxCamlLoop`
(`backend/ssa/loop/rocq/`). `ROCQ-REVIEW-GUIDE.md` (sections 2.3 and 2.4)
says what each group is to be checked against; the reasons here are
short. The trusted OCaml of these libraries is the extraction directives
of their `*Extract.v` files and the hand-written rewrites of the passes,
which that guide covers (sections 2.3, 4.7 and 5.5).

### `Int64` (`rocq/OxCamlInt64.v`)

Rocq has no 64-bit machine integer. `Int64` is an abstract type with its
operations, and each axiom is the documented behaviour of one OxCaml
operation; `int32`, `int64` and `nativeint` are the types of constants
the models carry and do not compute with.

- `OxCamlStdlib.OxCamlInt64.Int64.abs_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.add_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.compare_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.div_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.equal_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.mul_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.neg_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.of_int_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.rem_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.shift_right_logical_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.shift_right_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.sub_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_bounded`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_max_int`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_min_int`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_minus_one`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_one`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_zero`
- `OxCamlStdlib.OxCamlInt64.Int64.to_int_exact`
- `OxCamlStdlib.OxCamlInt64.int32`
- `OxCamlStdlib.OxCamlInt64.int64`
- `OxCamlStdlib.OxCamlInt64.int64_abs`
- `OxCamlStdlib.OxCamlInt64.int64_add`
- `OxCamlStdlib.OxCamlInt64.int64_compare`
- `OxCamlStdlib.OxCamlInt64.int64_div`
- `OxCamlStdlib.OxCamlInt64.int64_equal`
- `OxCamlStdlib.OxCamlInt64.int64_max_int`
- `OxCamlStdlib.OxCamlInt64.int64_min_int`
- `OxCamlStdlib.OxCamlInt64.int64_minus_one`
- `OxCamlStdlib.OxCamlInt64.int64_mul`
- `OxCamlStdlib.OxCamlInt64.int64_neg`
- `OxCamlStdlib.OxCamlInt64.int64_of_int`
- `OxCamlStdlib.OxCamlInt64.int64_one`
- `OxCamlStdlib.OxCamlInt64.int64_rem`
- `OxCamlStdlib.OxCamlInt64.int64_shift_right`
- `OxCamlStdlib.OxCamlInt64.int64_shift_right_logical`
- `OxCamlStdlib.OxCamlInt64.int64_sub`
- `OxCamlStdlib.OxCamlInt64.int64_to_Z`
- `OxCamlStdlib.OxCamlInt64.int64_to_int`
- `OxCamlStdlib.OxCamlInt64.int64_zero`
- `OxCamlStdlib.OxCamlInt64.nativeint`
- `OxCamlStdlib.OxCamlInt64.nativeint_to_int64`

### Overflow tests (`rocq/IntArith.v`)

Four tests of whether a sum or a product fits its type, each a few lines
of OCaml in `rocq/IntArithExtract.v` that are easier to read than to
model, with an axiom saying that it answers the question.

- `OxCamlStdlib.IntArith.add_fits`
- `OxCamlStdlib.IntArith.add_fits64`
- `OxCamlStdlib.IntArith.add_fits64_spec`
- `OxCamlStdlib.IntArith.add_fits_spec`
- `OxCamlStdlib.IntArith.mul_fits`
- `OxCamlStdlib.IntArith.mul_fits64`
- `OxCamlStdlib.IntArith.mul_fits64_spec`
- `OxCamlStdlib.IntArith.mul_fits_spec`

### List functions (`rocq/OxCamlList.v`)

Two functions of OxCaml's `List` that are mapped onto OxCaml's own
instead of being extracted, with what the models use of them.

- `OxCamlStdlib.OxCamlList.compare_length_with`
- `OxCamlStdlib.OxCamlList.sort_uniq`
- `OxCamlStdlib.OxCamlList.sort_uniq_In`
- `OxCamlStdlib.OxCamlList.sort_uniq_NoDup`

### Operations of the backend (`backend/rocq/Operation.v`)

The payloads of `Operation.t` that no model looks inside are abstract
types. `specific_linear` is the target's reading of its specific
operations as linear combinations of their arguments, the one thing
taken on trust about a target's semantics.

- `OxCamlBackend.Operation.addressing_mode`
- `OxCamlBackend.Operation.alloc`
- `OxCamlBackend.Operation.float_operation`
- `OxCamlBackend.Operation.float_width`
- `OxCamlBackend.Operation.int128_operation`
- `OxCamlBackend.Operation.intop_atomic`
- `OxCamlBackend.Operation.load`
- `OxCamlBackend.Operation.memory_chunk`
- `OxCamlBackend.Operation.name_for_debugger`
- `OxCamlBackend.Operation.probe_is_enabled`
- `OxCamlBackend.Operation.reinterpret_cast`
- `OxCamlBackend.Operation.signedness`
- `OxCamlBackend.Operation.specific_linear`
- `OxCamlBackend.Operation.specific_operation`
- `OxCamlBackend.Operation.static_cast`
- `OxCamlBackend.Operation.symbol`
- `OxCamlBackend.Operation.test`
- `OxCamlBackend.Operation.vec128_bits`
- `OxCamlBackend.Operation.vec256_bits`
- `OxCamlBackend.Operation.vec512_bits`

### The SSA graph (`backend/ssa/rocq/SsaModel.v`)

Blocks, instruction identifiers and sets of blocks are the compiler's
own data, abstract in the models: the types, the observations the models
make of a block, equality tests with the axioms that they decide
identity, and sets with the axioms of membership.

- `OxCamlSsa.SsaModel.all_successors`
- `OxCamlSsa.SsaModel.block`
- `OxCamlSsa.SsaModel.block_body`
- `OxCamlSsa.SsaModel.block_eqb`
- `OxCamlSsa.SsaModel.block_eqb_spec`
- `OxCamlSsa.SsaModel.blockset`
- `OxCamlSsa.SsaModel.dominates`
- `OxCamlSsa.SsaModel.instr_id`
- `OxCamlSsa.SsaModel.instr_id_eqb`
- `OxCamlSsa.SsaModel.instr_id_eqb_spec`
- `OxCamlSsa.SsaModel.op_def`
- `OxCamlSsa.SsaModel.op_def_find`
- `OxCamlSsa.SsaModel.param`
- `OxCamlSsa.SsaModel.params`
- `OxCamlSsa.SsaModel.predecessors`
- `OxCamlSsa.SsaModel.raise_kind`
- `OxCamlSsa.SsaModel.set_add`
- `OxCamlSsa.SsaModel.set_empty`
- `OxCamlSsa.SsaModel.set_for_all`
- `OxCamlSsa.SsaModel.set_for_all_spec`
- `OxCamlSsa.SsaModel.set_mem`
- `OxCamlSsa.SsaModel.set_mem_add`
- `OxCamlSsa.SsaModel.set_mem_empty`
- `OxCamlSsa.SsaModel.set_mem_singleton`
- `OxCamlSsa.SsaModel.set_singleton`
- `OxCamlSsa.SsaModel.strict_dominators`
- `OxCamlSsa.SsaModel.terminator`
- `OxCamlSsa.SsaModel.value_eqb`
- `OxCamlSsa.SsaModel.value_eqb_spec`

## Rocq's own

### Primitive 63-bit integers

Rocq's `int` is OxCaml's `int`. Its operations are primitives of Rocq's
kernel, and their specifications are axioms of Rocq's library. Only the
SSA libraries use them.

- `Corelib.Numbers.Cyclic.Int63.PrimInt63.add`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.addc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.addcarryc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.addmuldiv`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.asr`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.compare`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.compares`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.div`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl_21`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.divs`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.head0`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.int`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.land`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.leb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lor`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lxor`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.mod`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.mods`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.mul`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.sub`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.subc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.subcarryc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.tail0`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.asr_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.compare_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.div_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.leb_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.ltb_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.mod_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.add_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.addc_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.addcarryc_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.addmuldiv_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.compare_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.div_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.diveucl_21_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.diveucl_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.eqb_correct`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.eqb_refl`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.head0_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.land_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.leb_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.lor_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.lsl_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.lsr_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.ltb_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.lxor_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.mod_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.mul_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.mulc_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.of_to_Z`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.sub_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.subc_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.subcarryc_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.tail0_spec`

### Classical logic

The excluded middle, used by the SSA libraries for case splits on whether
a register is defined. No statement of the Flambda 2 libraries uses it,
and the second check above keeps it so.

- `Stdlib.Logic.Classical_Prop.classic`
