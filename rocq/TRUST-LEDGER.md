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
- **Tupled functions** are in the model as code that is marked
  (`FlambdaModel.cm_is_tupled`), and the converter gives code the mark
  of `Code0.is_tupled`. Every call of the model gives tupled code its
  first argument as a tuple, which the machine takes apart; any
  arguments after it are given as they are, and make the call an
  over-application (`FlambdaSemanticsSpec.arguments_for_code`): that
  is the compiler's call of unknown arity. The compiler's direct call
  and its call of
  known arity give code its arguments as the code takes them, and the
  model has not got that of tupled code. So the converter refuses
  (`Unsupported`) a direct call of tupled code that the unit binds, and
  a call of known arity in a unit that binds tupled code; that is
  OCaml, in the same file, and is trusted. Trusted too: that a tuple
  given to tupled code that has parameters has the tag 0 and as many
  fields as the code has parameters. The machine makes any other call
  of such code undefined; the run time reads the first fields of
  whatever it is given (the review comment at
  `FlambdaSemanticsSpec.tuple_fields`). Tupled code with no parameter
  reads no field: its first argument is evaluated, and its kind is
  tested as that of any argument is, but neither its tag nor its
  fields are looked at
  (`middle_end/flambda2/tests/semantics/tupled_apply_zero.fl`).
- **Partial applications and over-applications** are in the model
  (`FlambdaSemanticsSpec.shape_of_closure_call`), and the converter
  gives a call its arguments and its two arities as they are, whatever
  its kind. Two things are trusted. A partial application is a value of
  the model that the compiler has not got as such (it makes a closure
  of a wrapper): at the end of a run the tool observes it as it
  observes a closure (`observe`, `Function`), without looking into it,
  so two runs that end with functions that differ are not told apart,
  as for closures. And the model takes every call for a generic
  application: a direct call, or an indirect one of known arity, with
  fewer or more arguments than its code has parameters is a partial
  application or an over-application in the model, where the backend
  stops on the first and compiles the second as a full call
  (discrepancy C3-9; the CR at `shape_of_closure_call`). The tool does
  not refuse such a call. Of a unit with one `validate_unit` may answer
  yes: its statement then holds of the model, and says nothing of what
  the backend makes of the unit there.
- **What the conversion of terms leaves out**, in the same file. These
  are the exceptions to "never to approximate", each with a `CR
  mshinwell` where it is done. *Depths*: the depth variables of
  recursion and the coercions that mention them are dropped
  (`depth_variables`), so the model sees nothing of what Simplify does
  with them. *Regions* (decision D37): the bindings of `Begin_region`
  are dropped, `End_region` returns the unit value and does nothing,
  and what is allocated in a region is converted as if it were
  allocated on the heap (`region_variables`). This is trusted of both
  units of a check, the one after Simplify as much as the one before:
  it is right for a unit in which nothing allocated in a region is used
  after the region has ended. A validation therefore does not
  establish that Simplify keeps the uses of a local allocation within
  the life of its region: a term that uses one later has, in the model,
  the meaning it would have with the allocation on the heap
  (discrepancy V2-3). The regions around a `try` (`Begin_try_region`,
  `End_try_region`) are dropped in the same way. There a region also
  ends when a raise leaves it open and the handler ends it, and the
  same is trusted of both units on that way out: nothing allocated in
  such a region is used in the handler after that, or later. One thing
  is kept of the region of a handler: the `Let` of its `End_try_region`
  (the one that is not a ghost) binds `Opaque_identity` of the unit
  value, where that of an `End_region` binds the unit value. The value
  bound is the same, so the unit means in the model what it meant;
  what changes is that the normalisations of the validator do not
  fold that `Let`, nor remove it for being unused
  (`FlambdaNormaliseSpec.prim_may_fold`), in either term, as Simplify
  does not delete the primitive for being unused (its effects are
  arbitrary, and `Flambda_primitive.is_end_region`, by which the end
  of an unused region is deleted, is of `End_region` alone). In the
  model as in the compiler it still goes with a handler or with code
  that is removed whole. It is a mark that something is done there,
  not a model of what is released. Without it the handler of a `try`
  that Simplify has demoted was, in the term before, a continuation
  that only applies another, and the validator forwarded to it where
  the compiler, whose handler ends the region first, has no shortcut
  (discrepancy C5-10).
  A region variable used as a value is refused. *Tupled functions*: a direct
  call of tupled code that the unit binds is refused, and so is a call
  of known arity in a unit that binds tupled code (the entry above);
  it is what keeps a call that gives code the components from being
  run as the model's call, which gives it the tuple.
- **Calls that never return**, in the same file (`convert_apply`). A
  call whose result continuation is `Never_returns`, whatever its call
  kind among those that the conversion takes (a method call, a C call
  and an effect are refused before that), is converted to a call that
  returns to a continuation bound around it and used nowhere else,
  whose handler is `Invalid` and whose parameters are of the kinds of
  the return arity of the call, which the call keeps; the continuation
  has a number that no continuation of the two units of the check has,
  and its parameters have numbers that no variable of them has (a
  number of one sort may be that of a name of another). The conversion
  interprets
  `Never_returns` as making a normal return undefined, and this
  interpretation is trusted. The backend inserts no trap for it: it
  emits the call with nothing after it, as it does a call in tail
  position (`to_cmm/to_cmm_expr.ml`, `apply_expr`). Nothing is assumed
  of the analysis by which Simplify finds that a callee never returns.
  If a run of the converted term after returns from such a call, it
  becomes undefined. Where the term before has a defined outcome,
  completed executions then expose the difference, and a sound
  validation cannot accept that pair. A validation is not a proof that
  the callee does not return in native code. The term of the model has
  a continuation that the compiler's term has not, and the round trip
  of the conversion prints it.
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
  primitives that allocate or load, that is: a block that is not
  immutable or not of values; and, for `Make_block`, a kind of a field
  that says more than `any_value`, as the model has no subkinds and
  Simplify uses them. An allocation in a region is not refused: it is
  converted as one on the heap, which is not a renaming of constructors
  and is one of the exceptions of the entry above (*Regions*). What a
  primitive computes is not here: it is
  `FlambdaPrimitiveSpec.eval_prim`, to be read against
  `terms/flambda_primitive.mli` and `simplify/simplify_*_primitive.ml`.
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
  and mask kinds are refused, so the tool does not exercise what the
  model says of boxing and unboxing at those kinds. A poison constant
  is converted to the poison constant of the model, of the kind that it
  carries; the string that says where the compiler made it is dropped.
  The poison of the model is the abstract one of decision D26: a
  constant with a kind and no bits. The backend gives the compiler's
  poison a number made from that string (`String.hash` of it, in
  `const` and `const_static` of `to_cmm/to_cmm_shared.ml`); the
  conversion follows the decision and not those bits.
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
  as deleted and not otherwise used, and then leaves out the
  declaration that the old one is deleted, so that the term of the
  model does not declare deleted a code id that it binds. Trusted: that
  this identifies only what is the same continuation and the same
  function. The second part
  goes when the comparison relates code ids itself (workstream S4; there
  are notes in `flsemantics.ml` and `FlambdaCompareSpec.v`).
- **Symbols that a unit does not define**, in the same file (`imports`,
  about 15 lines, and `check`, which runs the two units from them). The
  conversion lists the external symbols that the two units of a check
  mention: the symbols of another compilation unit, the predefined
  exceptions among them, which are of a unit of their own. A symbol of
  the unit's own compilation unit that the unit does not define is not
  one of them, and stays bound to nothing. Both units are run from the
  static environment that binds each listed symbol to something
  imported (`FlambdaImportsSpec.imports_statics`), an object whose
  contents the model does not know. A symbol is given the class
  `Import_identity` if it is a predefined exception
  (`Symbol.is_predefined_exception`) and `Import_data` otherwise. Three
  things are trusted. The list is the same for the two units: a symbol
  that one of them mentions is declared for both. A predefined
  exception is an object made once, by the startup code, that nothing
  the unit allocates and no other symbol is: the model answers false to
  `Phys_equal` of it against an allocated value of the unit and against
  an import that is data, and answers by the symbols for two of them;
  the compiler does not prove the first of these (the CR at
  `eval_phys_equal`). And the model does not look into an import. It
  can be passed, returned, stored (`Make_block` takes one as a field)
  and given to `Opaque_identity`, which returns it. `Phys_equal`
  answers false of an import of either class against a tagged
  immediate, compares an identity as just said, and has no value of an
  import that is data against an immutable allocated value, another
  import that is data or itself. That is
  `FlambdaPrimitiveSpec.eval_phys_equal`, which the machine that the
  tool runs uses (`FlambdaSemanticsSpec.step`); it has no value on a
  location of the heap, against an import as against anything.
  `Phys_equal` of the machine with a heap (`FlambdaHeapSpec.exec_prim`),
  which the tool does not run, answers false of an import of either
  class against a location bound by that heap. No other unary or
  binary primitive has a value on an import. It is not a closure, so a
  call of it is undefined. A run that executes a load from an import,
  or a call of one, is therefore undefined in the model where the
  compiler gives it a meaning. Merely containing such a load or call
  does not make the run undefined.
- **The extraction**: Rocq's extraction to OCaml, by
  `middle_end/flambda2/rocq/FlambdaExtract.v`. It has no directive that
  realises a definition of the model by hand-written OCaml. The extracted
  modules are in `middle_end/flambda2/tests/semantics/extracted/`.
- **What the tool reports**, in the same file (`check`, `run`,
  `observe`): that it calls `validate_unit` on the two terms converted
  or, where that does not validate them, `validate_unit_knowing` on the
  same two terms, and prints the answer as it is. The comparison of the
  two runs that it also prints is a test of one run, and no theorem is
  about it.
  For a unit that has imports (the entry "Symbols that a unit does not
  define") the two runs are from its imports. The theorem of the
  validator is of the two units run from the empty static environment,
  where an external symbol is bound to nothing. Of the two units run
  from their imports there is a theorem for three of its verdicts,
  which `FlambdaValidateImportsSpec.holds_from_imports` names: the same
  up to bound names, the same once normalised, and the same once the
  unused static bindings of the term before are removed as well
  (`validate_unit_sound_imports_statement`, and
  `validate_unit_knowing_sound_imports_statement` for the second
  asking). It is of no other verdict: not of a unit validated once
  something is lifted, nor of one that rests on a removal of static
  bindings from the term after. The tool asks that function, as it is
  extracted, of the verdict, and no line that it prints for a unit that
  has imports begins "validated:". Where the function accepts the
  verdict, the line begins "validated with its imports", and the
  verdict is of the two runs that the tool shows. Where the validator
  accepts with another verdict, what is validated is the unit run with
  nothing imported: the line begins "validated with nothing imported"
  and is followed by a line that begins "not validated with its
  imports", and the comparison of the two runs from the imports is
  then an execution of both terms that is compared, not a validated
  verdict. In that case the tool also runs the unit before from the
  empty static environment, to say where the validation with nothing
  imported is vacuous.
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
  - the model run: that `the_model` is the extracted
    `FlambdaJoinMeet.model_meet`, `model_add_equation`, `model_join`
    and the three functions of `FlambdaMeet.Flambda2_types` that add
    a relation, given the records of choices named, the depth of
    joins of the compiler's flag and fuel 200; that
    `scenario_in_the_model`, `env_of_model` and `join_in_the_model`
    make in the model the environments that `scenario`,
    `create_names` and `join_env` make in the compiler, call for
    call, the variables having the numbers of the numbering, but
    that the model adds each equation by a call of its own where
    `join_env` adds those of a use inside one `use_meet_env`, which
    is the same with the compiler's default strategy for the
    environment of a meet and is not claimed for the others;
  - what is seen (`seen_in_the_model`, `seen_in_the_compiler`,
    `print_seen`, `same_seen`): that the names asked are those that
    the scenario defines, and the parameter of a join; that a name
    is asked nothing of unless the environment defines it; that the
    type is `find` and the canonical element
    `get_canonical_simple_exn` at the name mode of types; that the
    other variables are those that the type answered and the types
    of those names reach, of which only the type is asked; that the
    variables numbered above the threshold are
    renamed in the order in which the text comes to them, and two
    texts are the same if `same_text` says so; that two sides which
    both give no answer are counted as the same whatever their
    reasons;
  - the names asked of a join (`names_asked_of_a_join`): that they
    are, on both sides, the names of the tests, the variables that
    the source defines for types only, each variable that a use
    binds, once, and the parameter;
  - the generated environments: that `generate_equations` and
    `generate_aliases` give a variable at most one equation, whose
    type mentions only variables numbered after it.
  - the types that are alike (`generate_alike`): that the two are a
    type of the generator and, on either side, that type again or
    one of the types of the same kind that the shrinker gives for
    it;
  - the types one step from a common type (`generate_siblings`):
    that each of the three is one of the types of the same kind that
    the shrinker gives for one type of the generator, or that type
    where it gives none;
  - the scenarios in the reverse order (`reversed`, in
    `scenarios_in_the_model`): that the definitions of the variables
    are moved before the other steps, in the reverse order, and
    nothing else of the scenario changes;
  - the inputs counted for T7-9 (`on_a_symbol`): that it says whether
    an extension of one of the two types met has an equation on a
    symbol of the tests (`has_an_extension_on`);
  - the generated inputs `generate_meet_of_relations`,
    `generate_meet_of_closures` and `generate_join_of_relations`:
    that they are what the comments at their definitions say; for
    the last, that the two equations of a relation at a use are
    those that `add_is_int_relation`, `add_get_tag_relation` and
    `add_is_null_relation` of the compiler add, in their order;
  - `up_to_the_alias_kept`: that it changes nothing of what is seen
    but the type of a name whose type is an alias, into the alias of
    the canonical element seen for that name, and only where the
    canonical element of what the alias is to, as seen (a constant:
    itself; a name: that of its line), is that element; that a
    difference between the model and the n-way meet which it removes
    is recorded under the label of T7-10 and is not a disagreement
    of the test; that the cases of `control_of_the_alias_kept` are
    what their names say;
  - the inputs counted for T7-9 by an alias of a symbol
    (`has_a_part`, `has_an_alias_of_a_symbol`,
    `an_alias_of_a_symbol`): that it says whether one of the two
    types met, or a type that an equation before the meet gives a
    name, is or has within it an alias of a symbol;
  - what is read of the analysis of a join (`analysis_of_the_model`,
    `analysis_of_the_compiler`): that the compiler's is read by
    `Analysis.simple_refined_at_join` with `fold_values_at_uses` and
    by `fold_variables_created_at_join` with
    `fold_definitions_at_uses`, and the model's by the extracted
    `simple_refined_at_join_of` with `values_at_uses` and
    `variables_created_at_join` with `definitions_at_uses`; that the
    names asked are those asked of the target which the target
    defines, and the variables made that what is seen reaches; that
    the uses are numbered by their positions on both sides;
  - its text (`print_analysis`): that the variables made have the
    names that the text of what is seen gave them, and that those
    created which it does not reach are ordered by what is read of
    them; that two analyses are compared only where what is seen of
    the two targets is the same;
  - the comparison of two readings (`compare_analyses`,
    `analysis_reading`): that it compares only where both joins
    answer a target and what is seen of the two is the same; that a
    reading missing on one side is then a disagreement, but for the
    one case counted as not run, in which the compiler's reader
    stops and a reader of the model has no answer;
  - `control_of_the_analysis`: that its two joins are what its
    comment says, and that the reader which stops is put in place of
    the compiler's and of nothing else.
  - the groups of static constants (`generate_static_group`,
    `static_const_of_model`): that the generator is what the comment
    at its definition says; that the constant of the compiler is the
    model's, an immutable block of the shape of values for a block,
    the boxed number of the kind of the constant for a boxed
    constant, a boxed float where the contents are a variable;
  - the two sides (`static_group_in_the_model`,
    `env_before_a_static_group`, `static_group_in_the_compiler`,
    `static_group_in_simplify`): that the model's environment is the
    one of `env_of_model` with the aliases added by the model's
    `add_equation`, and the compiler's is made by the functions that
    the types library exports, the names of the tests defined in
    the same order and the aliases added by its `add_equation`
    under the flag that chooses the meet; that Simplify is given
    that environment in the environment of the top level of a unit
    with no code, and is run on each prefix of the group; that its
    typing environment is read through the observer;
  - what is compared (`static_group_verdict`,
    `verdict_of_a_static_group`, `outcome_of_a_static_group`,
    `static_groups`): that the constant at which Simplify stops is
    the last of the first prefix on which it stops; that the
    environments are compared after the constants before it, or
    after the group, first and on every path, what the model itself
    sees and what the compiler sees both being read; that
    a difference is recorded under T3-10 only as the comment at
    `static_group_in_the_model` says, the model being made to give
    the symbol of a boxed number whose contents are a variable of
    kind value the type that its environment has for the variable;
    that a stop at a constant to which the model gives a type is
    recorded under T3-10 only where the constant is a boxed number
    of the variable that holds a naked float and that comparison
    passes;
    that `why_untyped` tells by the text of a block, and by the
    symbols bound before it, whether it names a symbol that is not
    defined or has a field that is a naked immediate;
  - `control_of_the_static_groups`: that its groups are what its
    lines say, and that where a line says so one side of a verdict
    is put there by hand.
  - what is seen, as text (`print_seen`, with
    `Model_type.normalise_by`): that the variables numbered above
    the threshold are named in the order in which a first text
    comes to them, and that the text answered has the sets of names
    and the maps keyed by names in the order of those names, and
    the lines of those variables in that order; that
    `normalise_by` differs from `normalise` only in the order of
    the variables;
  - the names to avoid (`names_for_a_join_to_avoid`, and `made` in
    `sides_of_joins`): that a join of the model is told to avoid
    the variables of the test, those that its source and its uses
    know and, in the joins after joins, those of the targets of
    every join run before it;
  - the joins after joins (`joined_step`, `run_joined_steps`,
    `sides_of_joins`): that the two sides run the same steps, a
    definition at the normal name mode, one scope further, an
    equation added by `add_equation` with the n-way meet, and a
    join after the scope of the environment so far of the
    environments that the lists of steps make from it, the uses
    numbered by their positions; that what is looked at is what is
    seen of the variables of the program;
  - the three joins of the shape of T5-10
    (`joins_of_the_shape_of_t5_10`): that its steps are those of
    `Recovered` of FlambdaJoinMeetExamplesSpec.v as that file was
    when it was written;
  - the generated programs (`generate_joined_steps`,
    `generated_joins_after_joins`): that the generator is what the
    comment at its definition says; that a difference of the model
    with the repaired test is recorded under T5-10 only where the
    model with the compiler's test sees what the compiler sees at
    every place looked at, and both sides of the run with the
    repaired test are read at every place
    (`outcome_of_the_repaired_test`);
  - the two controls (`control_of_the_names_to_avoid`,
    `control_of_the_repaired_test`): that their programs are those
    that the generator makes from the seeds named, and that where a
    line says so a reading of a run is replaced by hand
    (`with_a_reading_replaced`); that the model and the compiler
    are said to be told apart by a run only where both answer and
    every place looked at is read on both sides
    (`told_apart_where_read`).
  - the types kept in `.cmx` files (`environment_of_cmx`,
    `check_cmx`, in `types_of_compilations.ml`): that a file is
    loaded by the compiler's own loader and resolver
    (`Flambda_cmx.create_loader`, `load_cmx_file_contents`), the
    directory given being the whole load path and the current unit
    another one; that the environment is the one that
    `Typing_env.create` makes with that resolver, read through the
    observer; that the names asked are the symbols and the
    variables that `Serializable.ids_for_export` gives and whose
    compilation unit is the unit, a symbol at the kind of values
    and a variable at its own kind; that the units are those of
    the `.cmx` files of the directory, each named as its file with
    the first letter in upper case;
  - the rule of the test: that the directory is the one in which
    the compiler of the context `main` finds the standard library,
    and that the files there are those that the build of this tree
    made with its own compiler;
  - `check_environments`: that it does what `check_file` did for
    the environments of a file (the expected file of that test did
    not change);
  - `top_of_a_type`: that what is counted is the constructor at the
    top of the model's type, and for a head whether it may be null
    and whether it then has a variable;
  - the control (`control_of_the_tops`, and the rules of the
    directory `cmx_control`): that the four types are those that its
    lines say; that the three files are made as the rules say, by
    the compiler of the context, the second with `-opaque`, and the
    third by writing a line of text.
  - the meet of T7-13 (`the_meet_of_t7_13`,
    `run_the_meet_of_t7_13`, `the_meet_of_t7_13_in_every_order`):
    that the scenario is what the comment at its definition says,
    with the number of fields of the last block a parameter; that
    each run makes new variables, and that the order given is that
    of `Variable.compare` on the three of that run, taken when the
    scenario tells them, before its first step (`?made` of
    `scenario`); that the
    compiler's check is the flag
    `Oxcaml_flags.Flambda2.Debug.concrete_types_only_on_canonicals`,
    set for the runs that say so and put back; that a run is read
    as refused by the check where the compiler stops with a fatal
    error whose first words are those of
    `Typing_env.replace_equation`; that `v2` is said to have a type
    that is no alias and `v1` for its canonical element by
    `Typing_env.find` and `get_canonical_simple_exn` on the
    environment answered.

Not trusted, though it is OCaml: what the tool proposes to
`validate_unit` and to `validate_unit_knowing`. Each proposal is
checked by an extracted function, and `validate_unit_sound` and
`validate_unit_knowing_sound` hold whatever is proposed.
- Which static bindings to remove as unused (`unused_statics`): checked
  by `drop_statics`.
- Which `Let`s Simplify made static bindings, under which symbols, and
  in which code `my_closure` is a symbol (`lifting_guess`, once for
  each lifting of the list): the `Let`s outside code and the code ids
  are checked by `lift_unit`; the `Let`s in the bodies of code (the
  field `lifted_out_of_code` of the guess, which `lift_unit` does not
  read) by `lift_from_code_unit`; the `Let`s of the handlers that are
  not at toplevel, to bind at the head of the unit (the field
  `lifted_to_head`), by `lift_to_head_unit`.
- Which value slots Simplify removed from the static sets of closures
  (`unused_slots_guess`): checked by `drop_unused_slots`.
- Which code Simplify made a loop of, with a name for the loop of each
  (`loopify_guess`: the code that the front end marks for loopify, as
  the conversion notes it): checked by `loopify_unit`, which leaves
  alone the code that is not `loopable` with the name given.

The guesses are made from the two terms as `convert_both` gives them,
or from what extracted functions of the validation make of them, which
the tool computes again for the purpose: the term before with its loops
made, normalised, with the liftings made so far, and with its
continuations placed and tidied; the term after normalised; and for
`validate_unit_knowing` the same of the two terms normalised by
`normalise_knowing`. A symbol or a code id taken from the term after is
used in a guess with the number assigned by the conversion above. That
identification of names is trusted, as said there; a guess adds nothing
to it.

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
