# Decisions and discrepancies: an index of the labels

The comments and documents of the Rocq model of Flambda 2 cite decisions
as `D<n>` (in a `CR`: "Decision D<n>") and discrepancies between the
model and the compiler by the stream that found them and a number
(`T1-4`). This file says in a line or two what each label stands for.
It is an index and not the record: a decision's state here is its state
when the line was last touched.

"Ruled" is a ruling of the human in charge; "decided" is a choice made
for the proof that the human may overrule; "open" is still the human's
to decide, and the model then takes the conservative choice named, with
a `CR` at the place in the `Spec` file.

## Decisions

- **D1.** What an exit observes of a closure. Meanwhile the whole value:
  its function slot, the code ids of its set, the values of its value
  slots. Open.
- **D2.** Identity of closures. Meanwhile none: two closures are the
  same when their contents are. Open; goes with the heap.
- **D3.** A projection that names a function slot other than the
  closure's own is undefined. Ruled (as probably right).
- **D4.** How a static set of closures is kept consistent. The model
  asks, as a condition of well-formedness, that one group binds a set
  whole, each symbol at its slot. Open.
- **D5.** On which values `Is_int` and `Get_tag` have a value: `Is_int`
  of a variant on tagged immediates and blocks, `Get_tag` on blocks.
  Ruled for `Get_tag` (no value on an immediate); `Is_int` outside its
  domain is open.
- **D6.** Whether a block made by `Make_block` and a symbol bound to an
  equal static block are the same at an exit. Open; goes with the heap.
- **D7.** How a heap enters the statements, which build states field by
  field. Open; part of the design of the heap.
- **D8.** An operation on a symbol that is not bound is undefined, and
  well-formedness rules such terms out. Ruled. What `Is_null` and the
  other primitives are on poison is open; they have no value.
- **D9.** A call whose arities are not those of the code called is
  undefined. Ruled.
- **D10.** A mismatch of kinds is undefined where it is executed. Ruled
  for calls and primitives. Where a value of another kind is bound by
  a `Let` or a handler, or put in a block field or a value slot, the
  machine does not test yet. Open in that part.
- **D11.** The validator does not run the check of kinds; the test tool
  prints the check's answer and goes on. Decided.
- **D12.** A static check of kinds may refuse only what the compiler
  refuses with its default flags, and no statement takes such a check
  as a premise about the compiler's terms. Ruled.
- **D13.** Integer constants are in range for their kind: a condition
  of well-formedness. Ruled.
- **D14.** Division by zero is undefined; the least integer divided by
  -1 wraps. Taken from the compiler; open to objection.
- **D15.** A `Block_load` that fails the checks of size, tag or
  `Immediate` has no value. Open.
- **D16.** A primitive given an argument of another kind has no value.
  Ruled, with D10.
- **D17.** The target has 64 bits. Open.
- **D18.** A shift by an amount outside `[0, width)` has no value. Open.
- **D19.** `Phys_equal` has no value on two allocated values. Open;
  goes with the heap.
- **D20.** Closures that no compiler term makes (a closure at a
  function slot that its set has not got, and the like): the model
  leaves them to well-formedness and gives the machine no step on
  them. Open.
- **D21.** A boxed number whose contents are poison is a boxed number
  and is allocated; boxing and unboxing poison have no value. Open.
- **D22.** A caution, not a question: "no value" removes a case from
  what refinement has to prove. It is conservative about results, not
  about how much of the compiler's correctness is established.
- **D23.** `Make_block` keeps an integer tag and the machine does not
  test it; tags in `[0, 251)` are a condition of well-formedness.
  Decided.
- **D24.** Blocks with no fields are allowed. Ruled.
- **D25.** What the kind of a `Make_block` field promises. The
  conversion refuses annotated blocks meanwhile. Open; goes with kinds.
- **D26.** Types of names that hold poison. Typing facts are about
  values that are not poison; an environment asks nothing of the type
  of a name whose value is poison; an `Is_int` or `Get_tag` relation
  is never true of a scrutinee that is poison; `Is_null` relates
  poison to 0; aliases are exact, poison included. Decided.
- **D27.** The meet and join transcribed first are those of
  `types/meet_and_n_way_join.ml` (the n-way join). Ruled.
- **D28.** The functions of a set of closures have distinct code ids,
  and so have the sets bound in one static binding group. Ruled.
- **D29.** The renaming action reaches into code, and is defined on
  everything that holds names. Ruled.
- **D30.** The model ignores physical equality (`==`) in the compiler.
  Where `==` changes a result, the behaviour transcribed is the
  structural one. Ruled.
- **D31.** Code is closed but for symbols, code ids and slots; its
  parameters, `my_closure` and its return and exception continuations
  are binders. A condition of well-formedness. Ruled.
- **D32.** The model's well-formedness may be stricter than what the
  compiler checks where the condition ought to be an invariant, with a
  comment at the condition; not for kinds. Ruled.
- **D33.** Access to the types library for tests: accessors on
  `Block_size`, and a way for a test to observe the typing
  environments of Simplify, without opening the abstraction of
  `Flambda2_types.t`. Ruled in part; the design of the observer is
  open.
- **D34.** Whether `structural` becomes the default of
  `-flambda2-join-sharing`. Open.
- **D35.** Whether `Coercion.change_depth` compares its arguments with
  `Rec_info_expr.equal` in place of `==`. Open.
- **D36.** The model's equality of types is coarser than the
  compiler's structural one (depth information, the string of a
  poison, relation entries bound to no name); the correspondence is
  stated only on types that do not differ there. Decided.
- **D37.** Regions and local allocations. Proposed: the conversion
  drops regions and reads a local allocation as an ordinary one.
  Open.
- **D38.** `Boolean_not` of a tagged immediate other than 0 and 1 is
  undefined. Simplify makes it `Invalid` where the argument cannot be 0
  or 1, the backend flips the low bit of any integer, and nothing checks
  that the front end gives it a boolean. Decided overnight, for the
  review of the human; forced by the `Invalid` of Simplify.
- **D39.** The freshness quantifier of nominal sets is a derived layer;
  the explicit forms stay primary. Decided.

## Discrepancies with the compiler

A label is the stream that recorded the entry and a number. An entry
says where the compiler is silent, imprecise or inconsistent, or where
the model and the compiler part; it is not a claim of a bug unless it
says so. Only the labels that this tree cites are listed.

- **C0-1.** Simplify gives every new version of a piece of code a new
  code id, and closures carry it out of the unit.
- **C0-3.** Simplify refuses a `Let` that binds symbols away from the
  toplevel of the unit, but not one that binds only code; the model
  refuses both.
- **C0-4.** Nothing checks that a symbol or a code id is bound only once
  in a unit.
- **C0-5.** Code is checked to be closed against the free names its
  creator supplies.
- **C1-1.** Simplify replaces an integer division or remainder by zero
  with `Invalid`.
- **C1-2.** The least integer divided by -1 wraps to itself, and its
  remainder is 0.
- **C1-3.** Simplify replaces a primitive applied to an argument of
  another kind with `Invalid`.
- **C1-4.** Simplify takes the argument of a variant-only `Is_int` to be
  a variant that is not null; the machine computes the low bit of
  anything.
- **C1-5.** Simplify folds `Is_null` of a poison constant to 0 and
  `Is_int` of one to 1; the backend makes poison a tagged immediate.
- **C1-6.** Simplify replaces `Get_tag` of null or of a boxed number
  with `Invalid`, and leaves `Get_tag` of a tagged immediate alone.
- **C1-7.** Simplify uses the tag of a `Block_load`'s access kind only
  when it does not already know the field, and never its size.
- **C1-8.** Simplify turns a block made by `Make_block`, or a boxed
  number, into a static symbol; in the model the two are different
  values.
- **C1-9.** Simplify folds an arithmetic shift right by 63 of a negative
  naked immediate to 0, and of a tagged immediate to -1.
- **C1-10.** fexpr reads `%is_int` as the variant-only `Is_int`, and
  prints the other one the same way.
- **C1-11.** fexpr cannot write an integer constant beyond 63 bits, and
  wraps an out-of-range `int8` or `int16` literal without a word.
- **C1-12.** A constant of the model holds any integer; the compiler's
  constants are in the range of their kind by construction.
- **C1-13.** The kinds of the fields of a `Make_block` come from the
  types of the source, are used by Simplify for variables only, and are
  ignored by the backend.
- **C2-1.** Simplify replaces by `Invalid` a call made at arities that
  are not those of the code called.
- **C2-2.** With the default flags Simplify accepts ill-kinded code and
  makes it `Invalid`; a well-typed program with a GADT indexed at layout
  `any` needs that.
- **C2-3.** Simplify replaces by `Invalid` a call whose argument is not
  of the kind that the arity of the call itself gives; the machine runs
  it.
- **C2-4.** Some mismatches of kinds stop Simplify with a fatal error
  whatever the flags, while others of the same sort become `Invalid`.
- **C2-5.** The fexpr parser gives a direct call, and an indirect call
  with no annotation, the arity in which every argument and result is a
  `Value`; the printer leaves the arity of such calls out.
- **C2-6.** Nothing checks that the arities in a code's metadata are the
  kinds of its parameters.
- **C2-7.** A call with fewer or more arguments than the code has
  parameters is undefined in the model; in the compiler it is a partial
  application or an over-application.
- **C2-8.** Two array primitives treat an array of another kind than
  their own differently, and neither becomes `Invalid`.
- **C2-9.** An indirect call of a tupled function is made at one
  argument, the tuple, whatever the arity of the code; the model has no
  such mark on code.
- **C3-1.** Simplify answers a projection that names the wrong function
  slot on one of its two paths and makes it `Invalid` on the other; the
  slot named is not checked where the term is built.
- **C3-2.** `to_jsir` translates both projections from the environment
  of the function being translated, whatever closure they are applied
  to.
- **C3-3.** Simplify simplifies the body of each function of a set
  knowing that `my_closure` is that closure of that very set.
- **C3-4.** The number of variables bound by a `Let` of a set of
  closures is not checked against the number of its functions where the
  `Let` is built.
- **C3-5.** A set of closures in which a function slot is given twice is
  built without complaint, and Simplify then fails on an unrelated
  assertion.
- **C3-6.** The compiler binds the symbols of a static set with one
  pattern; the model binds each with a binding of its own and has to
  check that they agree.
- **C3-7.** The model can write a closure at a function slot that its
  set has not got; the compiler cannot.
- **C3-8.** The model can write a set of closures in which a value slot
  is given twice; the compiler cannot, and the fexpr parser accepts one
  and keeps the second value.
- **C4-1.** Simplify lifts an `Immutable_unique` block out of a function
  to one symbol.
- **C4-2.** Nothing checks that a field loaded as immutable is never
  written.
- **C4-3.** A comment says that physical equality is referential on
  immutable blocks; CSE and sharing do not keep it.
- **C4-4.** The copy of a large record stores, with `Assignment`, into
  fields that are then read as immutable.
- **C5-1.** Nothing in Flambda 2 checks that trap actions, raises and
  calls name the handler that is installed last; the backend goes by the
  stack and Simplify by the names.
- **C5-2.** `Apply_cont_expr.is_raise` and the backend disagree on which
  `Apply_cont` is a raise.
- **C5-3.** A `Pop` with no raise kind is "the same as No_trace" for the
  backend and is treated as a regular raise by Simplify.
- **C5-4.** With debugging information on, Simplify does not turn a
  regular raise or a reraise into a jump.
- **C5-5.** A call can give extra arguments to the exception
  continuation of its code or of the unit, which takes the exception
  alone; in the model a way out of a term takes any number of values.
- **C5-6.** Fexpr drops the extra arguments of a call whose exception
  continuation is `error`, without a word.
- **C5-7.** Nothing tests that the first parameter of an exception
  handler is of kind value.
- **C5-8.** Nothing checks that a continuation used as an exception
  handler is marked `is_exn_handler`, nor that a marked one is not the
  return continuation of a call.
- **C5-9.** `to_cmm` stops on a trap action of a jump that names the
  exception continuation of the function or of the unit.
- **N1-1.** `Compare` writes the reverse maps of function slots and
  value slots into the forward maps.
- **N1-2.** `pattern_match_pair` on code and on recursive handlers stops
  the compiler where the lists of bound names differ in length.
- **N1-3.** That the names of a binder are distinct is checked for
  continuations always, and for parameters only with invariant checks
  on.
- **N1-4.** That code is closed is a claim of whoever creates it,
  checked only for the form of the claim.
- **N1-5.** A static pattern is in a name abstraction, is never renamed,
  and is subtracted from the free names.
- **N1-6.** Existential variables of an environment extension, and the
  variables a level defines, are binders that the nominal interface does
  not see.
- **N1-7.** Some of Simplify's output depends on the order of names.
- **N1-8.** A renaming with an import map is not a permutation, and
  renamings do not compose in general.
- **N1-9.** The comparison of terms of the compiler (`Compare`) has no
  case for a primitive of four arguments, so it judges a term that has
  one different from itself.
- **P1-1.** Simplify folds `Phys_equal` of a poison against another
  constant to 0, and the backend makes a poison of kind `Value` a tagged
  immediate.
- **P1-2.** Simplify makes `Boolean_not` of a tagged immediate other
  than 0 and 1 `Invalid`; the backend flips a bit of whatever it is
  given.
- **P1-3.** Outside the amounts it computes, Simplify folds a shift to
  zero while calling it undefined, and the backend shifts by the amount
  modulo 64.
- **P1-4.** The fexpr parser reads `%bytes_length` as `String_length
  String`, and the printer writes `String_length Bytes` as
  `%bytes_length`.
- **R1-1.** Unboxing records `Get_tag` on the paths where the value is
  an immediate, and supplies a dummy tag of zero.
- **R1-2.** The types library evaluates `Is_null` of poison as false.
- **R1-3.** The field annotations of `Make_block` constrain variables in
  Simplify, and the model does not keep them.
- **R1-4.** The metadata of a `Block_load` is not checked uniformly by
  Simplify or by code generation.
- **R1-5.** `Get_tag` of a boxed value is lowered to a read of the tag,
  but Simplify can discard it.
- **R1-6.** The old test converter merged the least tagged immediate
  with minus one.
- **R1-7.** A block with no fields that is made at run time has to be
  lifted before the backend.
- **R1-8.** The model accepts block tags outside the compiler's
  scannable range.
- **R1-9.** `Tag.Non_scannable.of_tag` uses the test of the scannable
  range.
- **R1-10.** The comment on the modulus in `One_bit_fewer` disagrees
  with its implementation.
- **R1-11.** What is observed of a boxed number that holds poison
  differs between the types (T1) and the primitives (C1).
- **R1-12.** The conversion of static constants discards the shape of a
  mixed block.
- **R1-15.** The n-way join drops a conditional extension of a variant
  that the binary join keeps.
- **R1-16.** The n-way join of immediates gives an empty set to
  `create_naked_immediates_non_empty` when every head reduces to bottom;
  traced, not shown reachable.
- **R1-22.** Nothing checks that a trap action does not name the return
  continuation of the unit: `to_cmm` gives that continuation a handler
  of its own and lets such a trap action through, where for the return
  continuation of a function it fails.
- **R2-3.** A static set of closures may be empty; a set bound by a
  `Let` may not.
- **R2-7.** Simplify fails on a set of closures in which two function
  slots share one code id.
- **R2-9.** The number of variables that a `Let` of a set of closures
  binds is checked only by later consumers of the lists.
- **R2-11.** Simplify removes a dead use of a continuation at the wrong
  kind before checking it.
- **R2-12.** Printing a term as fexpr and parsing it back loses the
  arities of calls.
- **R2-15.** Sharing code between static sets succeeds in separate
  groups but fails within one group.
- **R2-16.** The checks for duplicate parameters compare the whole
  parameter, not only its variable.
- **R2-17.** A recursive group of continuations must be non-empty in the
  compiler; the model can write an empty one.
- **R2-18.** Tail-modulo-cons initialises blocks made `Mutable` that are
  later read as immutable lists.
- **R2-19.** An `Immutable_unique` block is lifted also where the
  function binds an allocation region.
- **R2-20.** A load marked immutable is reused across a write to the
  same field.
- **R2-21.** Sharing immutable allocations changes the result of a raw
  physical comparison.
- **R3-2.** The reverse reduction of `Get_tag` discards the possibility
  of an immediate.
- **R3-7.** The n-way join can say what the code of a closure is when
  one of its inputs does not (with T1-4).
- **R3-15.** In the model, the immediates of a type include raw integers
  that are out of range for the compiler.
- **T1-1.** After unboxing, the compiler's own types say that the
  arguments passed for a constant constructor are impossible (the
  `Get_tag` reduction of meet).
- **T1-2.** The compiler reads `Is_int` of a constant in two ways, and
  both are wider than what `Meet` deduces from the relation.
- **T1-3.** Unboxing gives types and relations to parameters that hold
  poison.
- **T1-4.** The n-way join of two closure types can name a code that one
  of them does not (the two implementations of join disagree on function
  types).
- **T1-5.** What the creation functions and raw constructors of types
  leave unchecked.
- **T1-6.** The model's grammar of types has a boxed number of every
  naked number kind.
- **T1-7.** More that the operations on types rely on and nothing
  checks: an exact set of closures has a function type for each closure;
  a set of strings is not empty; the kind of an alias to a constant.
- **T1-8.** The `Get_tag` reduction of meet takes a number that is no
  tag to be the tag of no block, and the machine has blocks of any tag.
- **T1-9.** A prover reads `Is_null` of a name of type `Null` as 1, and
  the relation of the model gives 0 when that name holds poison.
- **T1-10.** The type that a projection of a value slot gives its
  closure has an index with no function slot, so the fast path of the
  next projection never answers on it.
- **T2-1.** `Typing_env.replace_equation` on a name that is not bound
  records an equation that the environment cannot see.
- **T2-2.** The invariants of the typing environment are checked only
  when invariant checks are on, and one is not checked at all.
- **T2-3.** `Typing_env.find` in an environment that is bottom answers
  bottom for every name but a symbol with no equation.
- **T2-4.** A level drops an equation whose type is unknown, so `cut`
  can answer an older equation than the type the environment has.
- **T2-5.** After lifting, the environment speaks of a symbol that no
  run of the term as it was has bound.
- **T2-6.** The n-way join gives the handler a variable that only some
  uses define, with its type from those uses; on a run through another
  use nothing has that type.
- **T2-7.** Nothing checks that the names given to
  `Typing_env.add_alias` are bound, and the aliases take an unbound
  variable for one of another compilation unit.
- **T2-8.** `Typing_env.replace_equation` gives a variable a type of any
  kind; only its callers in `Meet_env` keep the kind that the variable
  was defined with.
- **T3-1.** Ordering two variables of the unit being compiled that have
  one binding time is a fatal error in the compiler's resolver; the
  model's resolver is total, and the typing environment's invariant asks
  for distinct binding times.
- **T3-2.** `Aliases.add` on two symbols demotes the first, and the
  result fails the compiler's own `invariant` (run with heavy checks
  only); the model follows `add` and proves the failure.
- **T3-3.** The compiler's `Aliases.invariant` never reads
  `canonical_elements` and never checks the name mode recorded for an
  alias; the model asks for both and proves that `add` keeps them.
- **T3-4.** `Alias_set.choose_opt` answers `None` for a set that has a
  constant and names (dead code; not modelled).
- **T3-5.** The order on name modes is total, and `aliases.ml` treats it
  as partial.
- **T3-6.** Asked for a `Phantom` name, `get_canonical_element_exn`
  prefers a `Phantom` alias to an earlier `Normal` one.
- **T3-7.** `find_best` and the tie in `find_earliest_alias` depend on
  the order of names; the model takes the first of a list.
- **T3-8.** The extra variables of an extension with extra variables are
  not a binding site in the compiler: `With_extra_variables.free_names`
  lists them and `apply_renaming` renames them.
- **T3-9.** `Aliases.add_alias_set` stops with a fatal error where two
  different constants come into one class; in the model that is `None`,
  proved absent when some environment respects the structure and gives
  the elements of the set the value of the name. Not reproduced from
  source.
- **T4-1.** After the n-way join, the meet defines a second time the
  variables that the join imported from a branch.
- **T4-2.** A meet that reads the type of a name holding poison can
  answer bottom, or add a false alias, with every other premise true.
- **T4-3.** The meet answers bottom for two function types of one slot
  with different code, also where the index does not say that the set
  has the slot.
- **T4-4.** The meet of code ids in the model has no relation of code
  age.
- **T4-5.** The meet deduces a type of blocks or of immediates for a
  scrutinee from a relation, also where the scrutinee holds poison.
- **T4-6.** The reduction from a `Get_tag` relation drops the numbers
  that are not tags of blocks.
- **T4-7.** `expand_head` answers the type of a constant for an alias
  whose canonical element is a constant, whatever the kind of the alias.
- **T4-8.** `is_int_for_scrutinee` says 1 for every constant scrutinee,
  `Null` included, and `Relation.of_const` says 0 for `Null`.
- **T4-9.** `meet_row_like`, where it keeps one case only, does not
  define in its result the variables that the meet of that case defined.
- **T4-10.** `add_concrete_equation_on_canonical_name` takes the name to
  be canonical after the meet that it runs in between.
- **T4-11.** In the model, `Typing_env.add_equations_on_params` may give
  a later parameter that the environment does not know a variable that
  the join made; whether the compiler can is not settled.
- **T5-1.** The assumption stated by the n-way join, that every name of
  the source is defined in every joined environment, is false of its
  callers, and nothing checks it.
- **T5-2.** The assumption that every symbol of a joined environment is
  defined in the source is checked of a set passed beside the
  environments, not of the environments.
- **T5-3.** The assumption that the binding times of the variables of
  the source are coherent across the joined environments is not checked.
- **T5-4.** The environment of a handler holds the types of constants
  lifted in other branches, which are not true on a path that did not
  define the symbol.
- **T5-5.** The n-way join gives a variable that only some uses define
  the join of its types at those uses, and nothing records that it means
  nothing at the others.
- **T5-6.** The results of the n-way join depend on the order of names.
- **T5-7.** A join through a name that holds poison is not an upper
  bound.
- **T5-8.** `Analysis.fold_variables_created_at_join` also visits
  variables that the join did not create.
- **T5-9.** The n-way join makes a variable of a kind for simples whose
  kinds it does not look at.
- **T5-10.** The n-way join takes every variable that a joined
  environment knows to have a value there, where it puts a relation back
  on a scrutinee and where it drops a bottom type.
- **T5b-1.** The join of types has no bound on its depth that is always
  reached; on two inputs that are an alias and a type in turn, both the
  n-way join and the binary join overflow the stack.
- **T5b-2.** The n-way join gives an `is_null` variable to a join one of
  whose inputs is not null, and so says that `Is_null` of each value of
  that input is 0, poison included.
- **T5b-3.** The n-way join of types takes what `Expand_head` answers to
  be of the kind of the types joined, and nothing gives it that.
- **T6-1.** A prover answers what the environment says of a name, which
  is not true of a name that holds poison (one case reaches a number
  that is not poison).
- **T6-2.** The grammar of the model has a type of naked numbers at the
  kind of the immediates, of which four provers answer that it has no
  value.
- **T6-4.** A value slot of the model has no kind;
  `meet_project_value_slot_simple` answers `Invalid` where the type of
  the slot is of another kind than that of the slot.
- **T7-1.** No function of the compiler makes the allocation mode
  `Local` of a type; the converter of types refuses it.
- **T7-2.** `Equal_types_for_debug.equal_type` overflows the stack on a
  type and itself when an extension on a name gives it a type with an
  extension on that name; the tests do not call it on such types.
- **T7-3.** The binary and the n-way join of two types keep different
  things (aliases, relations, extensions); neither is always the more
  precise.
- **T7-4.** The meet of a type with an `is_null` variable and a type
  that settles it forgets the variable.
- **T7-5.** The meet of a variant with a mutable block keeps the
  immediates. A loss of precision.
- **T7-6.** A meet forgets an inverse relation of a naked immediate. A
  loss of precision.
- **T7-7.** With the default setting of `-flambda2-join-sharing`, a join
  depends on whether equal types, or parts of them, are one value in
  memory; with the structural setting it does not.
- **V2-2.** The fexpr printer drops the kinds of the fields of a
  `Make_block`, and the parser reads back `any_value` for each.
- **V3-2.** Simplify lifts a closed constant out of a function or a
  loop, and shares equal constants: the number of allocations changes.
- **X3-5.** The n-way join of two variants that carry only a relation
  answers unknown and drops the relation it has just joined.
- **X4-1.** The output of Simplify binds the same variable in two
  places: the names stored in a term are not unique.
- **X5-2.** The fields of a recursive module are read by immutable
  loads, and `CamlinternalMod.update_mod` overwrites them; a read from
  before the write is reused after it.
- **X5-3.** A load from a string has no coeffect,
  `Bytes.unsafe_to_string` is erased, and `to_cmm` moves the load after
  a write to the bytes.
