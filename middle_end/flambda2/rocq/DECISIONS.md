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
- **C2-6.** Nothing checks that the arities in a code's metadata are the
  kinds of its parameters.
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
- **R2-3.** A static set of closures may be empty; a set bound by a
  `Let` may not.
- **R2-7.** Simplify fails on a set of closures in which two function
  slots share one code id.
- **R2-9.** The number of variables that a `Let` of a set of closures
  binds is checked only by later consumers of the lists.
- **R2-11.** Simplify removes a dead use of a continuation at the wrong
  kind before checking it.
- **R2-15.** Sharing code between static sets succeeds in separate
  groups but fails within one group.
- **R2-16.** The checks for duplicate parameters compare the whole
  parameter, not only its variable.
- **R2-17.** A recursive group of continuations must be non-empty in the
  compiler; the model can write an empty one.
- **R3-2.** The reverse reduction of `Get_tag` discards the possibility
  of an immediate.
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
