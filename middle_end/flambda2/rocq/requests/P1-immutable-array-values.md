# P1: an immutable array made when the program runs

For the source `[: 1; 2; 3 :]`, which is a `Make_array` marked
`Immutable` in the term that the compiler gives to Simplify.

For the human, C0 (the values), C4 (the heap), V3 (the lifting), V2
(the conversion and the corpus), and the reviewers R5 (the
primitives), R1 (what is trusted, and how the statements reached are
classed) and R3 (the boundary with the lifting).

Nothing of it is in this tree: no definition, no proof, no
conversion. The definitions of section 3 were written and compiled,
with no proof, to find every definition that changes and what it
reaches (section 5). The measure of section 7 was made with an edit
of the test tool that is not the conversion. The series comes after
this request is approved.

## 1. Why

The model has the immutable array of values as static data: what a
symbol is bound to (`Static_immutable_array`), read by `array_of`,
with `Array_length` and `Array_load` on it. It has no immutable
array that is made when the program runs: "There is no value that is
an immutable array, only a symbol bound to one: no primitive of the
model makes one" (`FlambdaValueSpec.v`).

The term that the compiler gives to Simplify makes one wherever the
source has an immutable array literal of at least one element.
Simplify then lifts most of them to the static constant. So the
conversion of the test tool refuses the term before, and nothing is
run or compared: not even the two runs.

Measured on 68 units written to try arrays (not in this tree), with
the test tool of the tree that has the static arrays: 46 are not
checked for this reason and no other. Six units of another set,
written to try immutable arrays, stop at the same primitive.

## 2. What the compiler makes

Read for this request; each place is named.

**The front end.**

- `lambda/translcore.ml`, the case `Texp_array`. An array literal is
  `Pmakearray (kind, mutability, mode)` of its elements. An
  immutable literal is made `Immutable`. A mutable literal of more
  than four elements
  (`use_dup_for_constant_mutable_arrays_bigger_than`), all of them
  constants, not allocated locally, is for this middle end
  `Pduparray (kind, Mutable)` of a `Pmakearray (kind, Immutable, _)`
  of them: an immutable array made, and then copied. The kind is
  chosen from the type of the elements; I did not read the choice.
- `from_lambda/closure_conversion.ml`, `close_primitive`. A
  `Pmakearray` of no element, mutable or not, is not a primitive: it
  is the static constant `Static_const.empty_array` of its kind,
  registered once for the unit (`register_const0`, which gives two
  equal constants one symbol where `Static_const.can_share` allows).
- `from_lambda/lambda_to_flambda_primitives.ml`, the case
  `Pmakearray`. With elements it is
  `Variadic (Make_array (array_kind, mutability, alloc_mode), args)`.
  The array kind (`convert_array_kind`): `Immediates` for
  `Pintarray`, `Values` for `Paddrarray`, `Gc_ignorable_values` for
  `Pgcignorableaddrarray`; `Naked_floats` for `Pfloatarray`, with
  each element unboxed; for `Pgenarray`, a test of the first element
  (`Is_boxed_float`) between a `Make_array` at `Naked_floats` and
  one at `Values`; and the kinds of naked numbers and of unboxed
  products for the arrays of unboxed elements.
- The same file, the case `Pduparray`: `Duplicate_array` with the
  mutability of the source `Immutable` and that of the destination
  as the source says.
- `from_lambda/lambda_to_lambda_transforms.ml`: `%array_to_iarray`
  and `%array_of_iarray` are the identity. So an array that a
  program reads as immutable may be a mutable array, the same
  object.

**What runs.** An object that holds the elements, never written by
a program that does not cast. Nothing in the compiler keeps which
allocation it is:

- `Flambda_primitive.variadic_primitive_eligible_for_cse` says yes
  of `Make_array (_, Immutable, Heap _)` with an argument that is a
  variable, as of `Make_block`: two of them with the same arguments
  become one.
- Simplify lifts it to a static constant, out of a function or a
  loop too, and gives two equal constants one symbol (below).

**Simplify.**

- `simplify/simplify_variadic_primitive.ml`, `simplify_make_array`.
  The type of each argument is met with the kind of the elements
  (with its subkind), and the primitive is `Invalid` where they
  cannot agree. `Immutable_unique` is a fatal error. The variable
  gets the type `T.immutable_array` of the types of the arguments
  for `Immutable`, and `T.mutable_array` of the kind and the length
  for `Mutable`; and reification is asked for (`try_reify`).
- `simplify/simplify_named.ml`: lifting is allowed where the
  primitive has only generative effects and the variable is bound
  at normal name mode (`allow_lifting`). A `Make_array` has only
  generative effects whatever its mutability
  (`effects_and_coeffects_of_variadic_primitive`); what keeps a
  mutable array from being lifted is its type.
- `types/reify.ml`, `reify`, on the type of an array:
  - immutable, of no field: `Lift (Empty_array kind)`, where the
    kind of the elements is known;
  - immutable, elements of kind `Value`:
    `Lift (Immutable_value_array {fields})` where
    `try_to_reify_fields` gives a `Simple` for every field, as for
    an immutable block. The type of the field is proved equal to a
    constant, a symbol or a variable, with no coercion; and a
    variable is allowed only if it is in the typing environment and
    is known to be a projection from a symbol, or is defined at the
    toplevel of the unit and, unless the array is allocated on the
    heap, proved never to hold a locally allocated value
    (`var_allowed`);
  - immutable, elements that are naked numbers, floats among them:
    lifted where every field is one known number
    (`Immutable_float_array`, `Immutable_int_array` and the
    others);
  - mutable, or of contents not known: lifted only where the length
    is known to be 0, to `Empty_array`.
- `simplify/lifting/reification.ml`: `create_static_const` makes the
  constant, and `lift` binds it to a new symbol named after the
  variable, or takes the symbol of an equal constant that the unit
  has already (`DA.find_shareable_constant`;
  `Static_const.can_share` says yes of `Immutable_value_array` and
  of `Empty_array`, where the constant mentions no variable). The
  variable becomes an alias of the symbol.

So, for an immutable literal of values bound at normal name mode,
this is what I read of when the `Let` is not made a symbol. It is
not a statement of exactly when: the conditions are on the types
that Simplify has, and on the `Simple` that each field is proved
equal to, which need not be the argument of the `Make_array`.

- A field is proved equal to no `Simple`, or to one with a coercion
  that is not the identity (`try_to_reify_fields`).
- A field is proved equal to a variable that is not allowed
  (`var_allowed`). A variable is allowed where it is in the typing
  environment at normal name mode and, either it is known to be a
  projection from a symbol, or it is defined at the toplevel of the
  unit and the array is allocated on the heap or the variable is
  proved never to hold a locally allocated value. So a parameter of
  a function, and a variable bound in the body of a function, in
  the handler of a recursive continuation or in an exception
  handler, are not allowed unless they are projections from a
  symbol (`Downwards_env.is_defined_at_toplevel`;
  `simplify/simplify_let_cont_expr.ml` is where a handler is said
  not to be at toplevel); and a projection from a symbol is allowed
  in a local array with no proof.
- The variable is bound at a name mode that is not normal.

Where reification does not lift, the `Let` keeps its `Make_array`,
or becomes the canonical `Simple` of the type of its variable where
there is one (`try_canonical_simple`). A literal whose elements are
constants and symbols is lifted wherever it is, in a function or a
loop too, unless its variable is the alias of a symbol already.

**The reads.**

- `simplify/simplify_binary_primitive.ml`, `simplify_array_load`.
  Where the type of the array is proved to be that of an immutable
  array of known fields (`T.prove_is_immutable_array`), whatever
  the mark of the load, and the index is one known tagged
  immediate: `Invalid` if the index is out of the bounds; otherwise
  the result has the type of the field, and reification makes the
  load that field where the type is an alias. A comment there says
  that the loads from immutable arrays are not all marked
  `Immutable`.
- `simplify/simplify_unary_primitive.ml`, `simplify_array_length`:
  the length is a projection from the type of the array.

## 3. The extension of the model

The names are proposals.

### 3.1 The value

One constructor of `FlambdaValueSpec.value`:

    Value_immutable_array (elements : list value)

It is an immutable array of values made by a primitive, by its
elements, as `Value_block` is an immutable block by its tag and its
fields. It is its contents: two of them are the same value when
they have the same elements, and nothing tells one allocation from
another. It is no cell of the heap.

- `kind_of_value` answers `Value` of it. So it may be a field of a
  block, an element of an array, a value slot, and what a cell of
  the heap holds.
- `array_of statics v` answers its elements, as it answers those of
  a symbol bound to `Static_immutable_array`. So an array made by a
  primitive and a symbol bound to an array of the same elements are
  two values that no primitive tells apart, as for a block and a
  symbol bound to a block: every reading is through `array_of`.
- `is_allocated` answers yes of it, through `array_of`.
- No other observation reads the new constructor, so
  `array_of_disjoint_statement` holds as it is stated.

The value does not keep the kind that it was made at. The
compiler's constant has none either
(`Static_const.Immutable_value_array`), and the lifting makes the
one of the other, so the two must be read alike. It is the choice
made for the static array: section 3.5 has the question that goes
with it.

### 3.2 The primitive

One constructor of `FlambdaPrimitiveModel.variadic_primitive`:

    Make_immutable_array (kind : array_kind)

It is the compiler's `Make_array (kind, Immutable, _)` at the three
array kinds whose elements are of kind `Value` (`Immediates`,
`Gc_ignorable_values`, `Values`). It has no mutability: a
`Make_array` marked `Mutable` is the heap's `Make_mutable_array`,
which stays as it is, and `Immutable_unique` is not a mutability of
arrays. It has no allocation mode (section 6 says what the
conversion does with a local one).

`eval_variadic_primitive` of it and the values `vs`:

- `array_made kind vs`, the function that the heap's
  `Make_mutable_array` uses: every argument is a value that the kind
  holds (a tagged immediate for `Array_immediates`, anything of kind
  `Value` for the other two);
- and no argument is a symbol bound to nothing (`bound_if_symbol`,
  as for `Make_block`; decision D8);
- then the value is `Value_immutable_array vs`.

Its arguments are of kind `Value` and so is its result. It carries
no number, so `prim_in_range` says yes of it; the array that it
makes is in range where its arguments are. Its effects are
`Only_generative_effects Immutable`, as the compiler has them. The
compiler gives a `Make_array` no coeffects
where it is allocated on the heap and coeffects where it is local
(`effects_and_coeffects_of_variadic_primitive`). The model has one
primitive for both, with no coeffects
(`FlambdaHeapSpec.coeffects_of_prim`, its last case): it does not
keep that distinction, under the proposal of decision D37 that a
local allocation is read as one on the heap (section 6).

Of no argument it has a value, the array of no element. The heap's
`Make_mutable_array` of no argument has none, because a location
for each would tell apart two empty arrays that the compiler makes
one constant. That reason is about identity, and this value has
none. It is the choice made for a `Make_block` of no field. The
front end makes neither.

### 3.3 What reads it

No primitive is added and the text of none changes: each reads an
array through `array_of`.

- `Array_length _`: `array_length_of` of the elements.
- `Array_load _ load_kind _`: `array_loaded load_kind elements
  index`. The index is a tagged immediate, at least 0 and below the
  number of elements, and the element is one that the load kind
  takes. The array kind and the mark that the load carries are not
  looked at, as for a symbol bound to a static array: section 2 has
  the comment of the compiler that the mark is not reliable.
- `Is_int` without `variant_only` and `Is_null`: no, as of every
  allocated value. `Opaque_identity` at `Value`: itself.
- `Phys_equal`: section 3.4.

### 3.4 Identity

It has none, as an immutable block has none (decision D19 is open,
and goes with the heap; `requests/C4-heap.md`, section 2.1, has the
reasons, which section 2 above repeats for arrays: sharing by CSE,
and lifting with sharing).

What follows for `Phys_equal`, with no change of its text:

- against a tagged immediate, and against an identity (an imported
  exception): the answer is "not the same";
- against a location: "not the same", in the machine of the heap
  and nowhere else. `eval_prim` has no heap, and no value on a
  location. `FlambdaHeapSpec.exec_prim` has a value only where
  every argument is bound (`argument_bound`: a location that the
  heap does not bind, and a symbol bound to nothing, give none);
  it then asks `eval_phys_equal_location`, which answers "not the
  same" of a location against an allocated value. Why that is
  right of an array: a location is an allocation made `Mutable`,
  or a unique block; an immutable array made at run time is another
  allocation, or after lifting a static constant. A mutable array
  that a program reads as immutable (`%array_to_iarray`) stays its
  location, and is compared as one. No location is the empty
  array;
- against an allocated value with no identity (a block, a closure,
  a boxed number, a string, an array, itself included): no value.
  The machine answers that an array is itself, and Simplify folds
  the comparison of a variable with itself to that answer; in the
  model the term before is undefined there, which the fold refines
  (`phys_equal_same_statement`). One of the 68 units compares an
  array with itself: its two runs are undefined in the model, and
  the compiled program prints that they are the same.

### 3.5 What is undefined, by the standing rules

- a `Make_immutable_array` given an argument that its kind does not
  hold (a block at `Array_immediates`, a naked number at any), or a
  symbol bound to nothing. Simplify gives `Invalid` where the types
  cannot agree with the kind;
- a load at an index that is not a tagged immediate, or out of the
  bounds: the question that is written at `array_index` already;
- a load at a load kind that the element does not fit;
- `Get_tag`, `Block_load`, `Unbox_number`, `String_length` and the
  loads from a string, of an array; a call of one; a projection
  from one;
- `Array_set` of one: it is not a location.

One question for the human is written at the new constructor, and
it is not new: the value is read at any load kind that its elements
fit, whatever kind it was made at, so an array made at `Values`
whose elements are tagged immediates has a value read at
`Load_immediates`. The case of `Array_load` asks it already of a
static array.

### 3.6 What is not in it

- arrays of naked numbers, of floats and of unboxed products, and
  the `Make_array` under a test of `Is_boxed_float` that `Pgenarray`
  gives (a literal whose elements have a type that is not known to
  be other than `float`): the conversion refuses them, and the unit
  is not checked;
- `Duplicate_array`, of which the source is this value and the
  result a cell of the heap: section 4.1;
- mutable arrays, in the conversion: the heap's;
- array comprehensions and the functions of the library on
  immutable arrays, which are calls.

## 4. The boundaries

### 4.1 With the heap

Sent to the owner of the heap as one page, who agrees to all of it;
the four additions it asked for are marked.

1. The immutable array made at run time is a value and no cell.
   `Heap (Make_mutable_array kind)` and `Cell_array` stay as they
   are. When `Make_array` becomes one variadic primitive with its
   mutability, `Immutable` is this request's case and `Mutable` the
   heap's; until then there are two constructors.
2. `Array_length` and `Array_load` are one constructor each. On a
   value that `array_of` reads they are `eval_prim`'s, and the heap
   is not read. On a location they are the heap's
   (`exec_unary_on_cell`, `exec_binary_on_cell`), unchanged: a load
   marked `Immutable` from a location keeps having no value (the
   question written there, on a mutable array read as immutable).
3. `Make_immutable_array` of no argument has a value (section 3.2).
4. `Phys_equal` of a location against an array value is "not the
   same" (section 3.4).
5. The text of the heap's file that changes: `locations_of_value`
   (the locations of the elements) and `effects_of_prim` (the case
   of the new primitive). `value_step` does not change its text:
   its rule `Step_array` is stated through `array_of`, so it comes
   to relate an array value to an array value, and to a symbol
   bound to an array, with related elements, as `Step_block` does
   for blocks. `cell_related`, `heap_evolves`,
   `arrays_hold_their_kinds` and `exec_heap_primitive` are not
   touched.
6. *(Added.)* The heap has a law of the form of
   `eval_prim_preserves_statement`, with the same premises, that is
   not in this tree. It takes the premise that section 5 adds, when
   it comes.
7. *(Added.)* A law of the heap that is not in this tree has
   `respects_observations` for a premise. Nothing is to be done for
   it: its proof goes through `eval_prim_related`.
8. *(Added.)* `kind_of_value` of the new value is `Value`: a cell
   may hold it (`Make_block_with_identity` and `array_element_ok`
   test the kind), and a value in a cell is compared like any
   other.
9. *(Added.)* The order: the series adds a constructor to `value`,
   so every proof by cases on a value with named cases breaks, the
   heap's included. It is cut where the owner of the heap says, so
   that the heap's series in flight are replayed on it once.

Not in the series, and agreed as leaf work in the heap's file once
`step` executes the primitives of the heap: `Duplicate_array`. Its
source is read through `array_of` where it is a value or a symbol,
and through its cell where it is a location; a mutable destination
is a new location, and of no element it has no value, for the
reason given of `Make_mutable_array`; an immutable destination is
this value, and the heap is returned as it came.

### 4.2 With the lifting

Sent to the owner of the lifting, who agrees to it. The texts of
its statements do not change. The function `lift_named` and the
relation `value_lifted` are extended, and the statements are then
about the extended ones: the case of the array is new proof, not
an instance of what is proved, and section 5 has what the ruling
on the relation asks of it.

- `FlambdaLiftSpec.lift_named`, one case:

      | Lift_to_symbol s,
        Prim (Variadic (Make_immutable_array _)) elements =>
        Some
          ([Bind_symbol s
              (Static_const_immutable_value_array elements)], s)

  The array kind is dropped, as the constant has none. So the term
  lifted is defined where the `Let` was not (an element that the
  kind does not hold). That is a refinement and no equivalence, and
  a refinement is what the statements of the lifting conclude.
- `value_lifted`, two rules, those of a block without its tag:

      Lifted_array:
        Forall2 (value_lifted statics') elements elements' ->
        value_lifted statics' (Value_immutable_array elements)
          (Value_immutable_array elements')
      Lifted_to_array:
        lookup s (static_values statics')
        = Some (Static_immutable_array elements') ->
        Forall2 (value_lifted statics') elements elements' ->
        value_lifted statics' (Value_immutable_array elements)
          (Value_symbol s)

- `FlambdaLiftFromCodeSpec.closed_named` and `once_each` need
  nothing: a `Let` of an array of symbols and constants is lifted
  out of code as a block is; and two of them that are lifted out of
  one body share a binding where the guess gives them the same
  symbol and their constants are the same term, and only there. A
  guess that gives one symbol to two that differ is refused, as for
  blocks.
- The checked statements that a unit lifted refines the unit
  (`lift_unit_program_refines_statement`,
  `lift_from_code_unit_program_refines_statement`,
  `lift_to_head_unit_program_refines_statement`) keep their checks:
  the unit leaves with symbols and constants only (`exits_plain`),
  and its lifted form is a well-formed unit. A unit that gives a
  variable to a continuation by which it may leave is refused
  whatever the variable holds, and an array value is no plain value
  (`plain_value`), as a block is none. `lift_simulates_statement`
  is not one of them: it asks that the lifted form is a well-formed
  unit and that it makes no closure, but the symbol, of the code
  that knows its symbol (`only_closures_of`), and no check of plain
  exits; its conclusion in `value_lifted` is the one that section 5
  says grows. That the test tool observes an array and a symbol
  bound to an array alike (section 6) is a test of two runs and no
  theorem: it allows no exit that is not plain, and says nothing of
  a unit run from its imports.
- Simplify also gives a `Let` the symbol of an equal constant that
  the unit binds already. The lifting has no such sharing in this
  tree; its owner says that a second `Let` of an equal array is not
  given the symbol by the first lifting, and that work of its own,
  not in this tree, makes it an alias of the symbol in a later one,
  as for two equal blocks.
- The empty array: the `Let` of a `Make_immutable_array` of no
  argument is paired only if the term after binds a symbol to the
  empty array. The front end makes no such `Let`.
- Which stream writes the cases of the proofs: this one, with the
  word of the owner of the lifting on the patch, as for the static
  arrays. Its owner counts, in its files of proofs: in
  `FlambdaLiftProofs.v`, 12 uses of `lift_named` and 33 places that
  invert `value_lifted` or go by one of two tactics that list its
  rules by name; in `FlambdaLiftFromCodeProofs.v`, 8 and 4; in
  `FlambdaStaticsScopeProofs.v`, 7 uses; and
  `FlambdaMyClosureProofs.value_free`, a function by cases on a
  value. A file of the lifting that is not in this tree has the
  same case analyses, and a series of the lifting that is not in
  this tree adds a rule to `value_lifted` too: the series of this
  request is cut after both, at the word of their owner.

### 4.3 With the pass by types

`FlambdaSimplifyPassSpec.simplify_variadic` has a case for the new
primitive: `Stays_with_kind Value`. The types of the model have no
arrays, so the pass knows of the variable its kind and nothing
else. The owner of that file says what it is to be.

### 4.4 With the sharing of primitives and the unused `Let`s

Two functions take the new primitive with no change of their text.

- `FlambdaNormaliseSpec.prim_may_fold` says yes of every variadic
  primitive: an unused `Let` of an array is removed, as Simplify
  removes a primitive that has only generative effects.
- `FlambdaCseSpec.shareable` says no of it (its last case): two
  `Let`s of one array are not shared, where Simplify shares them if
  an argument is a variable. It is the choice that the file has
  made for `Make_block` and `Box_number`, and says why; a unit in
  which Simplify shared two arrays is not validated.

### 4.5 With the locations as names

`FlambdaLocationsSpec.permute_value` has a case: the elements,
permuted. For the owner of that file.

## 5. What each changed definition reaches

By the search that the integrator runs on every stack: a search
over names, not a judgement. It was run on the definitions of
section 3, compiled with no proof. The search is the one that
reads the models of the primitives and of the kinds
(`FlambdaPrimitiveModel.v`, `FlambdaKindModel.v`) beside the
`Spec` files and `FlambdaModel.v`; that form of it is not in this
tree yet. The form that is did not read the two files, and so did
not find the type `variadic_primitive`; every other line of its
answer is the same.

Its answer: one statement whose text changes,
`eval_prim_preserves_statement`; none added, none removed; one
definition added, `holds_of_arrays`; 24 definitions whose body
changes, of `Spec` files and of `FlambdaPrimitiveModel.v`. The
appendix has each with the statements that it reaches.

Fourteen files of definitions change, in 27 places: `Spec` and
model files of `middle_end/flambda2/rocq/` (twelve) and of
`types/rocq/` (two). Every `Spec` and model file of the tree
compiles with them.

Of the three things that may happen to a statement reached:

**A premise is strengthened: in three statements, by three
definitions.**

- `eval_prim_preserves_statement` has one hypothesis more,
  `holds_of_arrays P`: the property holds of an array value exactly
  when it holds of its elements. It is `holds_of_blocks` for an
  array. `Make_immutable_array` needs one half (the array made of
  values that have the property has it) and `Array_load` the other
  (an element of an array that has the property has it).
- `eval_prim_related_statement` and
  `FlambdaExtcallSpec.eval_extcall_related_statement` have
  `respects_observations` for a premise, which changes in two
  places:
  - `relates_made` has a third conjunct: two arrays made of related
    elements are related. `Make_immutable_array` needs it;
  - the last conjunct of `relates_observations` is stated through
    `array_of`, whose text changes: it now asks, of a first value
    that is an array value, that the second is read as an array
    with related elements. `Array_load` needs it.
  The evaluator of the calls of C functions reads no array, and
  does not need either; the two laws keep one premise, as was
  decided for the static arrays.

Each clause speaks of the new form of value only: of a value that
the tree had it asks nothing. So a use of one of the three laws
must now say what its property or its relation is on an array, and
nothing else of it changes. The uses in this tree, by a search of
the names:

- `eval_prim_preserves`: named in 16 places of 10 files of proofs
  (`FlambdaClosuresProofs.v`, `FlambdaHeapProofs.v`,
  `FlambdaHoistCodeProofs.v`, `FlambdaKnownSlotsProofs.v`,
  `FlambdaLocationsPrimitiveProofs.v`, `FlambdaMyClosureProofs.v`,
  `FlambdaPrimitiveProofs.v`, `FlambdaStaticsInScopeProofs.v`,
  `FlambdaUnusedStaticsProofs.v`, `FlambdaWellKindedProofs.v`).
  Each property goes by cases on a value, and the new case goes
  into the elements as the case of a block goes into the fields:
  that is the hypothesis.
- `eval_prim_related`: the four relations that the static arrays
  had to be shown for. Equality, between a static environment and
  the one with value slots dropped; `value_lifted`, by the two rules
  of section 4.2; the relation of the heap, by `Step_array`; and
  `FlambdaLocationsPrimitiveProofs.moved`, by the case of
  `permute_value`. Two lemmas of `FlambdaSemanticsProofs.v` on the
  arguments of tupled code have the same premise and are used with
  the second and the third.

No statement of the validation, of ranges or of kinds gains a
hypothesis.

**A conclusion is weakened in form, on a new domain:
`value_lifted`.**

`value_lifted` has the two rules of section 4.2. It is in the
conclusion of `lift_simulates_statement`, and in no other
statement; no premise of that statement has it.

A pair that it comes to relate has an array value in it, and not
always at its head: the two rules relate an array value to an
array value and to a symbol; the rules of blocks, of closures and
of partial applications then relate two of those whose parts are
so related; and the array that a symbol stands for is in the
static environment. So what does not change is said of complete
values, and of the static environment that the second is read in,
in which no array value occurs anywhere.

The owner of the lifting reads its statement as weakened in form,
by two shapes of pair. The orchestrator was asked and has ruled,
for the human's review: it is a conclusion weakened in form on a
new domain, which the series may have on four conditions. The
series owes them before any reviewer signs it.

1. *Named, not counted.* Every statement of the tree in which a
   relation that grows is in a conclusion, by name, and apart every
   one in which it is in a premise. For `value_lifted` that is the
   one statement above; for the relation of the heap, the groups
   below.
2. *That nothing changes on what the tree had, as a theorem.* For
   each relation that grows, a statement that is proved: on
   complete values, static environments and heaps in which no
   array value occurs anywhere, the relation holds exactly where
   it held. It is stated with a predicate that says that no array
   value occurs, or by inversion. Until it is proved, "on what the
   tree had nothing changes" is a qualification of this request
   and no more.
3. *The top is unchanged, in text and in meaning.* By their names:
   no statement of the validation, of a unit run on its own or
   from its imports, or of what is observed of a result gains a
   premise or loses a conclusion. And what is observed of an array
   value at an exit is said (section 6: its elements, under the
   constructor of an array, as for a symbol bound to a static
   array), with that two results that a grown relation relates are
   observed alike.
4. *The reviewers.* R3 for `value_lifted`, with the word of the
   owner of the lifting; R2 for the relation of the heap and its
   statements, with the word of the owner of the heap on section
   4.1; R1 for this record and for what is trusted; R5 for the
   primitives.

The three statements whose premise is strengthened are authorised
as they are named above, with a record of the form that the static
arrays had.

**The relation of the heap: 27 statements, in four groups.**

`value_step` does not change its text. Its rule `Step_array` is
stated through `array_of`, so it comes to relate an array value to
an array value and to a symbol bound to an array, either way round,
with related elements; and what holds one, as above. Through
`value_related`, `outcome_related` and its two instances,
`states_related`, `heap_refines` and `heap_expr_refines` it reaches
27 statements, of `FlambdaHeapSpec.v` and of
`FlambdaHeapEquivarianceSpec.v`. They cannot be classed as one.
Each was read for this, and is in exactly one group, by where the
relation is in it. The orchestrator has ruled on the groups, for
the human's review; its ruling is with each.

*(i) Only in a conclusion that asserts it: 14 statements. The
conclusion is weakened in form on the new domain. Authorised in
principle, as named, on the theorem of the second condition.*
`block_and_symbol_related_statement`,
`boxed_poison_refined_statement`, `closed_state_related_statement`,
`cse_adjacent_statement`, `delete_unused_let_statement`,
`exchange_lets_statement`, `garbage_not_observed_statement`,
`heap_refines_reflexive_statement`, `lift_block_statement`,
`lift_closure_of_set_statement`, `lift_closure_statement`,
`load_known_field_statement`,
`location_names_not_observed_statement`,
`outcome_related_reflexive_statement`. The first two are of
outcomes that are written out, with no array in them. The others
are of every closed state, or of every term under every closed
state: of a state that holds an array value they conclude a
refinement, or a relation, in which an array value may stand
against a symbol bound to an equal array.

*(ii) Only in a premise: none.*

*(iii) Denied in the conclusion: 2 statements. Each claims more on
the new domain, and is to be proved again. No authorisation is
needed.*

- `aliasing_observed_statement`: two locations bound to one cell
  are not related to one location given twice, whatever the cell.
  Newly claimed: the same of a cell that holds an array value, and
  against a relation that relates more of what a cell holds. The
  reason does not look at what the cell holds: the correspondence
  of locations is a partial bijection.
- `delete_write_wrong_statement`: there is a `Let` of a variable
  that is not used whose removal is no refinement. Newly claimed:
  that the witness, a write, still is none against outcomes that
  are related by more. The witness has no array.

*(iv) On both sides of an implication or of an equivalence: 11
statements. Authorised in principle, as named, on two theorems.*
What changes for one who uses each:

- `heap_run_related_statement` (two related states step to related
  states, or leave with equivalent outcomes): it may be given two
  states of which one holds an array value where the other holds a
  symbol bound to an equal array, which it could not be given; and
  what it concludes of any two states is in the larger relation.
- `machine_respects_relation_statement` and
  `machine_respects_relation_except_statement` (related states
  refine): the same; more pairs of states are related, and the
  refinement concluded is up to the larger relation.
- `outcome_equivalent_refines_statement` (equivalent outcomes
  refine): both sides grow by the same pairs; it is used as before.
- `outcome_equivalent_symmetric_statement`: the same. It needs that
  what is added is symmetric, and it is: `Step_array` reads both
  values through `array_of`.
- `outcome_related_transitive_statement`: two relations may now be
  chained through an outcome that holds an array value, as an
  array against a symbol against an array.
- `related_projections_statement` (a function slot projected from
  two related closures gives related closures): no array value is
  a closure, so the new pairs are met only in the value slots that
  the two closures carry; what is concluded of the closure
  projected is in the larger relation.
- `states_related_nothing_statement` (the two forms of related
  states are one): both sides grow alike; it is used as before.
- `heap_expr_refines_equivariant_statement`,
  `heap_refines_equivariant_statement` and
  `outcome_related_equivariant_statement` (refinement and the
  relation under a renaming): each carries the larger relation to
  the larger relation; they are used as before.

The two theorems, which the series states and proves, and which
its record cites for each of the 11:

- *conservativity*, the theorem of the second condition: on
  complete values, static environments and heaps in which no array
  value occurs anywhere, the relation holds exactly where it held;
- *invariance*: a predicate on whole states that a step keeps. It
  says that no array value occurs anywhere in the state (its
  environment, its continuations, its static environment, its
  heap), and that `Make_immutable_array` occurs in nothing that
  the state may come to execute: its term, the code that its
  static environment binds, and the handlers that its
  continuations hold. A term that has no such primitive is not
  enough: it may call code that has one, or apply a continuation
  whose handler has one. The same is stated of the machine of the
  heap.

Which gives each statement back as it was signed, on what the tree
had:

- conservativity alone, for the laws of the relation itself:
  `outcome_equivalent_refines_statement`,
  `outcome_equivalent_symmetric_statement`,
  `outcome_related_transitive_statement`,
  `related_projections_statement`, and
  `outcome_related_equivariant_statement`, which also needs the
  word of the owner of `FlambdaHeapEquivarianceSpec.v`;
- conservativity with invariance, for those about a run:
  `heap_run_related_statement`,
  `machine_respects_relation_statement`,
  `machine_respects_relation_except_statement`; and
  `heap_refines_equivariant_statement` and
  `heap_expr_refines_equivariant_statement`, which speak of the
  behaviours of states, the second under every closed state, so
  that the record owes for them the states that the tree had and
  their renaming, with the word of the same owner. The ruling puts
  `states_related_nothing_statement` here; it is of two states and
  no run, and conservativity may be enough for it: the record of
  the series says which.

No corollary is asked for each statement: the two theorems are in
the tree as statements, and the transfer of each of the 11 is
checked by the reviewer when the proofs are.

The reviewers of this part: R2, with the word of the owner of the
heap on each of its statements; R1 for the record.

**A case more, and nothing added: every other definition.**

Each is a type with one more constructor, or a function by cases
that answers of the cases it had what it answered. On a term with
no `Make_immutable_array`, and of values none of which is or holds
an array value, each is what it was. So a statement that it reaches
gains no hypothesis and loses no conclusion, and says of the new
case what the function does there:

- the types `value` and `variadic_primitive`, which most of the
  statements of the tree reach (2041 and 2282);
- `array_of`, beyond the two places above: `Array_length` and
  `Array_load` have a value on an array value; `is_allocated` says
  yes of it, so `Is_int`, `Is_null` and `Phys_equal` answer of it
  as of a symbol bound to a static array;
- `eval_variadic_primitive`, the kinds of the arguments and of the
  result, `variadic_primitive_in_range`, `effects_of_prim`,
  `simplify_variadic`: the case of the new primitive (sections 3.2
  and 4.3);
- twelve functions by cases on a value, in ten files: each goes
  into the elements as it goes into the fields of a block, but
  `FlambdaKnownSlotsSpec.value_is`, which says no;
- `lift_named`: the case of section 4.2. `lift_expr` and the two
  liftings out of code and out of arms then lift a `Let` of an
  array that the guess names, and the validation may answer
  `Same_once_lifted` of a unit that has one. Of a unit that has
  none, every one of them is what it was.

What follows in the proofs, counted in this tree by a search of the
names: `Value_block` is named in 9 files of proofs, in 28 places,
and `Make_block` in 5, in 9 places; the counts of the lifting are
in section 4.2. A case analysis that names no constructor is not
found by such a search. Three OCaml files of the tests name a
constructor of either type (`tests/tools/flsemantics.ml`,
`flmodel_to_fexpr.ml`, `tests/semantics/types/types_difftest.ml`).

## 6. What the test tool needs

For V2, who has the conversion, and for R1.

- `convert_variadic_primitive`: `Make_array (kind, Immutable, _)`
  at the array kinds `Immediates`, `Gc_ignorable_values` and
  `Values` becomes `Make_immutable_array` of that kind. Refused,
  each by name: `Immutable_unique`; `Mutable`, until the conversion
  of the heap; and every other array kind.
- A local one: the conversion already takes a `Make_block` and a
  `Box_number` made in a region as one made on the heap (decision
  D37, open; the entry "What the conversion of terms leaves out" of
  the trust ledger). An array is taken the same way, under the same
  entry and the same condition, which is of both terms of a check,
  the one after Simplify as much as the one before: nothing
  allocated in a region is used after the region has ended. No
  verdict of the validation checks that condition, whichever it
  is. The header of `FlambdaPrimitiveModel.v` says that the
  conversion must refuse a local `Make_block` and `Box_number`: it
  is older than decision D37, and the series corrects the sentence,
  citing the decision.
- `lifting_guess`: a `Let` of a `Make_immutable_array` is paired
  with the symbol that the term after binds to an
  `Immutable_value_array` of the same elements, a symbol given
  once, as a block is paired (the word of the owner of the
  lifting). Nothing is believed of the guess.
- `observe`: an array value is observed as a symbol bound to a
  static array is, under the constructor `Array` and by its
  elements. So the two runs agree where one returns an array and
  the other a symbol bound to an array with the same observations,
  and never by an array on one side and a block on the other.
- The printers, and the round trip (`flmodel_to_fexpr.ml`): the
  fexpr syntax has the primitive (`parser/fexpr_prim.ml`,
  `make_array`).

What is trusted more than today: one case of the conversion of
primitives, which sends the `Make_array` marked `Immutable`, at
the three kinds, to the constructor of the model with the kind,
and refuses the others; and one case of `observe`, which goes into
the elements of an array. Both extend entries that the trust
ledger has ("The conversion of primitives"; "What the tool
reports", which has `observe`), and the lines themselves are to be
read when they exist, with the series. No axiom, and no
handwritten realisation of an extracted name.

## 7. The measure

Of an experiment, and not of the units as they are. An edit of the
test tool that is not the conversion, and is not in this tree,
changes the term before: it binds an immutable array made by
`Make_array` as a static immutable array where it is made, under
the symbol that the term after binds to the same elements. The
tool then checks that changed term against the term after. So what
follows are the outputs of the tool on a transformed pair. None is
a verdict on a unit, and the experiment stands for the lifting of
section 4.2 at the toplevel of a unit only.

The 68 units of section 1, with the tool of the tree that has the
static arrays and that edit; each row is the line that the tool
prints:

| the tool prints | default flags | `-O3` |
|---|---|---|
| "validated" | 12 | 10 |
| "validated with its imports" | 2 | 1 |
| "validated with nothing imported" | 28 | 22 |
| "not validated" | 17 | 26 |
| that the term before is undefined | 3 | 3 |
| "not checked" | 6 | 6 |

Without the edit, at both settings: 4, 1, 0, 11, 0, 52.

- Of the 46 units of section 1, at the default flags: 8, 1 and 28
  in the first three rows.
- Where both runs return, they return what the compiled program
  prints, from bytecode and from native code at the default flags,
  `-O3` and `-Oclassic`.
- **What the 28 wait for.** Each reads an array with a check of
  the bounds, which raises `Invalid_argument`, an imported symbol;
  and the line of each is by the verdict `Same_once_lifted`, which
  is outside `FlambdaValidateImportsSpec.holds_from_imports`: "The
  liftings, and what is done to a lifted term ... are each stated
  from the empty static environment. Each is to be stated from the
  imports by its owner before this is." The owner of the lifting
  says that this is its next series. Until then the line of these
  28 is of the transformed pair run with nothing imported.
- The 17, at the default flags: 10 have a `Switch` whose arms pass
  constants, which is a load from a table after Simplify; 3 take
  the length of an array twice, which Simplify shares; 2 have a
  check of the bounds that Simplify decides from the lengths of
  arrays that it knows; 2 make an array of which an element is
  computed, which the edit does not pair.
- The 9 more at `-O3`: eight are loops inlined where they are
  called, and one has a check that goes because two arrays have the
  same known length.
- The 3 where the term before is undefined: the unit of section
  3.4; and two that raise an imported exception on every path, so
  that the run with nothing imported is undefined.
- The 6 not checked: five make a mutable array, and one takes the
  length of an array that may be of floats.

## 8. What is not part of it

Each is named to its owner, who has it:

- the `Switch` whose arms pass constants, against the load from a
  table of the term after: a way more of
  `FlambdaMergeSwitchesSpec.merge_switches`, with the binding of
  the table at the head of the term before
  (`requests/P1-immutable-arrays.md`, section 4);
- `Array_length` in `FlambdaCseSpec.shareable`. What it needs of
  the heap is in the tree: `FlambdaHeapSpec.heap_evolves` says that
  an array keeps its number of elements, and
  `exec_prim_evolves_statement` that every primitive leaves a heap
  that the one it was given evolves to;
- the liftings stated from the imports (section 7);
- `Duplicate_array`, and the conversion of mutable arrays (section
  4.1).

## 9. What is decided here, and what is asked

Decided, by the standing rules, each with its place in section 3:
the array made at run time is a value with no identity; it does not
keep its kind; a `Make_immutable_array` of no argument has a value;
what is undefined (section 3.5).

Asked:

- of R5, the primitive and the value (sections 2 and 3);
- of R1, the classes of section 5 and the paragraph on trust of
  section 6;
- of R3, section 4.2;
- of the orchestrator: the class of `value_lifted` and of the
  groups of the statements of the heap. Both are ruled, with what
  the series owes for each (section 5);
- of the human, nothing new: the question on the load kind (section
  3.5) is the one asked of the static array.

Answers so far: the owner of the heap agrees to section 4.1, and
asked for its last four items; the owner of the lifting agrees to
section 4.2, and gave the counts that are there. R3 has read
section 4.2 as a design and finds it clear; two sentences of this
request are its repairs (when two `Let`s share a binding; that
what the lifting concludes is not widened), and one of section 2
(a projection from a symbol needs no proof that it holds no local
value). R5 has read sections 2 and 3 and finds them coherent with
the choice made for the static array; from it, that the list of
when Simplify does not lift is no statement of exactly when, what
the compiler says of the coeffects of a local array, and where a
location is compared. R1 has read the whole: from it, the groups
of the statements of the heap, that a pair that is added need not
have an array at its head, the counts of the search with the files
of the model, and the paragraphs on trust and on the measure. No
definition and no proof has been reviewed.

The order of work, after approval: the definitions and their
proofs, as one series that ends with the test tool and its units,
cut where the owners of the heap and of the lifting say (sections
4.1 and 4.2); every owner of a file that it touches gives its word
on the patch. With it: the header of `FlambdaValueSpec.v` and the
sentence of `rocq/HACKING.md` that say that `array_of` reads a
symbol only.

## Appendix: what each changed definition reaches

For section 5. The 24 definitions of a `Spec` or model file whose
body changes, each with the statements of the tree in which its
name occurs, directly or through other definitions; 40 is the
number above which the statements are counted and not named. A
definition is taken with its file, and a use of a name that two
files define is counted for both, so the search may list too much
for that reason and not too little.

"A case more" is the last class of section 5.

Reaching at most 40 statements:

- `value_sets_are` (`FlambdaClosuresSpec.v`): a case more. Through other
  definitions in `closure_of_code_statement`, `sets_are_kept_statement`.
- `effects_of_prim` (`FlambdaHeapSpec.v`): a case more. Directly in
  `cse_adjacent_statement`, `exchange_lets_statement`,
  `mutable_load_not_stable_statement`, `no_coeffects_statement`,
  `no_effects_statement`, `only_generative_effects_statement`; through
  other definitions in `delete_unused_let_statement`.
- `locations_of_value` (`FlambdaHeapSpec.v`): a case more. Directly in
  `exec_named_keeps_locations_bound_statement`,
  `exec_prim_keeps_locations_bound_statement`; through other definitions
  in `heap_expr_refines_equivariant_statement`,
  `closed_state_related_statement`, `cse_adjacent_statement`,
  `delete_unused_let_statement`, `delete_write_wrong_statement`,
  `exchange_lets_statement`, `garbage_not_observed_statement`,
  `heap_refines_reflexive_statement`, `heap_step_closed_statement`,
  `lift_block_statement`, `lift_closure_of_set_statement`,
  `lift_closure_statement`, `load_known_field_statement`,
  `outcome_related_reflexive_statement`, `behaves_permuted_statement`,
  `exec_named_permuted_statement`, `no_location_bound_statement`,
  `permute_state_locations_bound_statement`,
  `run_keeps_locations_bound_statement`, `run_permuted_statement`,
  `step_keeps_locations_bound_statement`, `step_permuted_statement`,
  `exec_prim_permuted_statement`, `hidden_entry_statement`,
  `cell_locations_nominal_statement`,
  `cont_value_locations_nominal_statement`,
  `env_locations_nominal_statement`, `heap_locations_nominal_statement`,
  `state_locations_nominal_statement`,
  `static_env_locations_nominal_statement`,
  `value_locations_nominal_statement`.
- `value_closures_bound` (`FlambdaHoistCodeSpec.v`): a case more.
  Through other definitions in `let_closures_runs_statement`,
  `closures_in_scope_run_statement`.
- `value_is` (`FlambdaKnownSlotsSpec.v`): a case more. Through other
  definitions in `read_slot_sound_statement`, `slots_as_kept_statement`.
- `value_slots_known` (`FlambdaKnownSlotsSpec.v`): a case more. Through
  other definitions in `read_slot_sound_statement`,
  `slots_as_kept_statement`.
- `lift_named` (`FlambdaLiftSpec.v`): a case more. Through other
  definitions in `lift_to_head_equivariant_statement`,
  `lift_to_head_unit_program_refines_statement`,
  `lift_from_code_equivariant_statement`,
  `lift_from_code_unit_program_refines_statement`,
  `lifted_out_bindings_equivariant_statement`,
  `lift_expr_equivariant_statement`, `lift_simulates_statement`,
  `lift_unit_program_refines_statement`,
  `lift_expr_keeps_scope_statement`,
  `lift_from_code_keeps_scope_statement`,
  `lift_to_head_keeps_scope_statement`,
  `with_lifting_keeps_scope_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `lifted_in_turn_equivariant_up_to_statement`,
  `lifted_in_turn_keeps_scope_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`,
  `with_lifting_equivariant_statement`.
- `value_lifted` (`FlambdaLiftSpec.v`): a conclusion weakened in form on
  a new domain. Directly in `lift_simulates_statement`.
- `permute_value` (`FlambdaLocationsSpec.v`): a case more. Directly in
  `eval_prim_permuted_statement`,
  `exec_prim_permuted_exactly_statement`,
  `exec_prim_permuted_statement`, `kind_of_permute_value_statement`,
  `lookup_permute_env_statement`; through other definitions in
  `behaves_permuted_statement`, `exec_named_permuted_statement`,
  `permute_state_locations_bound_statement`, `run_permuted_statement`,
  `step_permuted_statement`, `hidden_entry_statement`,
  `cell_locations_nominal_statement`,
  `cont_value_locations_nominal_statement`,
  `env_locations_nominal_statement`, `heap_locations_nominal_statement`,
  `is_bound_permute_heap_statement`, `lookup_permute_heap_statement`,
  `permute_state_inverse_statement`, `rename_permute_state_statement`,
  `state_locations_nominal_statement`,
  `static_env_locations_nominal_statement`,
  `value_locations_nominal_statement`.
- `relates_made` (`FlambdaPrimitiveSpec.v`): a premise is strengthened.
  Through other definitions in `eval_extcall_related_statement`,
  `eval_prim_related_statement`.
- `result_kind_of_variadic_primitive` (`FlambdaPrimitiveSpec.v`): a case
  more. Through other definitions in `examples_well_formed_statement` of
  `FlambdaPartialApplicationSpec.v`, `eval_prim_kinds_statement`,
  `examples_well_formed_statement` of `FlambdaTupledSpec.v`,
  `kind_of_named_equivariant_statement`,
  `well_kinded_equivariant_statement`,
  `well_kinded_unit_equivariant_statement`, `run_well_kinded_statement`,
  `step_well_kinded_statement`, `well_kinded_exit_statement`,
  `well_kinded_no_kind_fault_statement`,
  `well_kinded_unit_exits_statement`,
  `well_kinded_unit_never_faults_statement`,
  `well_kinded_unit_state_statement`.
- `value_in_range` (`FlambdaPrimitiveSpec.v`): a case more. Directly in
  `eval_extcall_in_range_statement`, `eval_prim_in_range_statement`,
  `blocks_in_range_statement`, `run_exit_in_range_statement`,
  `add_definitions_of_params_satisfies_in_range_statement`,
  `add_variable_definition_satisfies_in_range_statement`,
  `in_range_blocks_have_tags_statement`; through other definitions in
  `handler_refines_from_in_range_statement`,
  `let_cont_handler_refines_in_range_statement`,
  `target_valuation_in_range_statement`, `integers_in_range_statement`,
  `run_in_range_statement`, `step_in_range_statement`,
  `well_formed_in_range_statement`,
  `add_alias_satisfies_in_range_statement`,
  `create_satisfies_in_range_statement`,
  `example_out_of_range_statement`,
  `increment_scope_satisfies_in_range_statement`,
  `replace_equation_satisfies_in_range_statement`,
  `satisfied_strictly_satisfies_in_range_statement`,
  `satisfies_in_range_statics_extend_statement`,
  `satisfies_in_range_strictly_statement`.
- `value_statics_among` (`FlambdaStaticsInScopeSpec.v`): a case more.
  Through other definitions in `statics_bound_in_run_statement`.
- `value_eqb` (`FlambdaTypeMeaningBoolSpec.v`): a case more. Directly in
  `value_eqb_decides_equality_statement`; through other definitions in
  `closures_entry_satisfied_b_iff_statement`,
  `env_extension_satisfied_b_iff_statement`,
  `head_of_kind_value_non_null_satisfied_b_iff_statement`,
  `head_of_kind_value_satisfied_b_iff_statement`,
  `row_like_block_case_satisfied_b_iff_statement`,
  `row_like_closures_case_satisfied_b_iff_statement`,
  `row_like_for_blocks_satisfied_b_iff_statement`,
  `row_like_for_closures_satisfied_b_iff_statement`,
  `type_satisfied_b_iff_statement`.
- `value_avoids` (`FlambdaUnusedStaticsSpec.v`): a case more. Through
  other definitions in `lift_block_statement`,
  `lift_closure_of_set_statement`, `lift_closure_statement`,
  `drop_head_statics_refines_from_statement`,
  `drop_statics_refines_statement`,
  `envs_free_of_equivariant_statement`.
- `value_well_kinded` (`FlambdaWellKindedSpec.v`): a case more. Directly
  in `well_kinded_exit_statement`; through other definitions in
  `run_well_kinded_statement`, `step_well_kinded_statement`,
  `well_kinded_no_kind_fault_statement`,
  `well_kinded_unit_state_statement`.

Reaching more than 40 statements:

- `value_valid` (`FlambdaClosuresSpec.v`): a case more. Directly in
  `closure_in_set_valid_statement`, `eval_named_valid_statement`,
  `state_valid_step_statement`, `well_formed_exit_valid_statement`;
  through other definitions in 165 statements.
- `variadic_primitive` (`FlambdaPrimitiveModel.v`): a case more. Through
  other definitions in 2282 statements.
- `args_kind_of_variadic_primitive` (`FlambdaPrimitiveSpec.v`): a case
  more. Through other definitions in 68 statements.
- `eval_variadic_primitive` (`FlambdaPrimitiveSpec.v`): a case more.
  Through other definitions in 554 statements.
- `variadic_primitive_in_range` (`FlambdaPrimitiveSpec.v`): a case more.
  Through other definitions in 56 statements.
- `simplify_variadic` (`FlambdaSimplifyPassSpec.v`): a case more.
  Through other definitions in 66 statements.
- `array_of` (`FlambdaValueSpec.v`): a premise is strengthened in the
  two laws of related values, and the relation of the heap relates more;
  elsewhere a case more. Directly in `array_of_disjoint_statement`;
  through other definitions in 574 statements.
- `value` (`FlambdaValueSpec.v`): a case more. Directly in 346
  statements; through other definitions in 1695.
