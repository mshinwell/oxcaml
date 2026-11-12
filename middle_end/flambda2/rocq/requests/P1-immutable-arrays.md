# P1: static immutable arrays of values

For the tables that Simplify makes of a match whose arms are
constants.

For the human, C0 (the values and the terms), V2 (the conversion and
the validation) and R5 (review). Nothing of this is in the model yet.
A prototype of the definitions, not in this tree and with no proof,
was used for the measure of section 5; the proofs wait for the heap
to be in the state of the machine.

## 1. Why

Simplify replaces a `Switch` whose arms all give one continuation
constants by a load from an immutable array that it makes a static
constant. The model has no such constant, so the conversion of the
test tool refuses the unit after Simplify, and nothing is run: not
even the two runs are compared. The source has no array.

It was met in four ordinary units out of twenty-two written to try
pattern matching: a match from seven constant constructors to seven
integers; a match on an integer with the constants 0 to 7 and a
default; the same with runs of equal constants; and a match on a pair
of two values of a variant of three constant constructors. Three arms
are enough. A function from an enumeration, or from a small range of
integers, to constants has it, unless the constants are the number of
the arm times a constant plus a constant, of which Simplify makes
arithmetic.

## 2. What the compiler makes

All of it is in `simplify/simplify_switch_expr.ml`, when a `Switch`
is rebuilt on the way up (`rebuild_switch`).

- Where every arm applies one continuation, none with a trap action,
  each position of the arguments is classified
  (`recognize_mergeable_argument`): the same in every arm; the
  scrutinee, tagged; its negation; an affine function of the
  discriminant; or a **lookup table** (`Lookup_table_argument`). The
  last is taken where the discriminants are consecutive, from a first
  `d`; the argument of every arm is a constant or a symbol, all of
  one kind; and the arguments are not an affine function of the
  discriminant. A variable is refused. A poison constant is allowed:
  in a table of naked numbers it is written as an arbitrary number
  (`create_lookup_table_array_const`, `fields_to_or_variables`), and
  in a table of values it stays the poison constant, so an element
  of the static constant may be poison. The `Switch` must have at
  least three arms (`enough_arms`).
- The kind of array. For arguments of kind value that are all tagged
  immediates: array kind `Immediates`, load kind `Immediates`. For
  other arguments of kind value (symbols, tagged immediates and nulls
  may be mixed): `Values` and `Values`. For naked numbers: the array
  kind of that number (`Naked_ints`, `Naked_int32s`, ...), and the
  static constant is an array of that number
  (`Immutable_int_array`, ...).
- What is built (`rebuild_mergeable_argument`):
  - a static constant `Static_const.Immutable_value_array` of the
    arguments in the order of the arms, bound to a new symbol named
    `switch_block` (two equal tables of one `Switch` share a symbol),
    with the type of an immutable array of those elements;
  - `Tag_immediate` of the scrutinee, which the sharing of primitives
    makes the value that was untagged, where the scrutinee was an
    untagging;
  - where `d` is not zero, `Int_arith tagged_imm add` of that and
    `-d`;
  - `Array_load (array_kind, array_load_kind, Immutable)` of the
    symbol and that index, whose result is given to the continuation
    in place of the `Switch`.
- The compiler has the same static constant for an immutable array
  that Simplify lifts, and the empty array is a constant of its own
  (`Static_const.Empty_array`; closure conversion makes it of an
  array made of no element, mutable or not). These were not read for
  this request.

So after Simplify such a function is, for a parameter `v` that the
term before untags and tests:

    let x = Array_load Immediates ($switch_block, v) in cont k (x)
    with  $switch_block = Immutable_value_array (8, 6, 9, 7, 4, 0, 1)

## 3. The smallest extension of the model

No heap: the array is immutable static data, as a static block is.
It is not a location of the heap and nothing writes it.

- **A static constant** (`FlambdaModel.static_const`):
  `Static_const_immutable_value_array (elements : list simple)`. It
  is the compiler's constant: the elements are `Simple`s, with no
  array kind.
- **What a symbol is bound to**
  (`FlambdaValueSpec.statically_allocated_value`):
  `Static_immutable_array (elements : list value)`, made by
  `eval_static_const` of the values of the elements, as a static
  block is made of its fields.
- **An observation**, `array_of statics v`: the elements, of a symbol
  bound to such an array. `is_allocated` answers yes of one, so
  `Is_int` (without `variant_only`) and `Is_null` answer no, and
  `Phys_equal` treats it as it treats a static block.
- **The two primitives**, which `eval_prim` has no value on today:
  - `Array_length kind` of a value that `array_of` reads:
    `array_length_of` of the elements;
  - `Array_load kind load_kind mut` of such a value and an index:
    `array_loaded load_kind elements index`.
  Both functions are those of the section "Arrays" of
  `FlambdaPrimitiveSpec.v`, which the arrays of the heap use: the
  index is a tagged immediate at least 0 and below the number of
  elements, and the element is one that the load kind takes (a
  tagged immediate for `Immediates`, anything of kind value for the
  other two).

What is undefined, by the standing rules:

- an index that is not a tagged immediate, or is out of the bounds of
  the array: the load has no value. This is the CR that is at
  `array_index` already; the rewrite of section 4 is an equivalence
  because of it. If it is ever decided otherwise, one half is left
  and not the other (section 4, "The direction");
- an element that the load kind does not take (a symbol in the table
  read at `Immediates`): no value, where the load is executed;
- an element that is not of kind value is never loaded, as no load
  kind of the model takes it. Nothing is asked where the constant is
  bound: a static block asks nothing of its fields either;
- `Get_tag`, `Block_load` and `Unbox_number` of an array, and
  `Array_length` and `Array_load` of a block, a closure, a boxed
  number or a string: no value. Simplify makes these `Invalid` from
  the types, where a program reaches them by a cast;
- the mark of the load is not looked at, as for a `Block_load` of an
  immutable block; nor is the array kind that the load or the length
  carries, as for the arrays of the heap;
- `Array_set` of one: no value. It is not a location.

One CR to add, at the case of `Array_load`: the model reads a static
array at any load kind that its elements fit, where the compiler's
constant was made for one. A table of tagged immediates read at
`Values` has a value. I think that is right (it is what a load at
`Values` of an `int array` does), and it is the choice already made
for the arrays of the heap.

Not in this step: an immutable array that is made when the program
runs (`Make_array` marked `Immutable`), which needs a form of value;
the tables of naked numbers, which a `Switch` whose continuation
takes a naked number gives (the conversion refuses them, and the
unit stays "not checked"); arrays of floats; the empty array.

What changes, counted on the prototype: one constructor of each of
the two types, and a case in every match on either that has no
wildcard: about forty cases in 24 files of definitions (`Spec` and
model files of `middle_end/flambda2/rocq/` and of `types/rocq/`),
each the case of a static block without its tag, or the case of a
static string where the fields do not matter. The proofs by cases on
the two types follow, and four OCaml files of the tests match on
them (`tests/tools/flsemantics.ml`, `flmodel_to_fexpr.ml`,
`flroundtrip.ml`, and `tests/semantics/types/types_difftest.ml`).
The laws of the primitives have their cases for the two primitives
(`static_values`, `statics_extend`, `symbols_bound`, `kinds`,
`preserves`, `in_range`, `related`): each reads the static
environment through `array_of` only, as the loads from a string read
it through `string_of`. The section "Arrays" moves up in its file, as
`eval_unary_primitive` now uses it. In the types, the type that
Simplify gives the symbol of such a constant is not modelled in the
prototype (`FlambdaSimplifyStaticsSpec.static_const_type` answers
`None`): the owner of that file says what it is to be.

## 4. What the validator needs

The term before has the `Switch` and the term after has the load, so
a rewrite from one to the other is needed. Both directions are sound
and they are not equally cheap.

- **From the load to the `Switch`, on the term after.** Where the
  unit binds the symbol to an array of constants `c_0 .. c_(n-1)`,
  each one that the load kind takes and of the kind of the `Let`,
  and `i` is a variable,

      let x = Array_load ($t, i) in cont k (.. x ..)

  becomes

      let x = Untag_immediate (i) in
      switch x
        | 0 -> cont k (.. c_0 ..)
        | ..
        | n-1 -> cont k (.. c_(n-1) ..)

  with `x` bound at the kind of naked immediates; `x` is used only
  in the arguments of that one application. It is an
  **equivalence**: each side has a value exactly where `i` is a
  tagged immediate that is the number of an element, and then gives
  `k` the same arguments; the test of the kind of `x` that the first
  `Let` makes is the condition on the constants. So it may be used
  on the term after, which has equivalences only. It makes no name.
  Two conditions go with it, both from the review of this request,
  and it depends on one thing that the validation does not do today
  ("The binding that is left", below):
  - *Where the table is bound.* The load has a value only where the
    static environment binds the symbol to the table; the `Switch`
    asks nothing of the static environment. Under an environment in
    which the symbol is not bound to the table, the rewrite would
    make a term that is defined of one that is not, or, where the
    symbol is bound to another array, a term with another result. So
    "what the unit binds the symbol to", as the rewrites that follow
    known symbols take it, is not enough: those are refinements of a
    unit run on its own, and a normalisation of the term after is an
    equivalence of terms under every environment. The rewrite is to
    fire only where the term itself shows that the table is bound
    whenever the load is executed: in the body of the `Let_static`
    that binds the symbol, and in the code that this `Let_static`,
    or one inside its body, binds. The facts are kept by scope, as
    the rewrite goes down the term; the rule of scope of the static
    names is that of `FlambdaStaticsInScopeSpec.v`. A symbol that the
    unit imports, or one bound below the code that loads from it, is
    left alone. The other way would be a guard, proved apart, that
    the table is bound wherever the load is executed; I recommend the
    facts by scope. What the proof needs of the machine is that a
    static name, once bound, stays bound to the same thing in the
    states reached from the binding; whether that holds of every term
    or only of a well-formed one is to be settled when it is stated.
    The normalisation of the term after is an equivalence with no
    premise, and this request does not ask to weaken it: if the fact
    holds only of a well-formed term, the rewrite gets a guard that
    the validator checks, or it waits.
  - *The direction.* If a load out of the bounds were given a value,
    the term with the load would be defined where the term with the
    `Switch` is not. The term with the load would still refine the
    term with the `Switch`, which is the half that the validation
    uses of a rewrite of the term after; the other half, that the
    term with the `Switch` refines the term with the load, would
    fail, and with it the equivalence. The normalisation of the term
    after is stated as an equivalence today, so the rewrite would
    then be withdrawn from it or that statement weakened; the second
    rewrite below, on the term before, would be the one that stays a
    refinement.
  - *The binding that is left.* After the rewrite nothing mentions
    the symbol of the table, and the term before has no such
    binding. The validation removes the static bindings that are not
    used from the term before only, today, and as a refinement. The
    removal from the term after of a static binding that nothing
    mentions, as an equivalence, is not in the validation yet; the
    owner of the validation has it to do, for code and closures that
    an inlined call leaves behind as well. The rewrite validates no
    unit until it is there.
- **From the `Switch` to the load, on the term before.** This is
  what Simplify does, beside the two ways that
  `FlambdaMergeSwitchesSpec.merge_switches` has. It has to bind a
  symbol to the table at the head of the unit, from inside code, and
  the symbol has to be the one that the term after has: a guess that
  the tool makes and the validator checks, as for the lifting of a
  block out of a function. It is the dearer of the two.

I recommend the first. Where the first discriminant is not zero the
term after has the index less that discriminant, and the `Switch`
that the rewrite makes is on that difference with the arms from 0,
where the term before tests the scrutinee with the arms from `d`:
one more small rewrite, or the same one reading the `Let` of the
index. None of the four units has it.

## 5. The measure

Definitions only: the prototype of section 3 (not in this tree) in
the `Spec` and model files, extracted, with no proof built, and the
conversion of the test tool with the constant and the two primitives
(section 6). The integration branch at 222450f953; the tool built
there as it is and with the prototype; both run on the same terms:

| Set | Units | Outputs that differ |
|-----|-------|---------------------|
| the corpus, made from OCaml sources | 257 | 1 |
| the corpus, written by hand | 111 | 0 |
| the 600 generated units of `census/README.md` | 600 | 0 |
| 240 generated units of two later profiles | 240 | 0 |
| four sets of probing units, not in this tree | 263 | 4 |

- **Gained: four units**, those of section 1. Each went from "not
  checked" to two runs that are **the same** (the results are those
  worked out by hand from the sources), and "not validated".
- With each load replaced by hand in the term after, as the first
  rewrite of section 4 has it (one load in three of the units, two in
  the fourth), and the binding of the table, which nothing then
  mentions, taken out, the two terms of each of the four are the same
  up to the names bound. So that rewrite and the removal of that
  binding are all that these four need. This was done on the terms
  as the tool prints them; the validator was not run on the result.
- **Lost: none.** No verdict changes in any other unit.
- **One output moves and keeps its verdict**: `array_literal.ml` of
  the corpus, which makes a mutable array, is still not checked; the
  tool now refuses its `Make_array` where it refused its
  `Array_load`, so one line of its `.expected` changes.

## 6. What the test tool needs

For V2, who has the conversion. In `tests/tools/flsemantics.ml`:

- `convert_static_const`: `Immutable_value_array` becomes the new
  constant, its fields converted as those of a block. `Empty_array`
  and the arrays of naked numbers stay refused.
- `convert_unary_primitive`: `Array_length` at an array kind that is
  `Immediates`, `Gc_ignorable_values` or `Values`.
  `convert_binary_primitive`: `Array_load` at those three array
  kinds, with its load kind and its mark. `Make_array` and
  `Array_set` stay refused until the machine that the tool runs has
  a heap, so a unit that makes a mutable array is not checked, as
  today.
- A case for the new constant wherever the tool goes by cases on
  the static constants of the model or on what a symbol is bound to:
  where it prints a term, counts what a term refers to, finds the
  code and the value slots of a symbol, and reads what a unit
  returns. What is observed of an array is its elements, under a
  constructor of its own and not as a block of tag 0 (V2's word), so
  that the two runs cannot agree by an array on one side and a block
  on the other. The prototype read it as a block of tag 0; none of
  the four units returns an array.
- The round trip (`flmodel_to_fexpr.ml`, `flroundtrip.ml`): the
  fexpr syntax has the constant (`parser/fexpr.ml`,
  `Immutable_value_array`). `tests/semantics/types/types_difftest.ml`
  matches on the static constants in several places; its cases come
  in the same series, as the compiler must build at every commit
  that lands.
- The one line of `array_literal.expected`.

## 7. What is decided here, and what is asked

Decided, by the standing rules, each with its place in section 3: a
load out of the bounds, or at a load kind that the element does not
fit, is undefined; a primitive of blocks on an array and a primitive
of arrays on a block are undefined; the mark and the array kind of an
access are not looked at; nothing is asked of the elements where the
constant is bound.

Asked:

- of C0, the two constructors, as an epoch of the size of the one
  that added static strings: every match on the static constants and
  on what a symbol is bound to;
- of the owner of `FlambdaSimplifyStaticsSpec.v`, the type of the
  symbol of such a constant;
- of V2, its word on the conversion (section 6), which comes as one
  commit of the series of the definitions; the removal from the term
  after of a static binding that nothing mentions (section 4); and,
  when the rewrite of section 4 is proved, its place among the
  normalisations of the term after;
- of the human, the CR of section 3 (a static array is read at any
  load kind that its elements fit).

The order of work: the definitions and their proofs once the heap is
in the state of the machine, as one series that ends with the test
tool; then the rewrite of the term after, with its statement of
equivalence and its laws of renaming and scope.

Answers so far. R5 has read the request, with the outputs of the
measure, and agrees to it as a plan; its three corrections are in
sections 2 and 4 (poison in a table of values, where the rewrite may
fire, which half is left). No definition and no proof has been
reviewed. V2 agrees to the side of the rewrite and to the conversion
of section 6, with the observation of an array as said there.
