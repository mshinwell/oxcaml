# P1: static immutable arrays of values

For the tables that Simplify makes of a match whose arms are
constants.

For the human, C0 (the values and the terms), V2 (the conversion and
the validation) and R5 (review). The definitions of section 3 are in
the model with their proofs, and the conversion of section 6 is in
the test tool; they came after the heap became a part of the state
of the machine. The rewrite of section 4 is not in this tree. The
measure of section 5 was made before, on a prototype of the
definitions with no proof.

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

The statements that change with it, each in a `Spec` file:

- `FlambdaValueSpec.array_of_disjoint_statement`, new: a value that
  `array_of` reads is not a closure, a block, a boxed number or a
  string. It is beside `observations_disjoint_statement`, which is
  as it was.
- `FlambdaPrimitiveSpec.relates_observations` has one conjunct more,
  the last: where `array_of` reads the first of two related values
  it reads the second, and the elements are related one by one. It
  is the conjunct of `block_of` without the tag. The law
  `eval_prim_related_statement` needs it, as a load gives an element
  of the array; the four relations that are instances of the premise
  have it (they are named below).
- `FlambdaPrimitiveSpec.eval_prim_preserves_statement` has one
  hypothesis more, `holds_in_static_arrays`: the property holds of
  the elements of the static array that a symbol with the property
  is bound to. It is `holds_in_static_blocks` for an array, and each
  use of the law gives it as it gives that one.
- `FlambdaHeapSpec.value_step`, which relates the values of two
  runs by their heads, has one rule more, `Step_array`: two values
  that `array_of` reads are related where their elements are, one
  by one. It is the rule of two blocks without the tag.

That is every statement of a `Spec` file whose text changes:
`eval_prim_preserves_statement` changes and
`array_of_disjoint_statement` is new; `relates_observations` and the
relation `value_step` are definitions that change. No other
statement changes its text.

Three laws have a premise that gains a clause for static arrays:

- `eval_prim_related_statement`. Its premise
  `respects_observations` has `relates_observations`, which gains
  the conjunct. `Array_load` needs it: with equality for the
  relation, and one symbol bound to an array in the first static
  environment and to another array in the second, the load would
  give two elements that are not related.
- `FlambdaExtcallSpec.eval_extcall_related_statement`. Its text
  does not change; its premise is the same `respects_observations`,
  so it gains the conjunct too. Its evaluator and its proof read
  constants and strings only, and do not need the conjunct: the two
  laws of related values keep one premise deliberately, so that a
  relation is shown once to respect the observations (decided by
  the orchestrator, who was asked whether to split the premise).
- `eval_prim_preserves_statement`, by the hypothesis
  `holds_in_static_arrays`. `Array_load` needs it: without it the
  load could give, out of an array whose symbol has the property,
  an element that has not.

Each clause is vacuous in a static environment that binds no symbol
to a static array, so there each of the three laws is the law that
was signed, and that is every unit that this tree had before. For
the conjunct, in the first two laws: `array_of` answers `None` of
every value in such an environment. For the hypothesis, in the
third: no lookup there gives `Static_immutable_array`.

The appendix lists every definition of a `Spec` file whose body
changes, with the statements that it reaches, directly or through
other definitions: by name where there are at most 40, by their
number otherwise. They are found by the search of `rocq/HACKING.md`
and not by judgement. Of each definition it says which of three
things happens to the statements that it reaches: their domain
widens and nothing is added; a premise is strengthened; or a
conclusion is weakened.

- A premise is strengthened for `relates_observations` and for
  `holds_in_static_arrays`, which is new: in the three laws above,
  and in no other statement.
- No conclusion is weakened.
- For every other definition the domain widens. Each is a type with
  one more constructor, or a function or a relation by cases that
  answers of the cases it had what it answered: on a term with no
  such constant and a static environment that binds no symbol to a
  static array it is what it was. So a statement that it reaches
  says of those what it said, and says the same of a term or an
  environment that has an array. Three to note: `is_allocated`
  answers yes of a symbol bound to an array, so `Is_int`, `Is_null`
  and `Phys_equal` answer of it as of a symbol bound to a block, and
  `FlambdaImportsSpec.phys_equal_identity_other_statement` says as
  well that an identity is not a static array; `value_step` relates
  two static arrays with related elements, where the rule for a
  symbol that is bound to nothing that is read does not apply to
  them any more; and the cases of `Array_length` and `Array_load`
  give `eval_prim` a value where it had none.

No statement of the validation, of ranges or of kinds gains a
hypothesis. Where a premise of one is a check by cases on the two
types, the check has the case of the array, and on a unit without
one it is the check that it was. Each proof that uses
`eval_prim_preserves` gives the new hypothesis from the fact about
the static environment that gave it the same of a static block. One
is `FlambdaLocationsPrimitiveProofs.eval_prim_locations_bound`: its
premise that the locations of the static environment are bound in
the heap gives it, as the locations of a static array are those of
its elements. Each relation that is given to `eval_prim_related` has
the new conjunct. There are four: equality between a static
environment and the one with value slots dropped,
`FlambdaLiftSpec.value_lifted`, the relation of the heap, and
`FlambdaLocationsPrimitiveProofs.moved`, of a value and the value
with its locations permuted. `eval_prim_moved` uses the last,
between a static environment and the one permuted, and
`moved_respects` shows the conjunct for it: `permute_static_value`
permutes the elements of a static array one by one, so the array
that is read on one side has for elements those of the other,
permuted. Two lemmas of `FlambdaSemanticsProofs.v` on
the arguments of tupled code (`tuple_fields_from_related`,
`arguments_for_code_related`) have `respects_observations` for a
premise. They are used with `value_lifted`
(`FlambdaLiftProofs.v`, `FlambdaLiftFromCodeProofs.v`) and with the
relation of the heap, from the invariant on the two memories that
it had (`FlambdaHeapProofs.related_shape_of_closure_call`), and
each of the two relations is shown to have the conjunct. So nothing
travels up to the theorem of the validation.

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
  and it leaves a binding that the validation cannot account for
  today, which is open ("The binding that is left", below):
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
    states reached from the binding. The machine makes a binding of
    a name that is bound already undefined, which is what should
    give it of every term; whether it holds of every term or only of
    a well-formed one is to be settled when it is stated.
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
  - *The binding that is left. Open.* After the rewrite nothing
    mentions the symbol of the table, and the term before has no
    such binding. The validation removes the static bindings that
    are not used from the term before only, as a refinement
    (`FlambdaUnusedStaticsSpec.v`). Removing one from the term after
    is not an equivalence under every environment, and not even the
    half that a rewrite of the term after owes: a binding of a
    symbol that is bound already is undefined
    (`FlambdaSemanticsSpec.eval_static_bindings`), so under a static
    environment that binds the symbol the term with the binding has
    no value and the term without it may have one. The reviewer
    found it, and ran the case of a static block on the machine. So
    the removal is no normalisation of the term after, and it must
    not come into the two verdicts that hold under every environment
    (`validate_unit_sound_everywhere_statement`). What the owner of
    the validation proposes is a law of a unit run on its own: the
    term after refines, run from empty environments, the term with
    the binding removed, where the validator has checked that
    nothing mentions the symbol, that nothing else binds it, and
    that its constant has a value. It would be used only in the
    comparisons that conclude a refinement of units run on their
    own, as the moves of static bindings on the term after are
    (`FlambdaHoistStaticsSpec.v`, `FlambdaHoistCodeSpec.v`). That
    law and how it composes are stated and reviewed apart, after the
    heap is in the state; nothing here is agreed about them. The
    rewrite validates no unit until then.
- **From the `Switch` to the load, on the term before.** This is
  what Simplify does, beside the two ways that
  `FlambdaMergeSwitchesSpec.merge_switches` has. It has to bind a
  symbol to the table at the head of the unit, from inside code, and
  the symbol has to be the one that the term after has: a guess that
  the tool makes and the validator checks, as for the lifting of a
  block out of a function. It is the dearer of the two.

I recommended the first. Where the first discriminant is not zero the
term after has the index less that discriminant, and the `Switch`
that the rewrite makes is on that difference with the arms from 0,
where the term before tests the scrutinee with the arms from `d`:
one more small rewrite, or the same one reading the `Let` of the
index. None of the four units has it.

**Since the review: the second, in two parts.** The first rewrite
leaves a binding that nothing can take out of the term after, so it
validates no unit. The second can be split so that nothing binds a
symbol from inside code and nothing is taken out of the term after.
The owners of the validation and of `merge_switches` have agreed to
their parts; R5 has given remarks on the design, which the two
parts below take in, and has approved nothing of it. Nothing of it
is in this tree.

- **The binding: a guess that is checked.** The tool proposes the
  term before with one binding more for each table of the term
  after, of the symbol that the term after has to the same
  constant, in a group of static bindings at its head. The
  validator checks that the term proposed, with those bindings
  dropped, is the term before; and what the law that follows
  needs: that the symbols are distinct, that nothing else in the
  term binds or mentions one, and that each constant has a value
  under every environment, which a table has: none of its elements
  is a variable. The law is of the owner of the validation, for a
  unit run on its own: the term with the bindings refines the term
  without them. It is the converse of the removal of static
  bindings that are not used, which the validation applies to the
  term before already, and it is used on the term before only. The
  binding stays in both terms from then on, and the comparison sees
  it.
- **The load: one more way of `merge_switches` for an argument.**
  Beside the ways that `FlambdaMergeSwitchesSpec.v` has of computing
  from the scrutinee an argument that differs from arm to arm, one
  more: the argument is the element of a table at the number of the
  arm. The rewrite is given the tables, a symbol with its elements
  for each. Each arm is tested on its own, as for the other ways:
  it applies the one continuation with no trap action, its number
  is an index of the table, and its argument at that position is
  the element there; and each element that an arm reads is one
  that the load kind takes and is of the kind at which the result
  is bound. The argument is then computed by two `Let`s, the
  tagging of the scrutinee and the `Array_load` of the symbol at
  it, as Simplify builds it. Its statement is a refinement in the
  states whose static environment binds each table given to its
  elements; the head group of the term before, after the guess,
  makes that so for a unit run on its own. With no table given the
  rewrite is `merge_switches` as it is, and its statement stands.
  Which variable the `Let`s bind, and which notion of "refines
  where the static environment has this" the rounds of the
  validation take, are for the owners of `merge_switches` and of
  the validation to say, after the definitions of section 3.

A `Switch` with fewer arms than the table has elements is merged
too. On a scrutinee that is an index of the table and the number of
no arm the `Switch` is undefined and the load is not, which a
refinement allows: so what is asked is the refinement, which is
what a rewrite of the term before owes and what the other ways of
`merge_switches` have, and not an equivalence. R5's remark on the
vector of the arguments is met by the test of each arm: every
argument of every arm that the `Switch` has is preserved, and the
table need not have as many elements as the `Switch` has arms. A
first discriminant that is not zero is left out: I could not make
Simplify produce a table with one, in any of the units written to
try.

This needs of section 3 the constant, `array_of`, `Array_load` of a
symbol bound to the constant, and that the constant has a value
wherever its elements have: all are there.

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
  up to the names bound. So these four need that rewrite and a way
  to account for the binding of the table, which is open (section
  4). This was done on the terms as the tool prints them; the
  validator was not run on the result.
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
  commit of the series of the definitions; its law for the binding
  that the rewrite leaves (section 4, open); and, when the rewrite
  of section 4 is proved, its place among the normalisations of the
  term after;
- of the human, the CR of section 3 (a static array is read at any
  load kind that its elements fit).

The order of work: the definitions and their proofs, as one series
that ends with the test tool (done); then the two parts of the
rewrite of the term before (section 4, "Since the review"), each
with its owner: the guess of the binding with its law, and the
new way of `merge_switches` with its statement of refinement and
its laws of renaming and scope.

Answers so far. R5 has read the request, with the outputs of the
measure, and agrees to it as a plan; its corrections are in sections
2 and 4 (poison in a table of values, where the rewrite may fire,
which half is left, and that the binding left cannot be removed from
the term after as an equivalence). No definition and no proof has
been reviewed, and the agreement does not cover the law for the
binding that is left. V2 agrees to the side of the rewrite and to
the conversion of section 6, with the observation of an array as
said there.

## Appendix: what each changed definition reaches

For section 3. The 50 definitions of a `Spec` file whose body
changes in the commit of the definitions, each with the statements
of the tree in which its name occurs, directly or through other
definitions: the search of `rocq/HACKING.md`, with 40 for the
number above which the statements are counted and not named. A
definition is taken with its file, and a use of a name that two
files define is counted for both, so the search may list too much
for that reason and not too little.

"The domain widens" is said of a type with one more constructor, or
of a function or a relation by cases that answers of the cases it
had what it answered. On a term with no immutable array constant
and a static environment that binds no symbol to a static array it
is what it was; so each statement that it reaches says of those
what it said, and says the same of what has an array. It gains no
hypothesis and loses no conclusion.

Two definitions are new: `array_of` (`FlambdaValueSpec.v`), an
observation, in `array_of_disjoint_statement` and, through
`is_allocated` and `relates_observations`, where those are; and
`holds_in_static_arrays` (`FlambdaPrimitiveSpec.v`), in
`eval_prim_preserves_statement` only, where a premise is
strengthened.

Reaching at most 40 statements:

- `allocated_sets_are` (`FlambdaClosuresSpec.v`): the domain widens.
  Through other definitions in `closure_of_code_statement`,
  `sets_are_kept_statement`.
- `static_const_set_is` (`FlambdaClosuresSpec.v`): the domain widens.
  Through other definitions in `parity_sets_are_statement`,
  `set_of_code_bound_statement`, `sets_are_kept_statement`,
  `sibling_of_code_statement`, `sibling_symbol_of_code_statement`.
- `value_step` (`FlambdaHeapSpec.v`): the domain widens. Through other
  definitions in `heap_expr_refines_equivariant_statement`,
  `heap_refines_equivariant_statement`,
  `outcome_related_equivariant_statement`,
  `aliasing_observed_statement`, `block_and_symbol_related_statement`,
  `boxed_poison_refined_statement`, `closed_state_related_statement`,
  `cse_adjacent_statement`, `delete_unused_let_statement`,
  `delete_write_wrong_statement`, `exchange_lets_statement`,
  `garbage_not_observed_statement`, `heap_refines_reflexive_statement`,
  `heap_run_related_statement`, `lift_block_statement`,
  `lift_closure_of_set_statement`, `lift_closure_statement`,
  `load_known_field_statement`, `location_names_not_observed_statement`,
  `machine_respects_relation_except_statement`,
  `machine_respects_relation_statement`,
  `outcome_equivalent_refines_statement`,
  `outcome_equivalent_symmetric_statement`,
  `outcome_related_reflexive_statement`,
  `outcome_related_transitive_statement`,
  `related_projections_statement`, `states_related_nothing_statement`.
- `values_of_static` (`FlambdaHeapSpec.v`): the domain widens. Through
  other definitions in `heap_expr_refines_equivariant_statement`,
  `closed_state_related_statement`, `cse_adjacent_statement`,
  `delete_unused_let_statement`, `delete_write_wrong_statement`,
  `exchange_lets_statement`, `garbage_not_observed_statement`,
  `heap_refines_reflexive_statement`, `heap_step_closed_statement`,
  `lift_block_statement`, `lift_closure_of_set_statement`,
  `lift_closure_statement`, `load_known_field_statement`,
  `outcome_related_reflexive_statement`, `behaves_permuted_statement`,
  `exec_named_keeps_locations_bound_statement`,
  `no_location_bound_statement`,
  `permute_state_locations_bound_statement`,
  `run_keeps_locations_bound_statement`, `run_permuted_statement`,
  `step_keeps_locations_bound_statement`, `step_permuted_statement`,
  `exec_prim_keeps_locations_bound_statement`, `hidden_entry_statement`,
  `state_locations_nominal_statement`,
  `static_env_locations_nominal_statement`.
- `allocated_closures_bound` (`FlambdaHoistCodeSpec.v`): the domain
  widens. Through other definitions in `let_closures_runs_statement`,
  `closures_in_scope_run_statement`.
- `const_closures_bound` (`FlambdaHoistCodeSpec.v`): the domain widens.
  Through other definitions in
  `closures_in_scope_equivariant_statement`,
  `closures_in_scope_run_statement`,
  `hoist_code_program_equivalent_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`,
  `with_code_first_equivariant_statement`.
- `static_closure_code` (`FlambdaKnownClosuresSpec.v`): the domain
  widens. Through other definitions in
  `call_known_closure_sound_statement`,
  `use_closures_knowing_equivariant_statement`,
  `use_known_closures_equivariant_statement`,
  `use_known_closures_refines_statement`,
  `use_known_closures_keeps_scope_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `lifted_in_turn_equivariant_up_to_statement`,
  `lifted_in_turn_keeps_scope_statement`,
  `normalise_lifted_equivariant_up_to_statement`,
  `normalise_lifted_keeps_scope_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`.
- `static_closure_made` (`FlambdaKnownClosuresSpec.v`): the domain
  widens. Through other definitions in
  `use_closures_knowing_equivariant_statement`,
  `use_known_closures_equivariant_statement`,
  `use_known_closures_refines_statement`,
  `use_known_closures_keeps_scope_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `lifted_in_turn_equivariant_up_to_statement`,
  `lifted_in_turn_keeps_scope_statement`,
  `normalise_lifted_equivariant_up_to_statement`,
  `normalise_lifted_keeps_scope_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`.
- `static_closure_slots` (`FlambdaKnownClosuresSpec.v`): the domain
  widens. Through other definitions in
  `read_slot_named_sound_statement`,
  `use_closures_knowing_equivariant_statement`,
  `use_known_closures_equivariant_statement`,
  `use_known_closures_refines_statement`,
  `use_known_closures_keeps_scope_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `lifted_in_turn_equivariant_up_to_statement`,
  `lifted_in_turn_keeps_scope_statement`,
  `normalise_lifted_equivariant_up_to_statement`,
  `normalise_lifted_keeps_scope_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`.
- `allocated_slots_known` (`FlambdaKnownSlotsSpec.v`): the domain
  widens. Through other definitions in `read_slot_sound_statement`,
  `slots_as_kept_statement`.
- `static_const_slots_made` (`FlambdaKnownSlotsSpec.v`): the domain
  widens. Through other definitions in
  `read_known_slots_equivariant_statement`,
  `read_known_slots_in_scope_statement`,
  `read_known_slots_out_of_scope_statement`,
  `read_known_slots_program_refines_statement`,
  `read_known_slots_reads_statement`,
  `read_known_slots_variable_statement`,
  `read_slots_program_refines_statement`,
  `read_slots_slots_as_statement`, `slots_as_kept_statement`,
  `read_known_slots_keeps_scope_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `lifted_in_turn_equivariant_up_to_statement`,
  `lifted_in_turn_keeps_scope_statement`,
  `normalise_lifted_equivariant_up_to_statement`,
  `normalise_lifted_keeps_scope_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`.
- `closed_static_const` (`FlambdaKnownSymbolsSpec.v`): the domain
  widens. Through other definitions in
  `fold_known_unit_program_refines_statement`,
  `with_known_keeps_scope_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `lifted_in_turn_equivariant_up_to_statement`,
  `lifted_in_turn_keeps_scope_statement`,
  `normalise_lifted_equivariant_up_to_statement`,
  `normalise_lifted_keeps_scope_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`,
  `with_known_equivariant_statement`.
- `permute_static_value` (`FlambdaLocationsSpec.v`): the domain widens.
  Through other definitions in `behaves_permuted_statement`,
  `exec_named_permuted_statement`,
  `permute_state_locations_bound_statement`, `run_permuted_statement`,
  `step_permuted_statement`, `eval_prim_permuted_statement`,
  `exec_prim_permuted_exactly_statement`,
  `exec_prim_permuted_statement`, `hidden_entry_statement`,
  `permute_state_inverse_statement`, `rename_permute_state_statement`,
  `state_locations_nominal_statement`,
  `static_env_locations_nominal_statement`.
- `static_closure_of_is` (`FlambdaMyClosureSpec.v`): the domain widens.
  Through other definitions in `lift_simulates_statement`,
  `lift_unit_program_refines_statement`,
  `bind_my_closures_only_closure_statement`,
  `only_closure_of_equivariant_statement`,
  `only_closure_sound_statement`, `with_lifting_keeps_scope_statement`,
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
- `var_free_in_static_const` (`FlambdaNominalSpec.v`): the domain
  widens. Through other definitions in
  `alpha_equivalent_free_names_statement`,
  `var_free_equivariant_statement`, `inline_let_code_statement`,
  `inline_statement`, `var_free_agrees_statement`,
  `var_free_among_statement`, `unused_let_statement`,
  `inline_tupled_equivalent_statement`, `inline_tupled_statement`.
- `static_binding_in_scope` (`FlambdaNormaliseSpec.v`): the domain
  widens. Through other definitions in
  `inline_calls_equivariant_statement`,
  `expr_in_scope_agrees_statement`,
  `inline_sibling_calls_equivariant_statement`,
  `inline_sibling_calls_refines_statement`,
  `inline_calls_refines_statement`,
  `inline_known_calls_equivalent_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `inline_calls_keeps_scope_statement`,
  `inline_sibling_calls_keeps_scope_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `expr_in_scope_equivariant_statement`,
  `inlinable_b_equivariant_statement`,
  `inline_known_calls_equivariant_statement`,
  `lifted_in_turn_equivariant_up_to_statement`,
  `lifted_in_turn_keeps_scope_statement`,
  `normalise_after_equivariant_statement`,
  `normalise_before_equivariant_up_to_statement`,
  `normalise_before_keeps_scope_statement`,
  `normalise_before_round_equivariant_up_to_statement`,
  `normalise_before_round_keeps_scope_statement`,
  `normalise_lifted_equivariant_up_to_statement`,
  `normalise_lifted_keeps_scope_statement`,
  `tupled_inlinable_b_equivariant_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`.
- `symbols_of` (`FlambdaNormaliseSpec.v`): the domain widens. Through
  other definitions in `inline_known_calls_equivalent_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `inline_known_calls_equivariant_statement`,
  `normalise_after_equivariant_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`.
- `allocated_in_range` (`FlambdaPrimitiveSpec.v`): the domain widens.
  Directly in `eval_prim_in_range_statement`; through other definitions
  in `handler_refines_from_in_range_statement`,
  `let_cont_handler_refines_in_range_statement`,
  `blocks_in_range_statement`, `integers_in_range_statement`,
  `run_in_range_statement`, `step_in_range_statement`,
  `well_formed_in_range_statement`,
  `in_range_blocks_have_tags_statement`.
- `relates_observations` (`FlambdaPrimitiveSpec.v`): a premise is
  strengthened (the two laws of related values, section 3). Through
  other definitions in `eval_extcall_related_statement`,
  `eval_prim_related_statement`.
- `allocated_statics_among` (`FlambdaStaticsInScopeSpec.v`): the domain
  widens. Through other definitions in `statics_bound_in_run_statement`.
- `static_const_statics_in_scope` (`FlambdaStaticsInScopeSpec.v`): the
  domain widens. Through other definitions in
  `hoist_statics_program_equivalent_statement`,
  `read_known_slots_in_scope_statement`,
  `read_known_slots_out_of_scope_statement`,
  `read_slots_in_scope_statement`,
  `branch_round_binding_reads_unbound_statement`,
  `rebound_unit_exn_reads_unbound_statement`,
  `statics_bound_in_run_statement`,
  `with_statics_first_keeps_scope_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`,
  `with_statics_first_renamed_alike_statement`.
- `static_const_total` (`FlambdaUnusedHeadStaticsSpec.v`): the domain
  widens. Through other definitions in
  `drop_head_statics_program_refines_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`,
  `without_head_statics_equivariant_statement`.
- `drop_slots_static_const` (`FlambdaUnusedSlotsSpec.v`): the domain
  widens. Through other definitions in
  `drop_slots_keeps_scope_statement`,
  `without_slots_keeps_scope_statement`,
  `drop_slots_equivariant_statement`,
  `drop_slots_slots_unused_statement`,
  `drop_unused_slots_program_refines_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`,
  `without_slots_equivariant_statement`.
- `allocated_free_of` (`FlambdaUnusedStaticsSpec.v`): the domain widens.
  Through other definitions in `lift_block_statement`,
  `lift_closure_of_set_statement`, `lift_closure_statement`,
  `drop_statics_refines_statement`,
  `envs_free_of_equivariant_statement`.
- `static_const_avoids` (`FlambdaUnusedStaticsSpec.v`): the domain
  widens. Through other definitions in
  `heap_step_code_free_of_statement`, `lift_block_statement`,
  `lift_closure_of_set_statement`, `lift_closure_statement`,
  `machine_respects_relation_except_statement`,
  `without_statics_keeps_scope_statement`,
  `drop_head_statics_program_refines_statement`,
  `drop_statics_program_refines_statement`,
  `drop_statics_refines_statement`,
  `validate_unit_knowing_sound_imports_statement`,
  `validate_unit_sound_imports_statement`,
  `validate_unit_knowing_equivariant_statement`,
  `validate_unit_knowing_sound_everywhere_statement`,
  `validate_unit_knowing_sound_statement`,
  `validate_unit_sound_everywhere_statement`,
  `validate_unit_sound_statement`, `drop_statics_equivariant_statement`,
  `envs_free_of_equivariant_statement`,
  `expr_avoids_equivariant_statement`,
  `validate_unit_equivariant_statement`,
  `validate_unit_renamed_alike_statement`,
  `without_head_statics_equivariant_statement`,
  `without_statics_equivariant_statement`.
- `allocated_well_kinded` (`FlambdaWellKindedSpec.v`): the domain
  widens. Through other definitions in `run_well_kinded_statement`,
  `step_well_kinded_statement`, `well_kinded_exit_statement`,
  `well_kinded_no_kind_fault_statement`,
  `well_kinded_unit_state_statement`.
- `simples_of_static_const` (`FlambdaWellKindedSpec.v`): the domain
  widens. Through other definitions in
  `well_kinded_no_kind_fault_statement`,
  `well_kinded_unit_never_faults_statement`.
- `static_const_well_kinded` (`FlambdaWellKindedSpec.v`): the domain
  widens. Directly in `static_const_well_kinded_equivariant_statement`;
  through other definitions in `examples_well_formed_statement` of
  `FlambdaPartialApplicationSpec.v`, `examples_well_formed_statement` of
  `FlambdaTupledSpec.v`, `well_kinded_equivariant_statement`,
  `well_kinded_unit_equivariant_statement`, `run_well_kinded_statement`,
  `step_well_kinded_statement`, `well_kinded_exit_statement`,
  `well_kinded_no_kind_fault_statement`,
  `well_kinded_unit_exits_statement`,
  `well_kinded_unit_never_faults_statement`,
  `well_kinded_unit_state_statement`.

Reaching more than 40 statements:

- `canonical_static_const` (`FlambdaAliasesSpec.v`; the name is also
  defined in `FlambdaEnvAliasesFollowSpec.v`, and a use of it is counted
  for each): the domain widens. Through other definitions in 84
  statements.
- `free_variables_of_static_const` (`FlambdaBindersSpec.v`): the domain
  widens. Directly in `closed_code_free_names_statement`; through other
  definitions in 213 statements.
- `allocated_valid` (`FlambdaClosuresSpec.v`): the domain widens.
  Directly in `eval_static_const_valid_statement`; through other
  definitions in 167 statements.
- `static_const_eqb` (`FlambdaCompareSpec.v`): the domain widens.
  Through other definitions in 83 statements.
- `canonical_static_const` (`FlambdaEnvAliasesFollowSpec.v`; the name is
  also defined in `FlambdaAliasesSpec.v`, and a use of it is counted for
  each): the domain widens. Through other definitions in 84 statements.
- `static_closure_of_binding` (`FlambdaEnvAliasesFollowSpec.v`): the
  domain widens. Through other definitions in 86 statements.
- `static_const` (`FlambdaModel.v`): the domain widens. Directly in
  `eval_static_const_valid_statement`,
  `call_known_closure_sound_statement`,
  `read_slot_named_sound_statement`,
  `add_static_bindings_defined_symbols_statement`,
  `add_static_bindings_invariant_statement`,
  `add_static_bindings_well_formed_statement`,
  `static_const_type_in_rename_statement`,
  `static_const_type_in_scope_statement`,
  `static_const_typed_statement`,
  `symbol_typed_env_satisfies_statement`,
  `static_const_well_kinded_equivariant_statement`; through other
  definitions in 2243 statements.
- `rename_static_const` (`FlambdaNominalSpec.v`): the domain widens.
  Directly in `static_const_type_in_rename_statement`,
  `static_const_well_kinded_equivariant_statement`; through other
  definitions in 318 statements.
- `var_in_static_binding` (`FlambdaNormaliseSpec.v`): the domain widens.
  Through other definitions in 164 statements.
- `eval_binary_primitive` (`FlambdaPrimitiveSpec.v`): the domain widens.
  Directly in `imported_not_read_statement`,
  `phys_equal_same_statement`; through other definitions in 532
  statements.
- `eval_unary_primitive` (`FlambdaPrimitiveSpec.v`): the domain widens.
  Directly in `imported_not_read_statement`; through other definitions
  in 532 statements.
- `variables_in_static_const` (`FlambdaRenameApartSpec.v`): the domain
  widens. Through other definitions in 74 statements.
- `eval_static_const` (`FlambdaSemanticsSpec.v`): the domain widens.
  Directly in `eval_static_const_valid_statement`,
  `call_known_closure_sound_statement`,
  `read_slot_named_sound_statement`,
  `static_closure_of_set_made_statement`,
  `static_const_typed_statement`,
  `symbol_typed_env_satisfies_statement`; through other definitions in
  452 statements.
- `is_closure_const` (`FlambdaSimplifyStaticsSpec.v`; the name is also
  defined in `FlambdaStaticsInScopeSpec.v`, and a use of it is counted
  for each): the domain widens. Through other definitions in 69
  statements.
- `static_const_simples` (`FlambdaSimplifyStaticsSpec.v`): the domain
  widens. Through other definitions in 64 statements.
- `static_const_type` (`FlambdaSimplifyStaticsSpec.v`): the domain
  widens. Through other definitions in 64 statements.
- `is_closure_const` (`FlambdaStaticsInScopeSpec.v`; the name is also
  defined in `FlambdaSimplifyStaticsSpec.v`, and a use of it is counted
  for each): the domain widens. Through other definitions in 69
  statements.
- `is_allocated` (`FlambdaValueSpec.v`): the domain widens. Directly in
  `phys_equal_identity_other_statement`; through other definitions in
  550 statements.
- `statically_allocated_value` (`FlambdaValueSpec.v`): the domain
  widens. Directly in `eval_static_const_valid_statement`,
  `eval_extcall_statics_extend_statement`,
  `call_known_closure_sound_statement`,
  `read_slot_named_sound_statement`,
  `fold_function_slot_sound_statement`,
  `fold_known_apply_sound_statement`,
  `fold_known_named_sound_statement`, `eval_prim_in_range_statement`,
  `eval_prim_statics_extend_statement`,
  `static_closure_of_set_made_statement`, `step_values_all_statement`,
  `static_const_typed_statement`,
  `symbol_typed_env_satisfies_statement`; through other definitions in
  1985 statements.
- `static_const_in_range` (`FlambdaWellFormedSpec.v`): the domain
  widens. Through other definitions in 55 statements.
- `static_set_code_ids` (`FlambdaWellFormedSpec.v`): the domain widens.
  Through other definitions in 67 statements.
- `static_set_whole` (`FlambdaWellFormedSpec.v`): the domain widens.
  Directly in `eval_static_const_valid_statement`; through other
  definitions in 67 statements.
