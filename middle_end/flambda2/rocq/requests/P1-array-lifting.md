# P1: an immutable array lifted to a symbol, and read where it is known

For the source `[: x; y :]` once it is a value of the model: the
term after Simplify has a symbol where the term before has the
`Let` of the array, and a constant where the term before has the
length or an element of an array that it has just made.

For the human, V3 (the lifting), V2 (the rounds of the validation,
the tool and the corpus), and the reviewers R3 (the lifting), R1
(the record), R5 (the primitives) and R6 (the rewrites of the
validation).

Two changes are asked, each a series of its own, the second after
the first. Nothing of either is in this tree. The definitions of
sections 2 and 3 were written and compiled, with no proof, on
a5e4605469, whose `.v` files and tools are those of 3270ad86ed; the
test tool was built with them, and the measures of section 4 were
made with that tool. No statement was proved, and nothing here is a
verdict on any unit.

## 1. Why

The immutable array as a value is in the tree
(`requests/P1-immutable-array-values.md`, `status/P1.md`): the term
before is converted and run. It is seldom validated. Section 4.2
of that request has the case of `lift_named` and the rule from an
array value to a symbol, which its series left out by agreement
with the owner of the lifting; this is their request, with the
measure that the earlier one could not make.

On a set of 135 units written to try immutable arrays as values
(not in this tree), the tool of this tree does not validate 58 at
the default flags and 63 at `-O3`. Read from the two terms that
the tool prints, 43 and 44 of them have an array that is a `Let`
in the term before and a symbol in the term after, or is gone from
the term after with its reads.

## 2. The lifting (the first series)

### 2.1 What Simplify does

`FlambdaLiftSpec.v` says it already, for the three things that
Simplify lifts by the type of the result of a primitive that only
allocates: an immutable block of values, a boxed number, an
immutable array. For the array, read again for this request:

- `simplify/simplify_variadic_primitive.ml`, `simplify_make_array`:
  a `Make_array` at `Immutable` has the type of an immutable array
  of the types of its arguments (`T.immutable_array ~fields`), and
  asks to be reified (`~try_reify:true`).
- `types/reify.ml`, `reify`: such a type whose element kind is
  `Value` is rebuilt as `Immutable_value_array` of its fields where
  each field is a constant, a symbol, or a variable that is defined
  at the toplevel of the unit or is a projection from a symbol
  (`try_to_reify_fields`, as for a block); one of no field as
  `Empty_array`.
- `simplify/lifting/reification.ml`, `create_static_const` and
  `lift`: the symbol is named after the variable, unless an equal
  constant has been lifted already, when the symbol of that one is
  used (`DA.find_shareable_constant`).

So an array made at the toplevel of the unit is lifted with a
variable among its elements too, and an array of symbols and
constants is lifted out of a function or a loop, as a block is.

### 2.2 The definitions

In `FlambdaLiftSpec.v`, as section 4.2 of the earlier request gave
them:

    lift_named, one case more:
      | Lift_to_symbol s,
        Prim (Variadic (Make_immutable_array _)) elements =>
        Some
          ([Bind_symbol s
              (Static_const_immutable_value_array elements)], s)

    value_lifted, one rule more:
      Lifted_to_array:
        lookup s (static_values statics')
        = Some (Static_immutable_array elements') ->
        Forall2 (value_lifted statics') elements elements' ->
        value_lifted statics' (Value_immutable_array elements)
          (Value_symbol s)

Nothing else is defined. The lifting out of code, out of the arms
of a test and to a group around go through `lift_named`
(`FlambdaLiftFromCodeSpec.lifted_out`,
`FlambdaLiftAroundSpec.alias_of`), so they take the array with no
change of their text.

What the case does that the `Let` did not:

- The array kind is dropped: the constant has none. The `Let` has
  no value where an element is not one that its kind holds
  (`FlambdaPrimitiveSpec.array_made`) or is a symbol bound to
  nothing; the binding has a value wherever its elements have. So
  the term lifted is defined where the term was not. That is a
  refinement and no equivalence, and a refinement is what every
  statement of the lifting concludes.
- Two `Let`s of one array may be given one symbol where the
  lifting shares (out of one body of code, or as aliases of a
  symbol bound around them). No array value has an identity in the
  model: `Phys_equal` of two has no value
  (`FlambdaPrimitiveSpec.eval_phys_equal`), so a unit that could
  tell is undefined before it is lifted. The compiler's own choice
  between one symbol and two is by the debugging information of
  the elements; the model has no part in it.
- The empty array: Simplify binds `Empty_array`, which the
  conversion reads as the static immutable array of no element.
  A `Make_immutable_array` of no argument is lifted to it like
  another.

### 2.3 The statement whose text changes

One, in `FlambdaNoArrayValueSpec.v`, a file of this stream. Today:

    value_lifted_array_statement:
      value_lifted statics' (Value_immutable_array elements) v' ->
      exists elements',
        v' = Value_immutable_array elements'
        /\ Forall2 (value_lifted statics') elements elements'

It is false with the rule. It becomes, with the comment before it
("to an array value of its elements lifted, or to a symbol bound
to an immutable array of its elements lifted, and to nothing
else"):

      value_lifted statics' (Value_immutable_array elements) v' ->
      exists elements',
        Forall2 (value_lifted statics') elements elements'
        /\ (v' = Value_immutable_array elements'
            \/ exists s,
                 v' = Value_symbol s
                 /\ lookup s (static_values statics')
                    = Some (Static_immutable_array elements'))

Its conclusion is weaker: this is for the orchestrator, and for R3,
who signed the text that is there. The header of that file says of
it "a rule that did would be a case more of it": that sentence
goes, and the paragraph says what the statement then says.

### 2.4 What each changed definition reaches

Counted by `rocq/check-changed-defs.py` between a5e4605469 and the
definitions of 2.2 alone: no statement added or removed, no
definition added, two definitions whose body changes. (The text
change of 2.3 is not in that count: the prototype kept the
statement as it is.)

`lift_named` reaches 82 statements, all through other definitions
(`lift_expr`, `lift_unit`, `lifted_out`, `lift_from_code`,
`lift_to_head`, `alias_of`, `lift_around`, `with_lifting`,
`lifted_in_turn`, `validate_unit` and what is built on them). The
function gives the bindings of one more form of `Let` where it
gave none. No premise is added to any of them and no conclusion is
lost; each is then a statement about the function as extended, so
the case of the array is new proof in each proof that goes by the
cases of `lift_named` or by the rules of `value_lifted`. A guess
that names no `Let` of an array gives what it gave.

`value_lifted` reaches four statements, each directly:

- `lift_simulates_statement` has it in its conclusion: the values
  at the exit of the term lifted are those of the term up to it.
  The relation relates one more kind of pair, an array value and a
  symbol bound to an array of its elements lifted. That is what
  the statement is for (it says the same of a block, a boxed
  number and a closure), and it is a weaker conclusion: for the
  orchestrator. What it said of a unit that makes no array it
  still says: the run of such a unit holds no array value
  (`FlambdaNoArrayValueSpec.run_free_of_arrays_statement`), the
  new rule has an array value for its first value, as
  `Lifted_array` has, and a derivation goes by the head of the
  first value; `value_lifted_no_array_value_statement` and the
  statement of 2.3 are the two that say so.
- `value_lifted_array_statement`: 2.3.
- `value_lifted_to_array_statement` (nothing but an array value is
  lifted to an array value) and
  `value_lifted_no_array_value_statement` (a value that holds no
  array value is lifted to values that hold none): their texts
  stay and they are true of the relation with the rule; each is
  proved again, with the case.

The statements that a unit lifted refines the unit keep their
checks (`exits_plain`, and that the lifted form is a well-formed
unit): an array value is no plain value, so a unit that could
leave with one is refused as before. The six statements of
`FlambdaLiftObservedSpec.v` are among the 82: no primitive is
added, so what may follow a unit is what it was, and they are
reproved as conclusions.

The law of the primitives that the lifting uses
(`FlambdaPrimitiveSpec.eval_prim_related_statement`) is not
changed: its premise `relates_observations` already asks, of two
related values the first of which is read as an array by
`array_of`, that the second is and that the elements are related,
which the rule gives.

### 2.5 The comments

`FlambdaLiftSpec.v`: the item "immutable arrays" of "What is not
here" goes; "What is here" gains the third form; the paragraph
before `value_lifted` says "and none is made a symbol either" of
an array, which becomes what it says of a block; "Identity" names
the array beside the block. `FlambdaLiftFromCodeSpec.v` and
`FlambdaLiftAroundSpec.v` each list what `lift_named` lifts, and
say why what is shared has no identity: the array is added to
both lists. These three files are the lifting's: the texts are
its owner's to give or to approve.

### 2.6 The test tool

`tests/tools/flsemantics.ml`, in the guess of the lifting, where
there is a case for `Make_block` there is one for
`Make_immutable_array`, three in all: a `Let` at toplevel (elements
that are variables agree with anything, as fields do); a `Let` in
code or in an arm, of symbols and constants only; and the `Let`s
to make aliases of a symbol bound around them. And one filter: the
tables to bind at the head of the term before
(`tables_guess`) are symbols that the term after binds to an
immutable array and the term before does not bind; an array of the
source that the same lifting gives to a `Let` is one of those and
is no table, and with it among the tables the check of
`FlambdaUnusedHeadStaticsSpec.add_head_tables` fails for all of
them. The symbols that the first lifting gives to `Let`s are left
out of its tables.

All of it is a guess: `lift_unit` and its fellows check it, and a
wrong guess is a unit that is not validated. Nothing of the
conversion changes, and nothing of the trust ledger.

### 2.7 Proofs, and who writes them

This stream, with the word of the owner of the lifting on the
patch to its files, as for `Lifted_array`. The case of the array
follows that of the block without its tag: in this tree
`Lifted_to_block` is named in `FlambdaLiftProofs.v` (twice: the
relation under a larger static environment, and the step of a
lifted `Let`), in `FlambdaLiftFromCodeProofs.v` and in
`FlambdaLiftAroundProofs.v` (once each); the other uses are
inversions and constructors found by search. `lift_named` is used
in `FlambdaLiftProofs.v`, `FlambdaLiftFromCodeProofs.v`,
`FlambdaLiftAroundProofs.v` and `FlambdaStaticsScopeProofs.v`.

## 3. The length and the elements of a known array (the second series)

### 3.1 What Simplify does

- `simplify/simplify_unary_primitive.ml`, `simplify_array_length`:
  the length is a projection of the type of the array; where that
  type has the elements, the result is their number, a constant.
- `simplify/simplify_binary_primitive.ml`, `simplify_array_load`:
  where the array is proved an immutable array of known fields
  (`T.prove_is_immutable_array`) and the index is one known tagged
  immediate, the result has the type of that field, reified: the
  element itself where it is a constant, a symbol or a variable;
  `Invalid` where the index is out of the bounds. The mutability
  that the load carries is not looked at.

The type comes from `simplify_make_array` (2.1) and, for a symbol,
from its static constant. So in the term after, the length of an
array that the same code has just made is a constant, the test of
an index against it is decided or is a test against a constant,
and a load at a constant index is the element; an array that is
then unused is gone.

### 3.2 The definitions

New files of this stream, `FlambdaArrayLoad*`, after
`FlambdaBlockLoadSpec.v`, which does the same for the fields of a
block that is known from the term alone. `load_known_arrays` goes
through a term keeping, for a variable bound by a `Let` to
`Make_immutable_array` and for a symbol bound by a `Let_static` to
`Static_const_immutable_value_array`, the elements
(`known_arrays`; an element is forgotten where a variable that it
names is bound again, and the whole entry where the variable
itself is: `FlambdaBlockLoadSpec.forget_field`). Then, of a `Let`
whose defining expression is a primitive on such a variable or
symbol:

- `Array_length _` becomes the number of elements, a tagged
  immediate, if it is in range;
- `Array_load _ _ _` at an index that is a constant tagged
  immediate, at least 0 and below the number of elements, becomes
  the element, if what it holds is still known;
- anything else stays: a load at an index that is a variable, a
  load out of the bounds.

A handler of a non-recursive continuation is gone into, with what
is known where it is defined less its parameters; the handlers of
recursive continuations and the bodies of code are left
(`FlambdaNormaliseSpec.rewrite_code` and the rounds take the pass
into them, with nothing known at the start), as for blocks.

The statements, as for `load_known_blocks`: the result refines the
term under every environment
(`load_known_arrays_refines_statement`: `expr_refines e
(load_known_arrays e)`); it commutes with renaming; it keeps
scope. It is a refinement and no equivalence: the load has no
value where the element is not one that its load kind holds
(`FlambdaPrimitiveSpec.array_loaded`), and the element has. So it
is for the term before only.

### 3.3 Where it goes

In `FlambdaValidateSpec.v`, beside `load_known_blocks` in the two
places that apply it, `normalise_expr_before` and
`normalise_expr_params_knowing`:

    unbox_known_numbers (load_known_arrays (load_known_blocks e))

It is none of `merge_tables`, `unbox_loops_knowing`, `untag_params`
and `give_scrutinees`, and moves none of them: it comes before all
of them in a round where they are, at the place of the load of
blocks. That file is V2's: the two lines are asked of it.

### 3.4 What it reaches

Counted between the definitions of 2.2 and those with 3.2 and 3.3:
one statement added (the refinement; the two others of 3.2 were
not written), 18 definitions added, two changed.
`normalise_expr_before` reaches 39 statements, 10 directly;
`normalise_expr_params_knowing` reaches 43, none directly. The
round of the term before applies one rewrite more; no premise is
added and no conclusion lost, and the proofs that the round
refines, commutes with renaming and keeps scope each gain one
step. Nine of the ten that have `normalise_expr_before` directly
are statements that an example is not validated today
(`..._not_validated_today_statement`, in
`FlambdaUnboxParamsExamplesSpec.v` and
`FlambdaUnboxVariantsExamplesSpec.v`): their terms have no array,
so the rewrite gives them back; they are computed again by the
build. The tenth is `normalise_expr_before_keeps_scope_statement`.

### 3.5 What it does not do

- The length known where two arms meet: each arm gives one
  continuation an array of the same length, and the term after has
  no test of the index after them. That is known by a join of two
  types, or by a pass of the kind that gives a join what is read
  in scope; it is not this.
- The length of an array that the code does not make: one held in
  a value slot of a closure whose every closure is made with an
  array of that length.
- The tests of an index under the arm of a `Switch` on the length.
- A load taken twice: the second is not shared
  (`FlambdaCseSpec.shareable` says no of `Array_load`).
- A load at a constant index out of the bounds of a known array:
  Simplify makes it `Invalid`; here the `Let` stays, with no
  value.

## 4. The measure

Three tools built from one tree, a5e4605469: its own; A, with 2.2
and 2.6; B, with A and 3.2, 3.3. Each row is the number of units
not validated, at the default flags and at `-O3` where there are
two settings.

- The 135 units of section 1: this tree 58 / 63; A 27 / 34; B
  14 / 19.
- 68 units written to try arrays of constants (not in this tree):
  this tree 46 / 46; A 10 / 11; B 2 / 3.

On both sets every unit whose verdict changes goes from not
validated to validated, or to validated with its imports; no unit
goes the other way, and every other row of the counts is as it
was. The lines of the two runs are the same for every unit. One
unit of the first set, undefined in both runs, goes from "nothing
to validate" to a validation that says nothing of it, and stays
counted as undefined.

The examples of the tree (145 terms and 482 OCaml units), by the
test of the tree run with each tool: with A two expected files
move, `ocaml/iarray_literal` (not validated; validated once
lifted) and `ocaml/iarray_phys_equal` (undefined before Simplify:
"nothing to validate" becomes a validation followed by "the term
before is undefined in the model, so the validation says nothing
of this unit"). With B two more: `ocaml/iarray_exported` (not
validated; validated once lifted) and `static_array.fl`
(validated once lifted; validated once normalised). None goes
from validated to anything else.

The census of generated units: with A and with B, none of the 600
outputs and none of the 240 differs from those of the tool of the
tree.

What is left not validated of the 135 with B, by what the two
terms show, default / `-O3`: a table that Simplify makes of a
`Switch` and another static array with the same elements, which
the terms cannot tell apart, 4 / 4; a test made twice, the second
under an arm of the first, 4 / 4 (two of them with a load taken
twice); the length known in code that does not make the array,
2 / 2; the tests of an index under an arm of a `Switch` on the
length, 1 / 1; a length taken twice, 1 / 1; the length known where
two arms meet, 0 / 5; a recursive function made a loop and inlined
at its call, 0 / 1; a `Let` of a constant whose symbol is bound in
the body of its `Let_cont`, and so not around it, 1 / 1; and a
group of constants that Simplify binds under two `Let`s, in a unit
that mentions an import, so that the comparison with the static
bindings first is not made (`FlambdaHoistStaticsSpec.v` says so
of the pass), 1 / 0. The last two were reproduced with blocks and
no array.

## 5. What is decided here, and what is asked

Decided, as the earlier request decided it: the case and the rule
of 2.2 are those of a block without its tag; the array kind is
dropped.

Asked:

1. Of the orchestrator: the weaker conclusions of
   `value_lifted_array_statement` (its text) and of
   `lift_simulates_statement` (by the rule), with 2.4 as their
   record; and whether section 3 is a series of this stream.
2. Of the owner of the lifting: its word on 2.2, on the comments
   of 2.5, and on the patch to its proofs when it is written.
3. Of the owner of the validation: the two lines of 3.3, and the
   filter of 2.6 in the tool.
4. Of the reviewers: R3 the lifting and the statement of 2.3; R1
   the record of 2.4 and 3.4; R5 that the folds of 3.2 are what
   the primitives compute; R6 the pass of section 3 and its place
   in the round.
