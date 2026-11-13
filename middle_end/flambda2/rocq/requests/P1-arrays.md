# P1: arrays, as cells of the heap's prototype

A request and a record: what is written for the mutable arrays of
values, on top of the first step of the heap (`requests/C4-heap.md`,
`FlambdaHeapSpec.v`), what was decided on the way, and what is left
out. The design was agreed with the owner of the heap, who asked that
the changes to the heap's two files be written here and replayed once
over the change that puts the heap in the state of the machine. Not
approved by the owner of the branch: the decisions of section 4 were
taken while he was away, and each has a comment for him (a `CR
mshinwell`) at the definition it is about.

## 1. What OCaml programs use

Twenty-two small units were written for the count and taken through
the front end (`-nopervasives -nostdlib`, the externals declared in
the unit): sixteen with arrays (a literal read, `make` then stores and
loads, a sum by a `for` loop and by recursion, lengths, a swap, a
polymorphic access, an array of strings, unchecked accesses, a local
literal, a fill, a count, a reversal, a maximum, an array of pairs),
four with bytes, and two with a `ref` and a mutable record. In the raw
terms of the sixteen:

| Primitive | Units | Uses | With |
|-----------|-------|------|------|
| `Array_length` | 15 | 33 | `Immediates` 22, `Gc_ignorable_values` 7, `Values` 2, `Float_array_opt_dynamic` 2 |
| `Array_load` | 14 | 22 | `Immediates` 18, `Values` 3, all marked `Mutable`; one of `Naked_floats`, in the branch for floats of a polymorphic access |
| `Make_array` | 14 | 14 | `Mutable`, on the heap: `Immediates` 11, `Values` 3 |
| `Array_set` | 5 | 8 | `Gc_ignorable_values`, which is what the store of an integer into an `int array` is |
| the C function `caml_array_make` | 2 | 2 | `Array.make` |

So a literal of a mutable array is a `Make_array` of its elements; a
checked access is a comparison of the index with `Array_length`, a
raise of `Invalid_argument` and the unchecked `Array_load` or
`Array_set`; and an `int array` is read at the array kind `Immediates`
and written at `Gc_ignorable_values`. No unit of the count has an
array of naked numbers, an immutable array or an array of unboxed
products.

Every unit with bytes starts with the C function `caml_create_bytes`,
so the primitives of bytes (`Bytes_or_bigstring_set` in three units,
the length in three, the load in two) wait for calls of C functions
(`requests/P1-c-calls.md`) and are not here.

## 2. What is written

`FlambdaPrimitiveModel.v`:

- `array_kind`, `array_load_kind`, `array_set_kind`: the three
  constructors of the compiler's that are arrays of values
  (`Immediates`, `Gc_ignorable_values`, `Values`), and
  `array_kind_for_length` (an array kind, or
  `Float_array_opt_dynamic`);
- `Array_length kind`, a unary primitive, and `Array_load kind
  load_kind mut`, a binary one;
- under `Heap`, with the two primitives of blocks that are there:
  `Make_mutable_array kind` (the compiler's `Make_array (kind,
  Mutable, Heap)`) and `Array_set kind set_kind` (ternary).

`FlambdaPrimitiveSpec.v`, the section "Arrays": what the four compute
on the elements of an array, given as a list, with no heap.

- `array_element_ok kind v`: whether an array of the kind holds the
  value (a tagged immediate; anything of kind `Value` for the other
  two kinds).
- `array_made kind vs`: the elements are the arguments, each of which
  the kind holds.
- `array_length_of elements`: the number of elements, a tagged
  immediate.
- `array_loaded load_kind elements index`: the element at the index,
  which is a tagged immediate within the bounds, if the load kind
  takes the element.
- `array_stored set_kind kind elements index new`: the elements with
  the one at the index replaced, if the set kind takes the new value
  and the kind of the array holds it.
- Ten statements: an element is of kind `Value`; the elements made
  are the arguments; the length depends on the number of elements
  only; what is loaded is an element; a store keeps the length and
  puts in nothing but the new value, which the kind holds; a load
  after a store, at the same index and at another; and each of the
  three functions computes on related elements what it computes on
  the elements, for a relation that keeps kinds and integers
  (`relates_numbers`).
- `eval_prim` has no value on `Array_length` and `Array_load`: no
  value of the model is an array.

`FlambdaValueSpec.v`: `cell` has a second form, `Cell_array kind
elements`. It has no mutability: an array with an identity is mutable.

`FlambdaHeapSpec.v`:

- `exec_heap_primitive`: `Make_mutable_array` binds a fresh location
  to the array; `Array_set` replaces the cell by one with the elements
  after the store.
- `exec_unary_on_cell`, of an array: `Array_length`; `Is_null` and
  `Is_int` without `variant_only` answer no; `Opaque_identity` is the
  location; nothing else has a value. `Array_length` has none on a
  block.
- `exec_binary_on_cell`, new, called by `exec_bound_prim` for a
  binary primitive whose first argument is a location, after the case
  of `Phys_equal`: `Array_load` of an array, where its mark is
  `Mutable`.
- `effects_of_prim` and `coeffects_of_prim`, after
  `Flambda_primitive.effects_and_coeffects`: the allocation has only
  generative effects, the store arbitrary ones, the length neither
  effects nor coeffects, the load marked `Mutable` a coeffect.
- `heap_evolves` has a second part: an array stays an array of its
  kind and of as many elements.
- `cell_related` and `values_of_cell` have their case.
- A statement that is new: every primitive keeps the elements of each
  array of the heap among the values that its kind holds
  (`exec_prim_arrays_statement`).
- The laws of the primitives, the simulation and the invariant of
  closed memories are proved with the new cases; no statement of the
  file is changed but through `heap_evolves`.

The proofs are in `FlambdaPrimitiveProofs.v` and
`FlambdaHeapProofs.v`, with examples of each primitive run on a heap.

## 3. What the compiler was read for

- `terms/flambda_primitive.ml`: the kinds of the arguments and of the
  results, `Array_kind.element_kinds`, and the effects and coeffects
  (`reading_from_an_array`, `writing_to_an_array`, the cases of
  `Array_length` and `Make_array`).
- `simplify/simplify_common.ml`, `specialise_array_kind`: an access at
  `Values` or `Gc_ignorable_values` becomes one at `Immediates` where
  the type of the array says immediates; an access at a kind of naked
  numbers is `Invalid` where the type says another kind of element.
- `simplify/simplify_variadic_primitive.ml`, `simplify_make_array`:
  the type of a mutable array is its element kind and its length; a
  `Make_array` that is `Immutable_unique` is a fatal error.
- `simplify/simplify_binary_primitive.ml`, `simplify_array_load`: a
  load at a known index of an immutable array of known length is the
  element, or `Invalid` out of the bounds.
- `simplify/simplify_unary_primitive.ml`, `simplify_array_length`: the
  array kind is not looked at.
- `simplify/simplify_ternary_primitive.ml`, `simplify_array_set`: a
  fatal error if the array kind is still `Values` after
  `specialise_array_kind` and the set kind is not `Values`. Where the
  type of the array says immediates the same store goes through, as
  its array kind is changed first.
- `types/provers.ml`, `prove_is_int_generic_value`: `Is_int` with
  `variant_only` of an array is `Invalid`.
- `from_lambda/lambda_to_flambda_primitives.ml`: which array kind,
  load kind and set kind each access of the source gets, and the
  tests of bounds; `from_lambda/closure_conversion.ml`: a `Pmakearray`
  of no argument is the static empty array.
- `parser/fexpr_prim.ml`: how the primitives are written in fexpr.

## 4. Decided while the owner of the branch was away

Each is in `status/P1.md` under "Decided overnight" with the options
and what a change would cost.

1. An array records the kind it was made at, and a store of a value
   that this kind does not hold has no value. Without it nothing
   justifies the type that Simplify gives a mutable array.
2. A load or a store out of the bounds has no value.
3. `Gc_ignorable_values` holds any value of kind `Value`.
4. `Make_mutable_array` of no argument has no value: the compiler's
   empty array is one static constant.
5. A load marked `Immutable` has no value on an array that has an
   identity.
6. `Array_length` gives the number of elements whatever the kind it
   carries.
7. Only the arrays of values: no naked numbers, so that every value
   in a cell is of kind `Value`.

## 5. What is not here

- Immutable arrays. One is a value with no identity, as an immutable
  block is: a new form of `value`, a static constant
  (`Immutable_value_array`, `Empty_array`), and `eval_prim` on
  `Array_length` and `Array_load` through the functions above. The
  compiler makes the empty array, mutable or not, a static constant.
- Arrays of floats (the float array optimisation makes a polymorphic
  access test `Is_flat_float_array` and read a naked float in one
  branch; `requests/P1-floats.md`), of naked numbers, of vectors, of
  masks and of unboxed products.
- `Array.make` and the other C functions that make or copy arrays,
  `Duplicate_array`, and `%array_to_iarray` and `%array_of_iarray`.
- The conversion of the test tool: it refuses the four primitives, as
  it refuses the two of blocks, until the machine that it runs has a
  heap. Until then no example runs through Simplify; the functions
  and the primitives are checked by examples in the proof files.
- The test of bounds raises `Invalid_argument`, a predefined
  exception: a unit with a checked access needs the imported symbols.
- Bytes (section 1).

## 6. For the replay over the heap's next step

The edits to `FlambdaHeapSpec.v` and `FlambdaHeapProofs.v` are where
the primitives are: `exec_heap_primitive`, `exec_unary_on_cell`,
`exec_binary_on_cell`, `exec_bound_prim`, the two classifications,
`heap_evolves`, `cell_related`, `values_of_cell`, and in the proofs
the laws of effects, `related_exec_*`, `exec_related_allocation` and
`exec_related_write` (now stated of any two related cells),
`exec_prim_closed`, and each proof that went by cases on the one form
of cell. `replace_nth` and its three lemmas moved to
`FlambdaPrimitiveSpec.v` and `FlambdaPrimitiveProofs.v`. Nothing in
`heap_step`, `heap_apply_cont_value` or `heap_call_function` is
touched.

The proofs that go by cases on `cell` are in `FlambdaHeapProofs.v`,
in `FlambdaHeapMachineProofs.v` and, for one lemma, in
`FlambdaHeapEquivarianceProofs.v`
(`outcome_related_code`).

## 7. Added after the review of the first series

In `FlambdaHeapSpec.v`, beside `exec_prim_arrays_statement`, both
proved in `FlambdaHeapProofs.v`:

- `array_length_known_statement`: if `Make_array` of the arguments
  `vs` returned `v`, then in every heap that the one after the
  allocation evolves to, `Array_length` of `v` is
  `array_length_of vs`, whatever array kind it carries. It is what
  `Simplify_unary_primitive.simplify_array_length` does with the type
  that `Simplify_variadic_primitive.simplify_make_array` gives a
  mutable array, which has its length.
- `array_kind_of_access_statement`: the array kind that an
  `Array_length`, an `Array_load` or an `Array_set` carries changes
  nothing of what it does. `Simplify_common.specialise_array_kind`
  replaces `Values` and `Gc_ignorable_values` by `Immediates` in a
  load and in a store where the type of the array says that its
  elements are immediates, and keeps the load kind and the set kind;
  in the model that rewrite changes nothing, on any array.

Examples (`Array_of_a_partial_application`, in
`FlambdaHeapMachineProofs.v`):
an array that holds a partial application that holds the location of
a mutable cell, run on the machine with a heap. The call completed
after a write to the cell returns what the cell holds then. With a
location bound to nothing in place of the cell: `Make_array` refuses
the location itself, and stores a partial application that holds it
(the guard of `exec_prim` is on the arguments themselves); the call
completed is undefined at the load in the body of the function; the
state is not closed, and no state reached from a closed one holds
such a value.
