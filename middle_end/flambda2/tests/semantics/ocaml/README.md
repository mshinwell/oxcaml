# Units made from OCaml sources

Each `X.ml` here is a small OCaml program. `X.fl` is the Flambda 2 term
that the compiler makes of it for Simplify, and `X.expected` is what the
test tool (`../../tools/flsemantics.ml`) says of that term: it runs
Simplify on it, runs the term before and the term after on the machine
extracted from the Rocq semantics, and asks the extracted validator
whether the term after refines the term before
(`rocq/HACKING.md`, "Testing Simplify against the semantics").

## How a term is made

    sh from_ocaml.sh <ocamlopt> X.ml X.fl

which is, in a directory of its own,

    ocamlopt -nopervasives -nostdlib -stop-after middle_end -c \
      [X.mli] X.ml -drawfexpr-to X.fl

and then

    flsemantics.exe X.fl

The dune rules of this directory do both for every `X.ml` (with the
compiler that builds the tool, which is built from the same sources),
compare the term made with `X.fl` and what the tool prints with
`X.expected`, and fail on a difference:

    dune build --root=. --workspace=duneconf/main.ws \
      @middle_end/flambda2/tests/semantics/runtest

- `-drawfexpr` prints the unit after the conversion from Lambda (closure
  conversion) and before Simplify. The tool runs Simplify itself, with
  the default flags, on what the parser reads back.
- `-nopervasives -nostdlib`: the unit refers to no other unit, so each
  source declares the primitives it uses (`external ( + ) : int -> int ->
  int = "%addint"`). This changes nothing in what the front end makes of
  an expression.
- `X.mli` exports `result` only, in most units. A function that the
  unit exports is a field of the module block, and Simplify makes its
  closure a symbol; the units named `..._exported.ml` are about
  that.
- A function whose inlining an example is about has `[@inline]`: with
  the default flags Simplify inlines only the smallest functions.
- The sources are formatted by `ocamlformat`, as `make fmt` wants, but
  for the two that have unboxed tuples, which it does not read
  (`.ocamlformat-ignore`).

## What the conversion does to a unit

The test tool converts the compiler's term to a term of the model
(`../../tools/flsemantics.ml`; it is trusted, and
`rocq/TRUST-LEDGER.md` lists it). Three things it does matter to a
unit made from OCaml.

- **Regions.** Where a block, a boxed number or a closure does not
  escape, the compiler allocates it on the stack, in a region that it
  opens and closes around the expression (`Begin_region`,
  `End_region`). The model has no regions and frees nothing. The
  conversion drops the opening of a region, makes its closing return
  the unit value, and converts what is allocated in it as if it were on
  the heap. That is right for a unit in which nothing allocated in a
  region is used after the region has ended, which the modes of the
  type checker are there to ensure and nothing in the middle end
  checks. It is assumed of the unit after Simplify as of the unit
  before: a validation does not establish that Simplify keeps the uses
  of a local allocation within the life of its region (discrepancy
  V2-3). The regions around a `try` are dropped in the same way: the
  handler ends the regions that the body had open when it raised, and
  nothing allocated in one of them is assumed to be used after that.
  `match_variant_local.ml` is `match_variant.ml` without the type
  annotation that keeps the argument of its function on the heap; both
  are validated. Other early examples have such an annotation for the
  same reason.
- **Depths.** The depth variables of recursion, and the coercions that
  mention them, are dropped.
- **Poison.** Where two branches meet with a variant, Simplify unboxes
  it and gives the fields that a branch has not got the constant
  `poison`. The conversion makes it the poison constant of the model
  (`FlambdaModel.Poison`), of the kind it carries; the unit is then run
  and compared like any other (`option_join.ml`).
- **Tupled functions.** `let f (a, b) = ...` may be compiled as code
  that takes the two components, with a mark that says a call of
  unknown arity gives it the pair. The model has not got the mark. A
  unit that has such code and a call that is not direct is refused
  (`tupled_function.ml`), which is more than is needed; one whose calls
  are all direct is converted, as they give the components
  (`nested_tuple.ml`).

## What the verdicts mean

- **validated**: the extracted `validate_unit` accepted the pair. By
  `FlambdaValidateSpec.validate_unit_sound`, the unit after Simplify
  refines the unit before, run on its own from empty environments. This
  is a theorem about this compilation. It rests on what
  `rocq/TRUST-LEDGER.md` lists (the conversion of the compiler's terms
  to the model's) and, for a unit made from OCaml, on the printing of
  `-drawfexpr` and the fexpr parser: what is validated is the term the
  parser reads back, which is the term the compiler simplifies only as
  far as printing and parsing lose nothing.
  What the theorem observes at the exit is the continuation and its
  arguments, here the symbol of the unit; the contents of the module
  block are not part of the statement.
  Where the verdict says that closures and blocks were lifted to
  symbols, the validator first made static bindings, in the term
  before, of the `Let`s that Simplify lifted
  (`FlambdaLiftSpec.lift_unit`, under the conditions of that file: one
  is that the unit exits with constants and symbols only). The theorem
  is the same one.
- **the same, not validated**: the two runs came to the same result,
  which is a test of one run and no proof. The validator could not make
  the two terms the same; the table says what it is missing.
- **nothing to validate, as the term before is undefined**: the machine
  has no step somewhere in the run of the term before, so anything
  refines it and a validation would say nothing. The compiler runs
  these programs: the model is what lacks something, and the table
  says what. Such a unit is not counted as validated; where the
  validator accepts one all the same, the tool says so on a line of its
  own.
- **not checked**: the conversion refused the unit, as it has something
  the model has not got.

## The examples

Each source begins with a comment that says what it shows and what
Simplify does to it. Steps are those of the machine, before and after
Simplify. The names in brackets are the streams whose work in progress
is the rewrite that is missing.

219 sources: 179 validated, 34 compared on one run and not validated, 2
undefined in the model, 4 not checked.

### Validated

| Source | Steps | Source | Steps |
|--------|-------|--------|-------|
| `add3_exported.ml` | 9, 6 | `int64_join.ml` | 26, 1 |
| `add_zero.ml` | 8, 2 | `int64_of_int.ml` | 25, 7 |
| `apply_exported.ml` | 8, 4 | `int64_overflow.ml` | 33, 1 |
| `bitwise_unknown.ml` | 14, 7 | `int64_shift.ml` | 21, 8 |
| `bool_not_unknown.ml` | 8, 3 | `int64_to_int32.ml` | 10, 6 |
| `bool_ops.ml` | 47, 1 | `int_of_char.ml` | 8, 3 |
| `bswap_constants.ml` | 29, 2 | `int_switch.ml` | 31, 1 |
| `char_code.ml` | 13, 3 | `is_even.ml` | 29, 1 |
| `char_match.ml` | 48, 1 | `labelled_arguments.ml` | 13, 3 |
| `clamp.ml` | 49, 1 | `labelled_optional.ml` | 38, 6 |
| `closed_mutual_recursion.ml` | 66, 35 | `length_exported.ml` | 8, 3 |
| `closure_argument_exported.ml` | 12, 7 | `let_polymorphism.ml` | 27, 1 |
| `closure_argument_used.ml` | 14, 3 | `list_head.ml` | 41, 3 |
| `closure_capture.ml` | 31, 4 | `list_map.ml` | 132, 95 |
| `closure_from_pair_exported.ml` | 9, 4 | `list_sum.ml` | 61, 42 |
| `closure_from_pair_used.ml` | 16, 3 | `local_call_exported.ml` | 8, 4 |
| `closure_in_tuple.ml` | 33, 5 | `local_call_used.ml` | 10, 3 |
| `compare_ints.ml` | 113, 1 | `local_function.ml` | 29, 5 |
| `compare_signed.ml` | 31, 1 | `match_guard.ml` | 52, 1 |
| `compare_unknown.ml` | 9, 4 | `match_unknown.ml` | 18, 10 |
| `compose.ml` | 29, 4 | `match_variant.ml` | 66, 7 |
| `compose_exported.ml` | 8, 4 | `match_variant_local.ml` | 72, 7 |
| `constant_exported.ml` | 8, 4 | `max_exported.ml` | 8, 4 |
| `constant_folding.ml` | 31, 1 | `min_max.ml` | 25, 1 |
| `conv_truncate.ml` | 45, 1 | `module_alias.ml` | 34, 5 |
| `curry.ml` | 36, 3 | `mutual_recursion.ml` | 130, 70 |
| `div_const.ml` | 26, 5 | `nativeint_arith.ml` | 25, 8 |
| `div_unknown.ml` | 16, 8 | `negate.ml` | 10, 5 |
| `enum_to_int.ml` | 19, 1 | `nested_record.ml` | 23, 3 |
| `exported_after_effect.ml` | 15, 6 | `nested_tuple.ml` | 24, 4 |
| `exported_and_used.ml` | 14, 6 | `not_inlined.ml` | 21, 17 |
| `exported_apply.ml` | 18, 9 | `num_conversions.ml` | 27, 19 |
| `exported_bool.ml` | 11, 7 | `option_bind.ml` | 89, 1 |
| `exported_branch_pair.ml` | 15, 10 | `option_default.ml` | 32, 3 |
| `exported_branch_then_fun.ml` | 14, 8 | `option_map.ml` | 70, 4 |
| `exported_branch_two_funs.ml` | 17, 11 | `option_map_exported.ml` | 8, 4 |
| `exported_capture.ml` | 16, 5 | `or_null_known.ml` | 23, 1 |
| `exported_chain.ml` | 14, 10 | `or_null_unknown.ml` | 16, 6 |
| `exported_compose_kept.ml` | 17, 13 | `or_pattern.ml` | 49, 1 |
| `exported_curried.ml` | 14, 6 | `over_application.ml` | 19, 3 |
| `exported_fun_branch_fun.ml` | 17, 11 | `overflow_wrap.ml` | 19, 1 |
| `exported_fun_given.ml` | 9, 7 | `partial_application.ml` | 23, 3 |
| `exported_fun_in_option.ml` | 9, 8 | `phys_equal_unknown.ml` | 9, 4 |
| `exported_fun_returned.ml` | 9, 7 | `physical_equality.ml` | 32, 1 |
| `exported_fun_to_map.ml` | 12, 9 | `pipeline.ml` | 23, 5 |
| `exported_function.ml` | 14, 6 | `polymorphic_variant.ml` | 77, 4 |
| `exported_funs_given.ml` | 10, 10 | `power.ml` | 147, 99 |
| `exported_funs_in_pair.ml` | 14, 11 | `projections_exported.ml` | 11, 7 |
| `exported_list.ml` | 9, 5 | `record_exported.ml` | 11, 7 |
| `exported_local_fun.ml` | 8, 4 | `record_of_functions.ml` | 51, 10 |
| `exported_local_never.ml` | 9, 7 | `record_project.ml` | 37, 8 |
| `exported_made.ml` | 14, 6 | `record_update.ml` | 27, 4 |
| `exported_match_then_fun.ml` | 21, 12 | `ref_local.ml` | 132, 79 |
| `exported_nested_pair.ml` | 10, 7 | `ref_straight.ml` | 13, 4 |
| `exported_record.ml` | 23, 9 | `result_map.ml` | 44, 3 |
| `exported_record_update.ml` | 14, 6 | `returned_closure_of_pair.ml` | 71, 50 |
| `exported_some_again.ml` | 26, 6 | `seq_unit.ml` | 13, 2 |
| `exported_string_length.ml` | 8, 5 | `shift_edges.ml` | 23, 1 |
| `exported_table.ml` | 13, 8 | `shift_unknown.ml` | 17, 7 |
| `exported_twice_kept.ml` | 14, 10 | `shifts.ml` | 22, 8 |
| `exported_two_branches.ml` | 23, 15 | `sign.ml` | 27, 1 |
| `exported_two_functions.ml` | 22, 10 | `string_const.ml` | 21, 2 |
| `exported_two_values.ml` | 18, 1 | `string_get16.ml` | 10, 5 |
| `exported_variant.ml` | 17, 6 | `string_get16_be.ml` | 16, 6 |
| `fact_exported.ml` | 8, 3 | `string_get16_checked.ml` | 29, 17 |
| `factorial.ml` | 70, 46 | `string_get32.ml` | 23, 11 |
| `fib.ml` | 2041, 1417 | `string_get_const.ml` | 9, 4 |
| `first_class_module.ml` | 22, 4 | `string_length_const.ml` | 8, 1 |
| `float_const.ml` | 15, 4 | `string_length_unknown.ml` | 9, 5 |
| `for_down.ml` | 79, 40 | `submodule.ml` | 27, 1 |
| `for_if.ml` | 165, 96 | `succ_pred.ml` | 12, 5 |
| `for_nested.ml` | 171, 95 | `swap_exported.ml` | 8, 4 |
| `for_sum.ml` | 135, 81 | `tree_root.ml` | 90, 4 |
| `for_two_refs.ml` | 90, 52 | `tuple_match.ml` | 75, 1 |
| `fst_snd.ml` | 16, 3 | `tuple_return.ml` | 20, 5 |
| `functor_apply.ml` | 23, 1 | `tuple_swap.ml` | 19, 4 |
| `gadt_known.ml` | 35, 4 | `twice_inlined.ml` | 19, 6 |
| `higher_order.ml` | 32, 5 | `unboxed_pair.ml` | 13, 4 |
| `id_exported.ml` | 8, 4 | `unboxed_pair_argument.ml` | 10, 3 |
| `identity.ml` | 22, 3 | `uncaught_raise.ml` | 10, 4 |
| `if_unknown.ml` | 13, 6 | `unit_argument.ml` | 18, 1 |
| `ignore_value.ml` | 11, 2 | `variant_match_exported.ml` | 8, 4 |
| `indirect_call.ml` | 13, 9 | `while_const_after.ml` | 70, 45 |
| `inline_function.ml` | 20, 4 | `while_countdown.ml` | 61, 34 |
| `inline_record.ml` | 45, 7 | `while_if_inside.ml` | 161, 106 |
| `int32_arith.ml` | 27, 8 | `while_loop.ml` | 78, 45 |
| `int32_overflow.ml` | 40, 1 | `while_nested.ml` | 188, 127 |
| `int32_unknown.ml` | 17, 7 | `while_sum_down.ml` | 133, 80 |
| `int64_boxed.ml` | 22, 8 | `while_two_loops.ml` | 126, 81 |
| `int64_compare.ml` | 48, 1 | | |

### What the validation of a unit that exports a function rests on

Of the validated units, those that export a function are validated
through the lifting of closures and blocks to symbols in the term
before. What each shows, and what its validation uses besides:

| Source | What Simplify does | What the validation uses |
|--------|--------------------|--------------------------|
| `exported_function.ml` | inlines the call; the exported closure becomes a symbol | the closure lifted to a symbol in the term before |
| `exported_two_functions.ml` | two exported functions, the second calling the first: inlines the calls, makes both closures symbols, and removes from the second the value slot that held the first | the closures lifted to symbols and the unused value slot removed in the term before |
| `exported_table.ml` | an exported function that reads a field of a constant pair of the module, the field being a function: the code of the function, which stays, returns the symbol of that function, and the value slot that held the pair is removed | the closures and the pair lifted to symbols, the projection of the pair from the closure and the load from the pair folded in the code, and the unused value slot removed |
| `exported_capture.ml` | an exported function that uses a value of the module computed when the module runs: its closure becomes a symbol that holds the value in a value slot, its code is bound after the value is computed, and where the function is inlined the slot is read as the variable | the closure lifted to a symbol, the value slot read from the static closure, and the bindings of code moved up in both terms |
| `exported_apply.ml` | an exported function given to another exported function: inlines both calls; the call of the argument, once the first is inlined, is a call of the symbol of the function | the closures lifted to symbols and the indirect call of the symbol made a direct call of its code, which is then inlined |
| `exported_made.ml` | a pair made by an exported function that is called when the module runs: inlines the call, and makes the pair that the inlined call makes a symbol | in two liftings: the closure of the function in the term before as given, then the pair in the term that this gives once normalised |
| `exported_record.ml` | a record made by one exported function and read by another, both called when the module runs with an argument that is not known; the closures of the two functions become symbols | closures and blocks lifted to symbols in the term before |
| `exported_variant.ml` | a value of a variant type made when the module runs, with an argument that is not known, and an exported function that tests it, called on that value; the block and the closure become symbols | closures and blocks lifted to symbols in the term before |
| `exported_list.ml` | a list of three elements whose head is not known until the module runs; its cells become symbols | closures and blocks lifted to symbols in the term before |
| `exported_local_fun.ml` | an exported function with a function of its own inside, which it calls; its closure becomes a symbol | closures and blocks lifted to symbols in the term before |
| `exported_curried.ml` | an exported function of two arguments, called with both when the module runs | closures and blocks lifted to symbols in the term before |
| `exported_nested_pair.ml` | a constant pair of pairs, and an exported function that reads a field of a field of it | closures and blocks lifted to symbols in the term before, and the loads from the constants of the module folded in the code of the function |
| `exported_funs_in_pair.ml` | two functions in a pair, and an exported function that calls the first | closures and blocks lifted to symbols in the term before, and unused value slots removed |
| `exported_chain.ml` | three exported functions, each calling the one before twice | closures and blocks lifted to symbols in the term before, and unused value slots removed |
| `exported_string_length.ml` | a constant string of the module, and an exported function that returns its length | closures and blocks lifted to symbols in the term before, and the length of the constant computed in the code of the function |
| `exported_record_update.ml` | a constant record, an exported function that makes a record from another with one field changed, and a call of it on the constant when the module runs | closures and blocks lifted to symbols in the term before |
| `exported_bool.ml` | an exported predicate, and an exported function that uses it on each of its two arguments with `&&` | closures and blocks lifted to symbols in the term before, and unused value slots removed |
| `exported_after_effect.ml` | a value that is not known until the module runs, then an exported function, then a call of the function on the value | closures and blocks lifted to symbols in the term before |
| `exported_twice_kept.ml` | a function that takes a function and is always inlined, given an exported function that is never inlined: the two calls of the argument, in the code of the function that gives it, stay, as direct calls | closures and blocks lifted to symbols in the term before, and unused value slots removed. It takes two things together: the calls of the argument are left alone on both sides, as the code called is in the list of code not to inline (the term after still calls it), and in the term before the indirect calls of the symbol of the argument are made direct in the code, as Simplify leaves them (`FlambdaKnownSymbolsSpec.fold_known_apply`). Without the second it is not validated: the two terms then differ in the kind of those calls only. With every call inlined on both sides in place of the first it is not validated either: the term after is left with a continuation applied once, which its normalisation does not inline |
| `exported_compose_kept.ml` | the composition of two exported functions that are never inlined, by a function that is always inlined: the two calls stay, in the code of the composition, as direct calls | as `exported_twice_kept.ml` |
| `exported_branch_then_fun.ml` | a value chosen by a test that is not resolved when the module runs, then an exported function that uses it: the closure of the function becomes a symbol that holds the value in a value slot, and the symbol and its code are bound in the handler of the continuation that the test goes to | the closure lifted to a symbol in the term before and all the code of the term after bound first |
| `exported_match_then_fun.ml` | a value taken out of an option that is not known, then a predicate that uses it: as the one before, after a match | as the one before |
| `exported_branch_two_funs.ml` | a value chosen by a test, then two functions, the second calling the first: inlines the call; both closures become symbols, bound with their code in the handler | the closures lifted to symbols, the unused value slot removed and the code of the term after bound first |
| `exported_fun_branch_fun.ml` | a function, then a value chosen by a test, then a function that uses both: the code of the second function, with the call of the first inlined, is bound in the handler | as the one before |
| `exported_two_branches.ml` | two values, each chosen by a test, with a function after each, the second function calling the first: the code of each function is bound in the handler of its test, the second handler inside the first | as the one before |
| `exported_branch_pair.ml` | one of two constant pairs chosen by a test, then a function that reads it: the pairs become symbols, and the closure a symbol that holds the one chosen | the closure lifted to a symbol in the term before and the code of the term after bound first |
| `exported_branch_calls_twice.ml` | as `exported_branch_two_funs.ml`, the second function calling the first twice: inlines both calls, and reads the value slot of the first closure once | the same, not validated: with the two calls inlined in the term before the validator reads the value slot twice, and it shares no primitive |
| `exported_some_again.ml` | a value that is not known until the module runs, put in an option that a function which is always inlined takes apart, and kept in another option: the first option is gone, and the second is a symbol | the closure and the second option lifted to symbols: the test tool gives the symbol to the first block of its shape, which is the first option, finds it unused in the end, and guesses again without it |
| `exported_fun_given.ml` | a function that gives, to the function it is given, a function which needs nothing from around it: the closure given is a symbol, bound beside the code of the function that gives it | the closure lifted out of the code of the function in the term before (`FlambdaLiftFromCodeSpec.lift_from_code_unit`) |
| `exported_fun_returned.ml` | a function that returns a function of its own which needs nothing from around it: the closure returned is a symbol | as the one before |
| `exported_funs_given.ml` | a function that gives two such functions: both closures are symbols | the two closures lifted out of the code; they are bound in the order of their `Let`s, which is not the order in which Simplify binds them, and the static bindings of a group are compared whatever their order |
| `exported_fun_in_option.ml` | a function that returns an option of such a function: the closure and the option are symbols | the closure lifted out of the code in a first lifting and the option in a second, which puts it before the closure; the order again |
| `exported_fun_to_map.ml` | a recursive function on lists, which is not inlined, and a function that gives it a function which needs nothing from around it: the closure given is a symbol | the closure lifted out of the code of the function that gives it, the calls of the recursive function left as they are, and the unused value slot removed |
| `exported_local_never.ml` | a function with a function of its own inside, which is never inlined and needs nothing from around it: the closure of the inner function is a symbol | the closure lifted out of the code of the outer function, and the calls of the inner function left as they are |

### The same on one run, not validated

| Source | Steps | What the validator lacks |
|--------|-------|--------------------------|
| `either_heap.ml` | 58, 37 | a variant unboxed where two branches meet, with `poison` for the fields that a branch has not got (T6) |
| `exported_branch_calls_twice.ml` | 17, 11 | with its two calls inlined in the term before, each inlined body reads the value slot of the static closure of the function; Simplify reads it once. Two equal projections of a value slot are not shared yet (V2) |
| `int64_option_heap.ml` | 63, 38 | a variant unboxed where two branches meet, with `poison` for the fields that a branch has not got (T6) |
| `list_heap.ml` | 54, 33 | a variant unboxed where two branches meet, with `poison` for the fields that a branch has not got (T6) |
| `list_length.ml` | 64, 44 | a self tail call made a jump (V4) |
| `list_rev.ml` | 70, 47 | a self tail call made a jump (V4) |
| `mod_zero.ml` | 22, 6 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `nested_heap.ml` | 50, 29 | a variant unboxed where two branches meet, with `poison` for the fields that a branch has not got (T6) |
| `option_heap.ml` | 47, 29 | a variant unboxed where two branches meet, with `poison` for the fields that a branch has not got (T6) |
| `option_join.ml` | 55, 29 | a variant unboxed where two branches meet, with `poison` for the fields that a branch has not got (T6) |
| `pair_built.ml` | 43, 21 | a parameter of a continuation where two branches meet, unboxed (T6) |
| `pair_join.ml` | 31, 28 | a parameter of a continuation where two branches meet, unboxed (T6) |
| `pair_kept.ml` | 35, 33 | a parameter of a continuation where two branches meet, unboxed (T6) |
| `pair_loop.ml` | 192, 85 | a self tail call made a jump (V4), and a parameter of the loop unboxed (T6) |
| `partial_exported.ml` | 13, 6 | the wrapper that Simplify makes of a partial application calls the function through a value slot of its own closure; the validator, which knows what the slot holds, inlines that call in the term before, and has no rewrite that does it in the term after (V3) |
| `raise_in_function.ml` | 24, 11 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `raise_inlined.ml` | 27, 11 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `raise_notrace.ml` | 22, 10 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `raise_unused_bucket.ml` | 23, 10 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `raise_unused_exn.ml` | 22, 10 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `shape2_heap.ml` | 61, 36 | a variant unboxed where two branches meet, with `poison` for the fields that a branch has not got (T6) |
| `shape_heap.ml` | 54, 30 | a variant unboxed where two branches meet, with `poison` for the fields that a branch has not got (T6) |
| `string_get_checked.ml` | 21, 4 | the bounds check of an access to a string that is a constant of the unit: the validator, which knows the string, resolves it where Simplify does not |
| `string_get_unknown.ml` | 28, 16 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `string_sum.ml` | 100, 82 | a self tail call made a jump (V4) |
| `tail_loop.ml` | 128, 83 | a self tail call made a jump (V4) |
| `try_catch_all.ml` | 22, 10 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `try_div_zero.ml` | 23, 12 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `try_nested.ml` | 30, 14 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `try_no_raise.ml` | 14, 5 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `try_reraise.ml` | 29, 14 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `try_result_unused.ml` | 13, 3 | an exception: the handler of a `try` that nothing raises to any more is made an ordinary continuation and its trap actions dropped, which the validator does not follow (C5) |
| `while_flag.ml` | 150, 75 | a boolean that Simplify keeps untagged in a parameter of the loop (T6) |
| `while_unused_counter.ml` | 78, 40 | a parameter of a loop that is only passed round the loop, which Simplify removes (V4) |

### Undefined in the model

| Source | Why the term before has no meaning |
|--------|------------------------------------|
| `exn_with_argument.ml` | as `try_not_found.ml` |
| `try_not_found.ml` | a handler that catches an exception by name compares it with a symbol of another unit (V2-4; C5) |

### Not checked

| Source | What the model has not got |
|--------|----------------------------|
| `array_literal.ml` | arrays: `Array_load` |
| `float_add.ml` | floating-point arithmetic |
| `ref_counter.ml` | mutable fields: `Block_set` (C4) |
| `tupled_function.ml` | a tupled function in a unit with a call that is not direct |

## What stops a unit from validating, most common first

1. Exceptions (thirteen units). A `try` installs a handler and removes
   it. Where Simplify finds that nothing can raise to the handler any
   more, or that what is raised is known, it makes the handler an
   ordinary continuation and drops the trap actions. The validator
   compares trap actions and has no rewrite for that yet
   (`try_no_raise.ml`, `mod_zero.ml`). Where the body can still raise
   to the handler, or there is no `try`, the unit is validated
   (`div_unknown.ml`, `uncaught_raise.ml`, `div_const.ml`).
2. A value unboxed where two branches meet (twelve units). Simplify
   passes the fields of a pair to the continuation that the branches
   go to, in place of the block (`pair_join.ml`); for a variant it
   passes `poison` for the fields that a branch has not got
   (`option_join.ml`, `shape_heap.ml`).
3. A self tail call made a jump (four units, and one of those above):
   `tail_loop.ml`, `list_length.ml`. The validator can do it
   (`FlambdaLoopifySpec.v`) and is not yet told for which code.
4. Loops (two units): a parameter of a loop that is only passed round
   the loop (`while_unused_counter.ml`), and a boolean that Simplify
   keeps untagged in a parameter of the loop (`while_flag.ml`).
5. A partial application that the unit exports
   (`partial_exported.ml`): the wrapper that Simplify makes of it calls
   the function through a value slot of its own closure, and the
   validator, which knows what the slot holds, inlines that call in
   the term before only.
6. The validator knows more than Simplify in one unit: it resolves the
   bounds check of an access to a string that is a constant of the
   unit (`string_get_checked.ml`), and the two terms then differ the
   other way.
7. Two equal projections of a value slot, which a function inlined
   twice leaves in the term before and Simplify makes once
   (`exported_branch_calls_twice.ml`): the sharing of primitives does
   not cover projections yet.

What the model has not got, and the conversion refuses: floating-point
arithmetic (`float_add.ml`), arrays (`array_literal.ml`), mutable
fields (`ref_counter.ml`), and a tupled function called indirectly
(`tupled_function.ml`).

Two units are undefined in the model before Simplify
(`try_not_found.ml`, `exn_with_argument.ml`): a handler that catches an
exception by name compares what was raised with the predefined
exception, which is a symbol of another unit; the model gives no
value to a comparison of two allocated values, and none to an
operation on a symbol that the unit does not bind (discrepancy V2-4).

What was on this list and is not any more, with the rewrite that
removed it:

- The continuation that makes the module block, applied once inside
  the handler that two branches go to (`if_unknown.ml`): a
  continuation is moved to the handler that alone uses it
  (`FlambdaSinkContsSpec.v`).
- A function that the unit keeps, whose closure becomes a symbol
  (`exported_function.ml`, `factorial.ml`): the validator lifts the
  `Let`s that Simplify lifted (`FlambdaLiftSpec.v`), and uses what the
  unit binds its symbols to (`FlambdaKnownSymbolsSpec.v`).
- Loops whose handler has something to fold (`while_loop.ml`,
  `for_sum.ml`): the rewrites of a round go into the handlers of
  recursive continuations (`FlambdaRecHandlersSpec.v`).
- The identities of arithmetic (`add_zero.ml`):
  `FlambdaIdentitiesSpec.v`.
- A primitive computed twice by the front end and once by Simplify, a
  boxed number unboxed at each use above all: `FlambdaCseSpec.v`.
- A function inlined twice at arguments that are not known
  (`twice_inlined.ml`, `local_function.ml`, `labelled_optional.ml`).
  The two copies of its body bind the same names in the term before,
  one in the scope of the other, and an alias of a name that is bound
  again is not followed, as it must not be; Simplify gives each copy
  names of its own. The validator gives every binder of the term
  before a name of its own once the calls are inlined
  (`FlambdaRenameApartSpec.v`).
- The order in which a group of static bindings binds the code of
  functions that call each other: Simplify builds the group again, in
  an order of its own, and the validator puts the bindings of the term
  before in the order of the term after (`FlambdaStaticsOrderSpec.v`;
  `../statics_order.fl`, written by hand, is validated by that alone).
- A local function given to a function that is inlined, inside a
  function that the unit keeps (`closure_argument_exported.ml`): the
  call becomes direct in the body of code, whose own group has the
  code called; the validator inlines between the code of one group
  (`FlambdaInlineSiblingsSpec.v`).
- A closure of a set that the term does not use
  (`returned_closure_of_pair.ml`): in the model it is the `Let` of a
  projection, which the term before loses by a refinement; the term
  after now loses it by an equivalence
  (`FlambdaUnusedProjectionsSpec.v`).
- A recursive function that the unit keeps and calls (`fib.ml`,
  `list_map.ml`, `factorial.ml`): each round inlined the call once
  more on both sides. The validator is told which calls to leave
  (`FlambdaNormaliseSpec.inline_calls`), and the test tool names the
  recursive code and the code that the term after still calls.
- A function that is never inlined, given to one that always is
  (`exported_twice_kept.ml`): the same list, and the indirect call of
  a symbol that the unit binds to a closure made direct
  (`FlambdaKnownSymbolsSpec.v`).
- Closures made symbols where a value slot is a variable
  (`closed_mutual_recursion.ml`), or where the function is then called
  through a variable (`indirect_call.ml`): the function slots of a
  static set are known whatever its value slots hold
  (`FlambdaKnownSymbolsSpec.v`), and liftings are made in turn.
- An application of a continuation whose handler only applies
  another, a trap action included (`div_unknown.ml`,
  `string_get16_checked.ml`): it goes there directly
  (`FlambdaForwardSpec.v`).
- A parameter of a loop that every application gives the same thing
  (`while_const_after.ml`, `while_nested.ml`): it is bound at the head
  of the handler (`FlambdaParamAliasesSpec.v`), and the parameters of
  loops that are left unused are removed
  (`FlambdaUnusedParamsSpec.v`).

A count over 600 units made at random is in `census/README.md`.

## Units that test the arithmetic

Some units have no unknown input: Simplify computes the whole result,
and the machine computes it from the term before, so the two runs
agreeing says that the model's primitives and Simplify's compute the
same thing there. They are written for the edges: arithmetic that
overflows at 63, 32 and 64 bits (`overflow_wrap.ml`,
`int32_overflow.ml`, `int64_overflow.ml`), shifts at the first and the
last bit (`shift_edges.ml`), conversions that lose bits or extend a
sign (`conv_truncate.ml`), comparisons of negative numbers
(`compare_signed.ml`). Each result is exported by itself and not in a
tuple, as a tuple of constants is made a symbol and the unit would
then wait for lifting.

## What a check costs

The tool gives the validator fifty rounds. A round applies each
normalisation once to the whole term, and the normalisations are at
worst quadratic in the size of the term; the rounds are there because
one rewrite makes room for another, and most units are done in three or
four. A round inlines every direct call of known code but for the code
that the tool names to the validator, a guess that is not trusted. The
tool tries two lists in turn: the code that is recursive (that calls
itself, at once or through other code, in either term) with the code
that the term after still calls directly; then the recursive code
alone. Without such a list each round unrolled a recursive function
once more on both sides, and `fib.ml` did not end. With it a round can
only inline code that is not recursive, so the terms stop growing.
Each attempt may go on to guess what Simplify lifted and which value
slots it removed. The 212 units here are checked in under ten seconds
of processor time together.

`FLSEMANTICS_PRINT_TERMS=1` makes the tool print, of a unit that is not
validated, the two terms that were compared last, for each list.

## What a validation does not say

- A unit is validated on the reading that a string is immutable.
  `Bytes.unsafe_to_string`, `Bytes.unsafe_of_string` and the
  conversions between arrays and immutable arrays are erased before
  Flambda 2 (`from_lambda/lambda_to_lambda_transforms.ml`), so the test
  tool cannot see them; it refuses a unit in which a primitive on bytes
  arrives, but the verdict on a unit that reads a string says nothing
  of a string that is the block of bytes written while it is read
  (X5-3).
- Regions: see above.
- What is validated is the term the parser reads back from what
  `-drawfexpr` prints (see "validated" above).

What no example here validates, because the model has not got it:
mutable fields and arrays, arithmetic on floats, calls of C functions
(polymorphic comparison among them), an exception that the unit
declares (it is made by a call of a C function), objects, laziness.
(`fst` and `snd` are in the model: the standard library declares them
with `%field0_immut` and `%field1_immut`, a load that cannot change,
with a tag and a size that are not known: `fst_snd.ml`. It is `!`, and
`%field0` written by hand, that load a field marked as one that may
change.)
