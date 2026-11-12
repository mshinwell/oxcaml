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
  The `Let` by which the handler ends the region is kept, bound to
  `%opaque` of the unit value: Simplify does not delete that primitive
  for being unused, so a handler that begins with it is not a
  continuation that only applies another, and the validator must not
  take it for one.
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
  unknown arity gives it the pair. The model's code has the mark, and
  every call of the model gives such code its first argument as the
  pair; the arguments after it, if there are any, are given as they
  are and make the call an over-application
  (`FlambdaSemanticsSpec.arguments_for_code`). So a call of unknown
  arity is converted as it is (`tupled_function.ml`). A direct call,
  and a call of known arity, give the code the components, which the
  model has not got yet: a direct call of tupled code that the unit
  binds is refused, and so is a call of known arity in a unit that
  binds tupled code. A function with a pair pattern is not always
  tupled code: the code that `nested_tuple.ml` makes takes one
  parameter, the pair, which the call allocates.

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
  Where the verdict has a second line, "at the second asking", the
  validator refused the pair as it is, and the tool asked
  `validate_unit_knowing` (`FlambdaValidateKnowingSpec.v`): the same
  check of the two terms, each normalised first by rounds in front of
  which the aliases are followed knowing what the symbols are bound
  to. What it accepts is correct of the unit in the same way
  (`FlambdaValidateKnowingProofs.validate_unit_knowing_sound`).
- **validated for the term as read, which says never null of a value
  that may be null** (discrepancy T4-13): the tool's verdict is
  "validated", and the tables count the unit apart. The text that
  `-drawfexpr` prints cannot say that a value may be null where it
  writes a kind, which it does in a field of the shape of a block
  and in an arity of more than one component: the parser reads every
  kind of values that is written as one that is never null
  (`middle_end/flambda2/parser/fexpr_to_flambda.ml`). The model's
  term before is the compiler's all the same, as the conversion
  drops these kinds. Only the term after can differ from the
  compiler's, and only where Simplify used the kind: told that a
  value is never null, the tool's Simplify can remove a test of null
  that the compiler's keeps. So what is validated is the tool's
  Simplify of the term as read. Nothing in the tree finds these
  units, as the text is where the kind is lost: the list was made
  twice outside it, by compiling each unit with a compiler whose
  printer writes the mark (T4) and by comparing the term in the
  compiler's memory with the term read back (X5), and the two lists
  are the same.
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

284 sources: 256 validated, 13 validated for the term as read, which
says never null of a value that may be null (T4-13), 8 compared on one
run and not validated, 2 undefined in the model, 5 not checked.

### Validated

| Source | Steps | Source | Steps |
|--------|-------|--------|-------|
| `add3_exported.ml` | 9, 6 | `int_of_char.ml` | 8, 3 |
| `add_zero.ml` | 8, 2 | `int_switch.ml` | 31, 1 |
| `apply_exported.ml` | 8, 4 | `is_even.ml` | 29, 1 |
| `bitwise_unknown.ml` | 14, 7 | `join_pair_equal_fields.ml` | 50, 28 |
| `bool_not_unknown.ml` | 8, 3 | `join_phys_equal_arms.ml` | 25, 17 |
| `bool_ops.ml` | 47, 1 | `join_two_names_of_symbol.ml` | 24, 8 |
| `bswap_constants.ml` | 29, 2 | `labelled_arguments.ml` | 13, 3 |
| `call_result_tested.ml` | 78, 73 | `labelled_optional.ml` | 38, 6 |
| `call_result_unused.ml` | 79, 50 | `list_head.ml` | 41, 3 |
| `capture_fun_and_var_run.ml` | 24, 20 | `list_heap.ml` | 54, 33 |
| `capture_rec_self.ml` | 9, 6 | `list_last.ml` | 76, 41 |
| `capture_two_funs.ml` | 15, 12 | `list_sum.ml` | 61, 42 |
| `char_code.ml` | 13, 3 | `local_call_exported.ml` | 8, 4 |
| `char_match.ml` | 48, 1 | `local_call_used.ml` | 10, 3 |
| `clamp.ml` | 49, 1 | `local_function.ml` | 29, 5 |
| `closed_mutual_recursion.ml` | 66, 35 | `match_guard.ml` | 52, 1 |
| `closure_argument_exported.ml` | 12, 7 | `match_unknown.ml` | 18, 10 |
| `closure_argument_used.ml` | 14, 3 | `match_variant.ml` | 66, 7 |
| `closure_capture.ml` | 31, 4 | `match_variant_local.ml` | 72, 7 |
| `closure_captures_argument_inlined.ml` | 27, 21 | `max_exported.ml` | 8, 4 |
| `closure_captures_field_once.ml` | 24, 19 | `min_max.ml` | 25, 1 |
| `closure_from_pair_called.ml` | 44, 15 | `mod_zero.ml` | 22, 6 |
| `closure_from_pair_exported.ml` | 9, 4 | `module_alias.ml` | 34, 5 |
| `closure_from_pair_used.ml` | 16, 3 | `mutual_alias_exported.ml` | 78, 40 |
| `closure_in_tuple.ml` | 33, 5 | `mutual_capture_exported.ml` | 123, 72 |
| `closure_pair_shares_capture.ml` | 45, 40 | `mutual_recursion.ml` | 130, 70 |
| `collatz_local_refs.ml` | 3218, 1827 | `nativeint_arith.ml` | 25, 8 |
| `compare_ints.ml` | 113, 1 | `negate.ml` | 10, 5 |
| `compare_order.ml` | 60, 35 | `nested_heap.ml` | 50, 29 |
| `compare_signed.ml` | 31, 1 | `nested_record.ml` | 23, 3 |
| `compare_tested.ml` | 15, 6 | `nested_tuple.ml` | 24, 4 |
| `compare_unknown.ml` | 9, 4 | `not_inlined.ml` | 21, 17 |
| `compose.ml` | 29, 4 | `num_conversions.ml` | 27, 19 |
| `compose_exported.ml` | 8, 4 | `option_bind.ml` | 89, 1 |
| `constant_exported.ml` | 8, 4 | `option_default.ml` | 32, 3 |
| `constant_folding.ml` | 31, 1 | `option_heap.ml` | 47, 29 |
| `conv_truncate.ml` | 45, 1 | `option_inlined.ml` | 36, 12 |
| `div_const.ml` | 26, 5 | `option_join.ml` | 55, 29 |
| `div_unknown.ml` | 16, 8 | `option_map.ml` | 70, 4 |
| `either_heap.ml` | 58, 37 | `or_null_known.ml` | 23, 1 |
| `enum_to_int.ml` | 19, 1 | `or_null_unknown.ml` | 16, 6 |
| `exported_after_effect.ml` | 15, 6 | `or_pattern.ml` | 49, 1 |
| `exported_and_used.ml` | 14, 6 | `over_application.ml` | 19, 3 |
| `exported_apply.ml` | 18, 9 | `over_rec.ml` | 84, 52 |
| `exported_arms_after_let.ml` | 26, 21 | `overflow_wrap.ml` | 19, 1 |
| `exported_bool.ml` | 11, 7 | `pair_built.ml` | 43, 21 |
| `exported_branch_calls_twice.ml` | 17, 11 | `pair_computed.ml` | 45, 29 |
| `exported_branch_fun_const.ml` | 17, 12 | `partial_application.ml` | 23, 3 |
| `exported_branch_option.ml` | 14, 9 | `phys_equal_unknown.ml` | 9, 4 |
| `exported_branch_pair.ml` | 15, 10 | `physical_equality.ml` | 32, 1 |
| `exported_branch_then_const.ml` | 14, 9 | `pipeline.ml` | 23, 5 |
| `exported_branch_then_fun.ml` | 14, 8 | `polymorphic_variant.ml` | 77, 4 |
| `exported_branch_two_funs.ml` | 17, 11 | `power.ml` | 147, 99 |
| `exported_capture.ml` | 16, 5 | `project_record_two_levels.ml` | 43, 18 |
| `exported_chain.ml` | 14, 10 | `project_variant_argument.ml` | 27, 11 |
| `exported_compose_kept.ml` | 17, 13 | `projections_exported.ml` | 11, 7 |
| `exported_const_list.ml` | 10, 7 | `raise_in_function.ml` | 24, 11 |
| `exported_curried.ml` | 14, 6 | `raise_inlined.ml` | 27, 11 |
| `exported_fun_branch_fun.ml` | 17, 11 | `raise_notrace.ml` | 22, 10 |
| `exported_fun_given.ml` | 9, 7 | `raise_unused_bucket.ml` | 23, 10 |
| `exported_fun_in_arms.ml` | 20, 12 | `raise_unused_exn.ml` | 22, 10 |
| `exported_fun_in_one_arm.ml` | 17, 12 | `record_exported.ml` | 11, 7 |
| `exported_fun_in_option.ml` | 9, 8 | `record_of_functions.ml` | 51, 10 |
| `exported_fun_returned.ml` | 9, 7 | `record_project.ml` | 37, 8 |
| `exported_function.ml` | 14, 6 | `record_update.ml` | 27, 4 |
| `exported_funs_given.ml` | 10, 10 | `ref_local.ml` | 132, 79 |
| `exported_funs_in_arms_used.ml` | 23, 14 | `ref_straight.ml` | 13, 4 |
| `exported_funs_in_pair.ml` | 14, 11 | `result_join.ml` | 64, 33 |
| `exported_list.ml` | 9, 5 | `result_map.ml` | 44, 3 |
| `exported_local_fun.ml` | 8, 4 | `returned_closure_of_pair.ml` | 71, 50 |
| `exported_local_never.ml` | 9, 7 | `same_field_chain_twice.ml` | 29, 18 |
| `exported_match_pair_then_fun.ml` | 13, 7 | `same_int64_sum_twice.ml` | 29, 14 |
| `exported_match_then_fun.ml` | 21, 12 | `same_projection_across_call.ml` | 25, 13 |
| `exported_match_three_funs.ml` | 33, 19 | `seq_unit.ml` | 13, 2 |
| `exported_nested_branch.ml` | 21, 13 | `shape2_heap.ml` | 61, 36 |
| `exported_nested_pair.ml` | 10, 7 | `shape_constant.ml` | 24, 11 |
| `exported_option_fun_in_arm.ml` | 18, 10 | `shape_heap.ml` | 54, 30 |
| `exported_pair_fun_in_arms.ml` | 21, 14 | `shift_edges.ml` | 23, 1 |
| `exported_record.ml` | 23, 9 | `shift_unknown.ml` | 17, 7 |
| `exported_record_of_funs.ml` | 14, 11 | `shifts.ml` | 22, 8 |
| `exported_record_update.ml` | 14, 6 | `sibling_given_as_value.ml` | 75, 38 |
| `exported_records_in_arms.ml` | 21, 14 | `sibling_through_alias.ml` | 74, 38 |
| `exported_some_again.ml` | 26, 6 | `sign.ml` | 27, 1 |
| `exported_string_length.ml` | 8, 5 | `string_get16.ml` | 10, 5 |
| `exported_submodule.ml` | 14, 8 | `string_get16_be.ml` | 16, 6 |
| `exported_table.ml` | 13, 8 | `string_get16_checked.ml` | 29, 17 |
| `exported_twice_kept.ml` | 14, 10 | `string_get32.ml` | 23, 11 |
| `exported_two_branches.ml` | 23, 15 | `string_get_const.ml` | 9, 4 |
| `exported_two_functions.ml` | 22, 10 | `string_length_const.ml` | 8, 1 |
| `exported_two_somes.ml` | 11, 5 | `string_length_unknown.ml` | 9, 5 |
| `exported_two_tests.ml` | 26, 17 | `string_sum.ml` | 100, 82 |
| `exported_two_values.ml` | 18, 1 | `submodule.ml` | 27, 1 |
| `exported_variant.ml` | 17, 6 | `succ_pred.ml` | 12, 5 |
| `fact_exported.ml` | 8, 3 | `tail_loop.ml` | 128, 83 |
| `factorial.ml` | 70, 46 | `toplevel_closure_applied_mutual.ml` | 84, 40 |
| `fib.ml` | 2041, 1417 | `tree_root.ml` | 90, 4 |
| `first_class_module.ml` | 22, 4 | `try_catch_all.ml` | 22, 10 |
| `float_const.ml` | 15, 4 | `try_div_zero.ml` | 23, 12 |
| `for_down.ml` | 79, 40 | `try_exported.ml` | 8, 4 |
| `for_if.ml` | 165, 96 | `try_in_function.ml` | 25, 10 |
| `for_nested.ml` | 171, 95 | `try_nested.ml` | 30, 14 |
| `for_sum.ml` | 135, 81 | `try_no_raise.ml` | 14, 5 |
| `for_two_refs.ml` | 90, 52 | `try_reraise.ml` | 29, 14 |
| `fst_snd.ml` | 16, 3 | `try_result_unused.ml` | 13, 3 |
| `functions_in_record_called.ml` | 23, 17 | `try_test_outside.ml` | 22, 10 |
| `functor_apply.ml` | 23, 1 | `tuple_match.ml` | 75, 1 |
| `gadt_known.ml` | 35, 4 | `tuple_return.ml` | 20, 5 |
| `higher_order.ml` | 32, 5 | `tuple_swap.ml` | 19, 4 |
| `id_exported.ml` | 8, 4 | `tuple_through_kept_identity.ml` | 19, 12 |
| `identity.ml` | 22, 3 | `tupled_function.ml` | 21, 2 |
| `if_unknown.ml` | 13, 6 | `twice_inlined.ml` | 19, 6 |
| `ignore_value.ml` | 11, 2 | `unboxed_pair.ml` | 13, 4 |
| `indirect_call.ml` | 13, 9 | `unboxed_pair_argument.ml` | 10, 3 |
| `inline_function.ml` | 20, 4 | `uncaught_raise.ml` | 10, 4 |
| `inline_record.ml` | 45, 7 | `unit_argument.ml` | 18, 1 |
| `int32_arith.ml` | 27, 8 | `variant_blocks_join.ml` | 20, 8 |
| `int32_overflow.ml` | 40, 1 | `variant_match_exported.ml` | 8, 4 |
| `int32_unknown.ml` | 17, 7 | `variant_nested_match.ml` | 213, 151 |
| `int64_boxed.ml` | 22, 8 | `variant_two_blocks.ml` | 44, 30 |
| `int64_built.ml` | 61, 43 | `while_const_after.ml` | 70, 45 |
| `int64_compare.ml` | 48, 1 | `while_countdown.ml` | 61, 34 |
| `int64_compare_tested.ml` | 18, 8 | `while_if_inside.ml` | 161, 106 |
| `int64_join.ml` | 26, 1 | `while_loop.ml` | 78, 45 |
| `int64_of_int.ml` | 25, 7 | `while_nested.ml` | 188, 127 |
| `int64_option_heap.ml` | 63, 38 | `while_sum_down.ml` | 133, 80 |
| `int64_overflow.ml` | 33, 1 | `while_two_loops.ml` | 126, 81 |
| `int64_shift.ml` | 21, 8 | `while_two_tests.ml` | 180, 123 |
| `int64_to_int32.ml` | 10, 6 | `while_unused_counter.ml` | 78, 40 |

### Validated for the term as read (T4-13)

| Source | Steps | Source | Steps |
|--------|-------|--------|-------|
| `curry.ml` | 36, 3 | `list_length.ml` | 64, 44 |
| `exported_fun_to_map.ml` | 12, 9 | `list_map.ml` | 132, 95 |
| `exported_length.ml` | 8, 3 | `list_rev.ml` | 70, 47 |
| `exported_made.ml` | 14, 6 | `option_map_exported.ml` | 8, 4 |
| `exported_option_library.ml` | 14, 10 | `string_const.ml` | 21, 2 |
| `length_exported.ml` | 8, 3 | `swap_exported.ml` | 8, 4 |
| `let_polymorphism.ml` | 27, 1 |  |  |

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
| `exported_branch_calls_twice.ml` | as `exported_branch_two_funs.ml`, the second function calling the first twice: inlines both calls, and reads the value slot of the first closure once | as `exported_branch_two_funs.ml`; with the two calls inlined in the term before, the value slot is projected twice, and the second projection is made the variable of the first (`FlambdaShareProjectionsSpec.share_known_projections`) |
| `exported_some_again.ml` | a value that is not known until the module runs, put in an option that a function which is always inlined takes apart, and kept in another option: the first option is gone, and the second is a symbol | the closure and the second option lifted to symbols: the test tool gives the symbol to the first block of its shape, which is the first option, finds it unused in the end, and guesses again without it |
| `exported_fun_given.ml` | a function that gives, to the function it is given, a function which needs nothing from around it: the closure given is a symbol, bound beside the code of the function that gives it | the closure lifted out of the code of the function in the term before (`FlambdaLiftFromCodeSpec.lift_from_code_unit`) |
| `exported_fun_returned.ml` | a function that returns a function of its own which needs nothing from around it: the closure returned is a symbol | as the one before |
| `exported_funs_given.ml` | a function that gives two such functions: both closures are symbols | the two closures lifted out of the code; they are bound in the order of their `Let`s, which is not the order in which Simplify binds them, and the static bindings of a group are compared whatever their order |
| `exported_fun_in_option.ml` | a function that returns an option of such a function: the closure and the option are symbols | the closure lifted out of the code in a first lifting and the option in a second, which puts it before the closure; the order again |
| `exported_fun_to_map.ml` | a recursive function on lists, which is not inlined, and a function that gives it a function which needs nothing from around it: the closure given is a symbol | the closure lifted out of the code of the function that gives it, the calls of the recursive function left as they are, and the unused value slot removed |
| `exported_local_never.ml` | a function with a function of its own inside, which is never inlined and needs nothing from around it: the closure of the inner function is a symbol | the closure lifted out of the code of the outer function, and the calls of the inner function left as they are |
| `exported_option_library.ml` | three functions on options, as a small library has them (`map`, `default`, `is_some`): nothing is known of their arguments, and the three closures are symbols | closures and blocks lifted to symbols in the term before |
| `exported_length.ml` | the length of a list, a recursive function that is not a loop: its closure is a symbol and it calls itself through it | closures and blocks lifted to symbols in the term before |
| `exported_const_list.ml` | a constant list and a function that reads its head: the match is resolved in the code of the function | closures and blocks lifted to symbols in the term before |
| `exported_record_of_funs.ml` | a record of two functions and a function that calls one of them through the record: the call is of the symbol of the function, and is inlined | closures and blocks lifted to symbols in the term before, and unused value slots removed |
| `exported_submodule.ml` | a module inside the module, and a function outside it that calls a function of the inner module twice: the calls are inlined | closures and blocks lifted to symbols in the term before, and unused value slots removed |
| `exported_two_somes.ml` | two options, each of a value that is not known until the module runs: each is a symbol with a variable in its field | the two blocks lifted to symbols in the term before |
| `exported_branch_option.ml` | an option chosen by a test when the module runs, and a function that reads it with a default | the closure lifted to a symbol in the term before and the code of the term after bound first |
| `exported_branch_then_const.ml` | a value chosen by a test, then a constant pair and a function that reads the pair and the value: the two loads from the pair and their sum are folded | as the one before |
| `exported_branch_fun_const.ml` | a test when the module runs, then two functions that do not use what it chose, the second calling the first twice | as the one before, with the unused value slot removed |
| `exported_match_pair_then_fun.ml` | a pair that is not known until the module runs, taken apart, and a function that uses both parts | the closure lifted to a symbol in the term before, with the two parts in its value slots |
| `exported_nested_branch.ml` | a value chosen by two tests, one inside the other, and a function that uses it: its code is bound in the handler of the continuation that the three arms go to | the closure lifted to a symbol in the term before and the code of the term after bound first |
| `exported_fun_in_arms.ml` | a function chosen by a test when the module runs, each arm making a function that needs nothing from around it: the two closures are symbols | the closures lifted to the head of the unit in the term before, and the two terms compared with their static bindings that mention no variable bound first |
| `exported_fun_in_one_arm.ml` | a test when the module runs, between a function defined before it and a function made in the other arm: the closure of the arm is a symbol | as the one before |
| `exported_arms_after_let.ml` | a function that makes a function in each arm of a test, and the same test made when the module runs on a value computed before it: the four closures of the arms are symbols | the closures lifted out of the code and to the head of the unit in the term before, and the two terms compared with their static bindings that mention no variable bound first |
| `exported_two_tests.ml` | two tests when the module runs, one after the other: the first chooses a number, the second a function, whose closures are symbols | as `exported_fun_in_arms.ml` |
| `exported_funs_in_arms_used.ml` | a function chosen by a test when the module runs, and a function defined after the test that calls it twice: the closures of the arms are symbols | as `exported_fun_in_arms.ml`, with the closure of the function defined after the test lifted where it stands |
| `exported_option_fun_in_arm.ml` | an option chosen by a test when the module runs, whose contents is a function made in the arm: the closure and the block that holds it are symbols | two liftings to the head of the unit in the term before: the closure, then the block, which mentions no variable once the closure is a symbol; and the two terms compared with their static bindings that mention no variable bound first |
| `exported_pair_fun_in_arms.ml` | a pair chosen by a test when the module runs, of a number and a function made in the arm: the closures and the pairs are symbols | as the one before |
| `exported_records_in_arms.ml` | a record chosen by a test when the module runs, of a function made in the arm and a number: the closures and the records are symbols | as the one before |
| `exported_match_three_funs.ml` | a function chosen by a match of three cases when the module runs: the three closures are symbols, bound below the handler of the inner test, which mentions two of them | as `exported_fun_in_arms.ml` |

### The same on one run, not validated

| Source | Steps | What the validator lacks |
|--------|-------|--------------------------|
| `capture_fun_bound_in_handler_run.ml` | 31, 26 | the closure of the function that is called holds a value chosen by a test when the module runs, so its symbol is bound in the handler of that test; the code of the closure that calls it is bound at the head of the unit and reads it from a value slot, where Simplify puts the symbol; the validation reads a slot only where the symbol it holds is in scope, and leaves this projection (C3) |
| `pair_join.ml` | 31, 28 | one branch gives a parameter of the function, and Simplify loads its fields at that use, which only the subkind of the parameter justifies; the model has no subkinds (T6-7) |
| `pair_kept.ml` | 35, 33 | as `pair_join.ml` |
| `pair_loop.ml` | 192, 85 | as `pair_join.ml`, at the entry of a loop, whose parameter Simplify unboxes from its subkind without looking at the uses (T6-7) |
| `partial_exported.ml` | 13, 6 | the wrapper of a partial application, which the front end makes as code marked `stub`, calls the function directly through a value slot of its own closure; Simplify does not simplify a stub where its closure is made, and makes that call indirect; the validator, which knows what the slot holds, inlines it in the term before (C3) |
| `string_get_checked.ml` | 21, 4 | the load of a character of a string that is a constant of the unit, at a constant index: the validator, which knows the string, has the character where Simplify, which resolves the bounds check as the validator does, keeps the load |
| `string_get_unknown.ml` | 28, 16 | the index is converted for the bounds test and again in the continuation that loads the character; Simplify converts it once and gives the result to that continuation as an argument, which the sharing of primitives does not do (V2) |
| `while_flag.ml` | 150, 75 | a boolean that Simplify keeps untagged in a parameter of the loop (T6) |

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
| `tupled_recursive.ml` | after Simplify the unit calls tupled code directly, giving it the components; the model has not got that call (C3) |
| `tupled_unknown_pair.ml` | as `tupled_recursive.ml` |

## What stops a unit from validating, most common first

1. A pair that is a parameter of the function, unboxed where two
   branches meet (three units). One branch gives the parameter, and
   Simplify loads its fields at that use, which only the subkind of
   the parameter justifies; the model has no subkinds, so the term
   after is less defined than the term before and no rewrite can be
   proved (`pair_join.ml`, `pair_kept.ml`; discrepancy T6-7).
   `pair_loop.ml` is the same at the entry of a loop, whose parameter
   Simplify unboxes from its subkind without looking at the uses.
2. A boolean that Simplify keeps untagged in a parameter of a loop
   (`while_flag.ml`).
3. The wrapper of a partial application whose closure stays
   (`partial_exported.ml`). The front end makes the wrapper, as code
   marked `stub`, with a direct call of the function through a value
   slot of the wrapper's own closure. Simplify simplifies the code of
   a stub where the code is bound and not where its closure is made
   (`middle_end/flambda2/simplify/simplify_static_const.ml`), so it
   does not know what the slot holds; and it makes of the direct call
   an indirect call of known arity, the code named being code that
   it has not simplified
   (`middle_end/flambda2/simplify/simplify_apply_expr.ml`). The
   validator, which knows what the slot holds, inlines the call in
   the term before only.
4. The validator knows more than Simplify in one unit
   (`string_get_checked.ml`): it evaluates the load of a character of
   a string that is a constant of the unit, at a constant index.
   Simplify resolves the bounds check, as the validator does, and
   keeps the load: `simplify_string_or_bigstring_load` of
   `middle_end/flambda2/simplify/simplify_binary_primitive.ml`
   answers that it knows nothing of the result, under a comment that
   says it could evaluate loads from known strings. The two terms
   then differ the other way.
5. A primitive computed before a `Switch` and again in the handler
   that an arm goes to (`string_get_unknown.ml`: the index of an
   access to a string is converted for the bounds test and again for
   the load). Simplify computes it once and gives the result to the
   handler as an argument; the sharing of primitives of the validator
   knows in a handler what was computed before its `Let_cont`, not
   what the body computes before it applies it.
6. A value slot that holds a symbol which is not in scope where the
   slot is read (`capture_fun_bound_in_handler_run.ml`). The closure
   of a function holds a value chosen by a test when the module
   runs, so its symbol is bound in the handler of that test; the
   code of a closure that calls the function is bound at the head of
   the unit and reads it from a value slot, where Simplify puts the
   symbol. The validation reads a slot only where the symbol it
   holds is in scope, and leaves this projection.

What the model has not got, and the conversion refuses: floating-point
arithmetic (`float_add.ml`), arrays (`array_literal.ml`), mutable
fields (`ref_counter.ml`), and a direct call of tupled code, which
gives the code the components (`tupled_recursive.ml`,
`tupled_unknown_pair.ml`): Simplify makes one of the call of a tupled
function that it knows and does not inline, so the term after is
refused where the term before is not.

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
- Exceptions (`try_no_raise.ml`, `mod_zero.ml`, `raise_inlined.ml`;
  twelve units). A `try` installs a handler and removes it. Where
  Simplify finds that nothing can raise to the handler any more, or
  that what is raised is known, it makes the handler an ordinary
  continuation and drops the trap actions. The validator does the
  same at the end of the normalisation of the term before, and after
  the last lifting, and goes through its rounds again
  (`FlambdaDemoteSpec.demote_handlers`,
  `FlambdaValidateSpec.demote_and_tidy`). The conversion keeps, for
  that, the `Let` by which a handler ends its region (see above).
- A continuation whose handler is one jump, bound above a `Let` and
  applied by an arm of a `Switch`, once a call is inlined
  (`option_inlined.ml`): the rounds of the first phase, which send
  the arm where the jump goes, are gone through again after the
  second (`FlambdaValidateSpec.demote_and_tidy`).
- A continuation of no parameters that Simplify leaves with a
  `Switch` on a parameter it removed, every application giving that
  parameter the same constant (`variant_blocks_join.ml`): Simplify
  binds the constant at the head of the handler and the `Switch`
  stays under that `Let`. The folding of constants of the validator
  makes the handler one jump in both terms; the term before has its
  applications forwarded, and the term after has them forwarded by
  an equivalence (`FlambdaForwardJumpsSpec.forward_jumps`, in
  `FlambdaValidateSpec.inline_once_applied_after`).
- Two arms of a `Switch` that give one continuation 0 and 1 (two
  generated units of `census/`): Simplify makes of them the tagging
  of what is tested, and so does the validator in both phases of the
  term before (`FlambdaMergeSwitchesSpec.merge_switches`).
- A field of a block loaded twice, once for each pattern of a match
  that looks at it (`list_last.ml`): a load marked immutable is one
  of the primitives that are not computed twice (`FlambdaCseSpec.v`).
- The tagging of a number that is the untagging of a variable
  (`variant_two_blocks.ml`, `variant_nested_match.ml`). A match on a
  variant gives each constant constructor its own number: the front
  end untags the scrutinee to test it, and the arms of those
  constructors pass their numbers as tagged constants, where
  Simplify makes them pass the scrutinee. The merging of the arms of
  a `Switch` makes of those arms the tagging of what is tested
  (`FlambdaMergeSwitchesSpec.merge_switches`). The sharing of
  primitives knows, under the `Let` of an untagging, that the
  variable untagged is the tagging of the result
  (`FlambdaCseSpec.computed_under_let`), so that tagging becomes the
  variable.
- A test against zero of the result of `compare`
  (`compare_tested.ml`, `compare_order.ml`,
  `int64_compare_tested.ml`). `compare a b < 0` reaches Simplify as
  a three-way comparison, the tagging of its result and a test of
  that against 0. Simplify makes the test a comparison of the two
  operands, and the three-way comparison goes where nothing else
  uses it. The validator does the same on the term before, with the
  compiler's table case for case
  (`FlambdaRecoverComparisonSpec.recover_known_comparisons`, T5b's).
- Two equal projections of a value slot, which a function inlined
  twice leaves in the term before (`exported_branch_calls_twice.ml`):
  the second is made the variable of the first
  (`FlambdaShareProjectionsSpec.share_known_projections`). Simplify
  finds that variable in the type of the closure, as it does for a
  field loaded twice.
- A variant, a pair or a boxed number unboxed where two branches
  meet, each branch building it (`option_join.ml`, `shape_heap.ml`,
  `pair_built.ml`, `int64_option_heap.ml`): Simplify gives the
  continuation the fields, with `poison` for those that a branch has
  not got, and the validator does the same in the first phase of the
  term before (`FlambdaUnboxVariantsSpec.unbox_variant_params`).
- A variant that is a constant block on one path and a constant
  constructor on the other, unboxed where they meet
  (`shape_constant.ml`): Simplify gives the continuation whether the
  value is an immediate and the field, which is that of the symbol
  of the constant block on one path and `poison` on the other. Under
  a test, the untagging of a symbol has no value, so the unboxing of
  parameters gives a constant in its place
  (`FlambdaUnboxVariantsSpec.no_value_on`).
- A boolean untagged where the two tests of the condition of a loop
  meet (`while_two_tests.ml`, a `while` with `&&`): the first test
  gives the number 0 and the second its comparison, with nothing
  tagged. Under a test, the unboxing of parameters gives, for an
  untagging, the number that a `Let` in scope tagged
  (`FlambdaUnboxVariantsSpec.made_number`).
- A self tail call made a jump (`tail_loop.ml`, `list_length.ml`,
  `list_rev.ml`): where the two terms are not the same as given, the
  validator makes loops of the self tail calls of the code it is told
  (`FlambdaLoopifySpec.v`), and the tool names the code that the front
  end marks for it. The recursive code is in the list of code to
  leave, so the call of the function stays on both sides and the two
  bodies are compared.
- A parameter of a loop that is only passed round the loop
  (`while_unused_counter.ml`): removed (`FlambdaDeadParamsSpec.v`).
- A continuation applied once that Simplify leaves in the term after,
  or that is applied once after the validation has inlined a call
  that Simplify left (`../kinds_partial_application.fl`; 46 of the
  generated units of `census/`): the term after has it moved to where
  it is applied and inlined there, where the checks of the passes
  permit, by equivalences
  (`FlambdaValidateSpec.inline_once_applied_after`).
- In the code of a function of which Simplify makes a loop, a `Let`
  of a parameter of the code that nothing uses (`string_sum.ml`): the
  term after loses it, with the parameters of the code in scope at
  their kinds (`FlambdaCodeLetsSpec.v`).
- A call of a variable bound to a closure of a set at a named function
  slot, which the rounds do not make direct (`tupled_function.ml`,
  whose tupled functions project their own function slot): where the
  validation fails, the tool asks it again with the aliases followed
  by the function that knows more of what is bound
  (`FlambdaValidateKnowingSpec.v`), which makes the call direct; a
  call that gives tupled code its tuple is then inlined
  (`FlambdaNormaliseSpec.inline_apply`). The verdict then has a
  second line that says so. With the rewrites from the types in the
  normalisation of the term before (the next point), that unit is
  validated at the first asking.
- A `Switch` on a variable, in a handler that only one arm of a
  `Switch` on the same variable applies (two generated units of
  `census/`): Simplify, which knows in the arm what the variable is,
  resolves the second. The rewrites that Simplify makes from the
  types are applied to the term before once, between two runs of the
  rounds of its second phase
  (`FlambdaSimplifyPassSpec.simplify_by_types`, in
  `FlambdaValidateSpec.normalise_before`): a handler that is applied
  once is rewritten under what is known where it is applied.
- A closure that calls a function of its module, made by a function
  that stays a function (`capture_fun_and_var_run.ml`,
  `capture_two_funs.ml`, `capture_rec_self.ml`, `over_rec.ml`): the
  closure holds the function in a value slot, and Simplify, which
  knows what the slot holds, makes the code of the closure call the
  symbol of the function. The validator replaces the projection of a
  value slot that every set of closures of the unit gives the same
  symbol or constant by that symbol or constant, where the symbol is
  in scope (`FlambdaKnownSlotsSpec.read_known_slots`, in each round
  of the normalisation of a term in which something was lifted).
- The return continuation of a call, bound above the `Let`s of the
  arguments of the call in the term before and below them in the
  term after (`call_result_unused.ml`, `call_result_tested.ml`; one
  generated unit of `census/`, and 56 of its units with loops).
  Where Simplify changes the parameter of the continuation (a result
  that the handler does not use is not passed; a boolean that an
  `if` tests is untagged), the call can no longer return to it:
  Simplify makes the call return to a new continuation, bound at the
  call, that applies the old one. The comparison is of the bindings
  in their order. The first comparison is of the two terms as they
  are given. Each term of the later comparisons has its
  continuations placed once the rounds are over: a `Let_cont` that
  is not recursive goes down to the call that returns to its
  continuation, or to the test of which an arm names it, where the
  guards of the pass permit. It passes a `Let` whose variable its
  handler does not use, a static binding, and the binding of another
  continuation that is not recursive if neither handler names the
  other; anything else between the two leaves it where it was
  (`FlambdaSinkUsesSpec.sink_conts_to_uses`, an equivalence, in
  `FlambdaValidateSpec.placed`).

A count over 600 units made at random is in `census/README.md`, with
one over 240 more that have exceptions, loops and recursive functions.

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
slots it removed, and where it fails it is made again at the second
asking. The 284 units here are checked in about ten seconds of
processor time together.

`FLSEMANTICS_PRINT_TERMS=1` makes the tool print, of a unit that is not
validated, two terms that the validation compared, for each list, and
how the term before was made: it is not always the last pair that was
compared.

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
  `-drawfexpr` prints (see "validated" above), as the tool's Simplify
  simplifies it. The printed term has no mark for a functor, for
  `[@cold]`, for opaque code or for the modes of parameters, and the
  parser gives each a default
  (`middle_end/flambda2/parser/fexpr_to_flambda.ml`). Simplify reads
  them. So the tool's Simplify can decide otherwise than the
  compiler's on the same unit. One case is known. For code with no
  inlining attribute, the decision made at its declaration
  (`make_decision0` of
  `middle_end/flambda2/simplify_shared/function_decl_inlining_decision.ml`)
  compares the size of the code with the thresholds for functors
  (`small_functor_size`, `large_functor_size`) if the code is marked
  as a functor, and with those for functions if not; a functor no
  larger than `small_functor_size` is to be inlined. The tool's
  Simplify, to which the functor is a function, compares it with
  the thresholds for functions and may leave the call. The pair
  validated is then not the pair that the compiler made (discrepancy
  V2-6). For code with `[@inline]` or `[@inline never]` that
  decision does not look at the mark of a functor; the other marks
  are lost for such code as for any other.
- The printed term loses kinds as well (found by X5, who compared
  the term in the compiler's memory with the term read back; nothing
  in the tree makes that comparison). Four of the losses are of
  something that Simplify reads, and with each the tool's Simplify
  knows less than the compiler's:
  - the kind of the result of an application, where the arity of the
    result is not written: the subkind is lost and the result is read
    as one that may be null, and the type of the result of a call
    that is not inlined comes from that arity
    (`T.unknown_types_from_arity` in
    `middle_end/flambda2/simplify/simplify_apply_expr.ml`);
    `identity.ml` has it;
  - the kinds of the fields of a `Make_block`, whose subkinds are
    lost (discrepancy V2-2): Simplify meets the type of each argument
    with the kind of its field (`simplify_make_block` in
    `middle_end/flambda2/simplify/simplify_variadic_primitive.ml`);
    `exported_list.ml`;
  - the kind of a value slot, an immediate being read as any value:
    it is the kind of a projection of the slot
    (`middle_end/flambda2/simplify/simplify_unary_primitive.ml`);
    `add3_exported.ml`;
  - the mark `[cold]` of a continuation handler, such as the handler
    of a failed bounds check, which is dropped (`DE.mark_as_cold` in
    `middle_end/flambda2/simplify/simplify_let_cont_expr.ml`);
    `string_get_checked.ml`.

  With one more the tool's Simplify is told more than the compiler's:
  a value that may be null is read as one that never is, wherever the
  text writes its kind. That is discrepancy T4-13, and the 13 units
  that have such a kind are counted apart (see "What the verdicts
  mean"). None of these losses makes a verdict wrong of the pair that
  the tool validates: they are a distance between that pair and the
  compiler's.

What no example here validates, because the model has not got it:
mutable fields and arrays, arithmetic on floats, calls of C functions
(polymorphic comparison among them), an exception that the unit
declares (it is made by a call of a C function), objects, laziness.
(`fst` and `snd` are in the model: the standard library declares them
with `%field0_immut` and `%field1_immut`, a load that cannot change,
with a tag and a size that are not known: `fst_snd.ml`. It is `!`, and
`%field0` written by hand, that load a field marked as one that may
change.)
