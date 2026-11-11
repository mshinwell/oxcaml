# T5b, the type traversal of the n-way join: status

Branch `flambda2-rocq/T5b-join-types`, cut from T5's
`flambda2-rocq/T5-join` at 132ba2d396 (on T2's 0ca4818b80, T1's
e644383b6e, with T3's commits). Files, all in
`middle_end/flambda2/types/rocq/`:

- `FlambdaJoinTypes.v` (handed over by T5): the join functions of
  `types/meet_and_n_way_join.ml` and their helpers. Definitions only.
- `FlambdaJoinTypesSpec.v`: what the type traversal is proved to
  meet, and what it assumes of the other streams' functions.
- `FlambdaJoinTypesProofs.v`: the proofs.

The interface is T5's `FlambdaJoinSpec.v`, section "The join of
types, inside a join of environments". I do not change that file.

## The plan

### What is transcribed

The compiler is the integration branch's with the change of
`n_way_join_closures_entry` (a function type is kept only if every
entry has one). Lines are those of `types/meet_and_n_way_join.ml`
before that change, which moves nothing above line 2920.

Helpers:

| Function | Lines | In the model |
|----------|-------|--------------|
| `map_join_result`, `let>>+` | 49-51 | in full |
| `join_alloc_mode` | 768-773 | in full (`unknown ()` is `Heap_or_local`, as in the grammar) |
| `n_way_join_unknown` | 790-801 | in full |
| `n_way_join_head_of_kind_naked_number` | 803-805 | in full |
| `generic_merge_map_known` | 807-865 | in full, on the maps of the model, with the fold that threads the state |
| `deduce_is_int`, `deduce_is_int_simple` | 867-878 | in full |
| `deduce_get_tag`, `deduce_get_tag_simple` | 880-901 | in full |
| `n_way_join_relation_simples` | 903-915 | in full |
| `join_array_element_kinds` | 936-950 | left out: the grammar has no arrays |
| `reduce_head_of_kind_naked_immediate` | 952-1006 | T4's; a parameter here |

The thirty join functions:

| Function | Lines | In the model |
|----------|-------|--------------|
| `n_way_join` | 1885-1913 | in full; fuel is spent here |
| `n_way_join_expanded_head` | 1915-2106 | in full; the eleven cases of the naked numbers other than immediates are one |
| `n_way_join_head_of_kind_value` | 2108-2173 | in full |
| `n_way_join_head_of_kind_value_non_null` | 2175-2493 | `Variant`, `Mutable_block`, the nine boxed numbers as one, `Closures`, `String`; `Array` left out |
| `n_way_join_array_contents` | 2495-2548 | left out with arrays |
| `n_way_join_variant` | 2550-2586 | in full |
| `n_way_join_head_of_kind_naked_immediate` | 2588-2617 | in full |
| `n_way_join_head_of_kind_naked_float32` to `..._naked_mask` (eleven) | 2619-2661 | one function, the kind an argument |
| `n_way_join_head_of_kind_rec_info` | 2663-2666 | the head is `unit` in the grammar: always known |
| `n_way_join_head_of_kind_region` | 2668-2670 | in full |
| `n_way_join_row_like` | 2678-2804 | in full |
| `n_way_join_row_like_for_blocks` | 2806-2849 | in full |
| `n_way_join_row_like_for_closures` | 2851-2893 | in full |
| `n_way_join_closures_entry` | 2895-2953 | in full (the function types are there already) |
| `n_way_join_generic_product` | 2955-3008 | in full |
| `n_way_join_function_slot_indexed_product`, `n_way_join_value_slot_indexed_product` | 3010-3034 | in full |
| `n_way_join_int_indexed_product` | 3036-3096 | in full, with the test of `-flambda2-join-sharing structural` in place of `!=` |
| `n_way_join_function_type` | 3098-3131 | there already; no `rec_info` in the grammar |
| `n_way_join_env_extension` | 3133-3139 | in full: the environment's function, bottom made the empty extension |

A fatal error of the compiler, an `assert false` and an exception
that nothing catches are `None`: the join of zero types, the mismatch
of kinds that `n_way_join` tests, a head of another kind in
`n_way_join_expanded_head`, an environment that has no such index, an
empty set given to `create_naked_immediates_non_empty` (R1-16), a
symbol answered by the join of the `is_null` simples, the two fatal
errors of `n_way_join_row_like_for_closures`, a field index outside a
mixed shape. No other `None` but fuel.

### The shape of the recursion

Every cycle among the thirty goes through `n_way_join`. So:

- every function but `n_way_join` is an ordinary definition, in a
  `Section` whose variables are the abstract state with
  `joined_env`, the three functions of the environment side
  (`n_way_join_simples`, `import_type`, `n_way_join_env_extension`),
  T4's `expand_head` and `reduce_head_of_kind_naked_immediate`, T1's
  `type_eqb`, and `n_way_join_rec`, the join of types that the
  function calls on the parts of its arguments
  (`n_way_join_expanded_head` is also a recursion on its list);
- `n_way_join_body n_way_join_rec` is the compiler's `n_way_join`;
- `n_way_join fuel` is `fun _ _ => None` at 0 and
  `n_way_join_body (n_way_join fuel)` at a successor.

Fuel is needed, not only convenient: `Expand_head` goes from an alias
to a type of the environment, which is no part of the type joined, so
no measure on the types given decreases. (See "Found so far" for a
pair of inputs on which I believe the compiler's function does not
terminate.)

### The shape of the proof

`n_way_join_type_sound` of `n_way_join fuel`, for every fuel, by
induction on the fuel: at 0 the function answers nothing, and at a
successor it is the body applied to a function that is sound by the
induction hypothesis. So the theorem to prove is: if `n_way_join_rec`
meets `n_way_join_type_sound`, so does `n_way_join_body
n_way_join_rec`. T1's `types_induction` is not what the top-level
proof goes by (the function is not a recursion on one type); it is
behind the statements I take from T1 (monotonicity) and may serve for
what is said of every part of a type.

One predicate says what it is for a function of the traversal to be
sound, for any type of argument and of answer (`join_step_sound`): the
invariant is kept, the state grows, the answer is in the target, and
the answer holds under every valuation that extends an input's
wherever that input's argument holds. Each of the thirty has it, with
its own "holds" (`type_satisfied`, `head_of_kind_value_satisfied`,
`row_like_for_blocks_satisfied`, ...), and the proofs compose by
three facts about the interface: `state_grows` is transitive,
`extends_input` at a later state gives it at an earlier one, and
scope and kindedness of arguments do not depend on the state beyond
`joined_env`.

The premises that go down with the arguments: `join_args_distinct`
(each list made for a part has at most one element for each element
of the list it was made from), `join_args_in_scope` and the
kindedness of each part (from `free_variables` and
`aliases_with_kinds`, which list the parts' own).

### Order

1. The heads with no nested types, end to end (first review
   request): `join_step_sound` and the three facts above;
   `n_way_join_unknown`; the naked numbers; `rec_info`, `region`;
   the naked immediates (with T4's reduction as a parameter);
   `deduce_is_int`, `deduce_get_tag`, `n_way_join_relation_simples`;
   the `is_null` part of `n_way_join_head_of_kind_value`;
   `n_way_join_env_extension`; `join_alloc_mode`.
2. Products: `n_way_join_generic_product`, the two slot-indexed
   products, `n_way_join_int_indexed_product` (with `type_eqb` and
   `import_type`), `n_way_join_closures_entry`.
3. Row-likes: `generic_merge_map_known`, `n_way_join_row_like`, for
   blocks and for closures.
4. `n_way_join_variant`, `n_way_join_head_of_kind_value_non_null`,
   `n_way_join_head_of_kind_value`, `n_way_join_expanded_head`,
   `n_way_join_body`, the fuel, and `n_way_join_type_sound`.

## What is assumed, and of whom

Hypotheses of the statements (no axiom, nothing admitted). Each is a
named proposition in `FlambdaJoinTypesSpec.v` until its owner's file
is on my base.

| Assumed | Owner who discharges it |
|---------|-------------------------|
| `n_way_join_simples_sound`, `import_type_sound`, `n_way_join_env_extension_sound`, `valid_states_have_witnesses` (`FlambdaJoinSpec.v`) | T5 |
| `expand_head`: a value of a type has the expanded type under a valuation that satisfies the environment strictly; the expansion is in scope and kinded where the type and the environment are; it is of the kind of the type | T4 (with T2) |
| `reduce_head_of_kind_naked_immediate`: a number that has a head, under a valuation that satisfies the environment strictly, has the reduced head, which is then not bottom | T4 |
| `type_eqb`: types that it identifies have the same kind and the same values | T1 (`FlambdaTypeEqualSpec.v`, 6175977ea4, not on my base) |
| `type_satisfied` is monotone when variables with no value are given one (`type_satisfied_monotone_all`) | T1 |
| the fold over a map that threads a state and may drop bindings (`Keyed.filter_map_fold_on`), with its equation | C0; a stand-in in my file until it lands |

Stand-ins carried in my files until the base has the owner's: T4's
`Expanded_type` (the type and its creation functions, copied from
T4's `FlambdaExpandHead.v` under the same names), C0's fold.

## Found so far

- A pair of inputs on which, by reading, `n_way_join` does not
  terminate: at each depth one input is an alias and the other is
  not, so the join of simples is never reached and `Expand_head`
  keeps supplying types from the environments. Not demonstrated. To
  be written up as T5b-1 with the inputs, and given to T7 or X5.

## Open questions

None yet for the human.
