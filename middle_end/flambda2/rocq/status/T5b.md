# T5b, the type traversal of the n-way join: status

Branch `flambda2-rocq/T5b-join-types`, on T5's
`flambda2-rocq/T5-join` at c1d72470da (which is on T2's 1af641592c).
T1's f90bcb7bf4 (the equality of types, monotonicity, D26 as amended)
is not under it yet. Files, all in `middle_end/flambda2/types/rocq/`:

- `FlambdaJoinTypes.v` (handed over by T5): the join functions of
  `types/meet_and_n_way_join.ml` and their helpers. Definitions only.
- `FlambdaJoinTypesSpec.v`: what the type traversal is proved to
  meet, and what it assumes of the other streams' functions.
- `FlambdaJoinTypesProofs.v`: the proofs.

The interface is T5's `FlambdaJoinSpec.v`, section "The join of
types, inside a join of environments", as at 2eba490876 (with the
kinds: `kind_in_target_env`, `state_kinded`). I do not change that
file.

## Done

- The plan below.
- First slice, transcription and proof: `join_alloc_mode`,
  `n_way_join_unknown`, `deduce_is_int(_simple)`,
  `deduce_get_tag(_simple)`, `n_way_join_relation_simples`, the
  `is_null` part of `n_way_join_head_of_kind_value`
  (`n_way_join_is_null`), `n_way_join_head_of_kind_naked_immediate`,
  the eleven joins of the other naked numbers as one, `rec_info`,
  `region`, `n_way_join_env_extension`.
- `join_step_sound` (Spec): what it is for a function of the
  traversal to be sound, for any things joined, in the words of
  `n_way_join_type_sound`, kinds included.
- One claim, `flat_heads_sound`: under `environment_side_sound` and
  `reduce_head_of_kind_naked_immediate_sound`, the eight conjuncts
  `n_way_join_unknown_sound`, `n_way_join_relation_simples_sound`,
  `n_way_join_is_null_sound`,
  `n_way_join_head_of_kind_naked_immediate_sound`,
  `n_way_join_head_of_kind_naked_numbers_sound`,
  `n_way_join_env_extension_sound_here`, `deduce_is_int_simple_sound`,
  `deduce_get_tag_simple_sound`.
- Validation at the tip: `make -C rocq -j16 all` (the claim is
  listed), `make -C rocq assumptions` (the statements of the Flambda 2
  libraries depend on no axiom). No OCaml or extracted file changes;
  the semantics tests were not run.
- Discrepancies T5b-1 and T5b-2.

## In progress

- Products, row-likes, variants, closures entries, then
  `n_way_join` and `n_way_join_type_sound` (steps 2 to 4 of the plan).

## Stand-ins carried

Each is a copy under its owner's names, to go with a change of
imports when the owner's file is under this branch.

| What | Owner | Copied from |
|------|-------|-------------|
| `Expanded_type` (`head`, `t`, `create`, `kind`, `descr`, `create_bottom`, `create_unknown`, `create_value`, `create_naked_immediate`, `create_naked_number`, `create_rec_info`, `create_region`, `unknown_like`, `to_type`) | T4, `FlambdaExpandHead.v` | a6d0e5357f on `flambda2-rocq/T4-meet` (the text is that of abf0ffd6f6) |
| `Keyed_fold.tabulate_fold_opt`, `filter_map_fold_on`, `filter_map_fold` | C0, to be in `Keyed` of `FlambdaMapSpec.v` | C0's message (not committed there yet); the text agreed |

## Agreed with other streams

- T5: the plan; `joined_env = None` is `None`; the first input is the
  one of least index; in B3 the test is `type_eqb other first`. The
  interface delta for kinds (2eba490876) is what the proofs are
  against. A symbol answered by the join of simples at kind naked
  immediate cannot happen under the contract's premises
  (`n_way_join_simples_sound` says a symbol is answered only at kind
  value); the two branches of the compiler for it are transcribed as
  they are.
- T4: the statements I take as premises are T4's
  `expand_head_sound`, `expand_head_closed`, `expand_head_kinded`,
  `expand_head_kind` (2ef422668c) and
  `reduce_head_of_kind_naked_immediate_sound` (to come, needs D26 as
  amended under T4's branch). `expand_head_kind` needs a premise on
  the constants that are canonical (T4-7); I take it under the
  abstract well-formedness of the interface. My
  `n_way_join_expanded_head` goes by the head, not by the kind.
- T1: `type_satisfied_monotone`, `type_satisfied_monotone_all`,
  `type_eqb`, `type_equal_kind`, `type_equal_satisfied`,
  `block_shape_eqb`, `boxable_number_eqb` are on f90bcb7bf4.
  `block_shape_element_kind` is mine to define (T1 will take it).
- C0: the fold, as above; I prove what I need from its equation.
- The orchestrator: D26 amended (18:55 UTC) on my report: `Is_null`
  relates poison to 0; only `Is_int` and `Get_tag` are never true of
  a scrutinee that holds poison.

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
| `type_eqb`: types that it identifies have the same kind and the same values | T1 (`FlambdaTypeEqualSpec.v`, on f90bcb7bf4, not under this branch yet) |
| `type_satisfied` is monotone when variables with no value are given one (`type_satisfied_monotone_all`) | T1 |
| the fold over a map that threads a state and may drop bindings (`Keyed.filter_map_fold_on`), with its equation | C0; a stand-in in my file until it lands |

The stand-ins are listed above.

## Found so far

- T5b-1: `n_way_join` has no bound on its depth and no test for a
  cycle (the binary join has one); on two inputs that are an alias
  and a type in turn it does not terminate. By reading; not
  demonstrated; T7 has the two environments.
- T5b-2: the join gives an `is_null` variable to a join one of whose
  inputs is `Not_null`, which says `Is_null` is 0 of a poison value
  of that input. An unchecked assumption; it is why D26 was amended.
- Met again here: R1-16 (the empty set given to
  `create_naked_immediates_non_empty`: `None` in the model), X3-5
  (the joined relations are dropped when the join of the variant is
  unknown: transcribed as it is).
- A mistake of mine that the proof found: a pattern in
  `n_way_join_head_of_kind_naked_immediate` that kept the tail of
  the set of numbers. Fixed before the first request.

## Open questions

None for the human.
