# T5b on the meet: slices of the proof of the contract of meet

Branch `flambda2-rocq/T5b-meet`, on T4's `flambda2-rocq/T4-meet`. T4
owns the meet, its contract and its statements, and leads; I prove
slices of the traversal that T4 has cut loose, in files of my own, to
statements that T4 fixes. Reviewer of the meet: R1. (My own stream,
the type traversal of the n-way join, is `status/T5b.md` on
`flambda2-rocq/T5b-join-types`.)

Files, in `middle_end/flambda2/types/rocq/`:

- `FlambdaMeetProductsSpec.v`, `FlambdaMeetProductsProofs.v`: slice 1.
- `FlambdaMeetHeadsSpec.v`, `FlambdaMeetHeadsProofs.v`: slice 3.

## The cut, as agreed with T4

1. Products (`FlambdaMeetProducts*`): `combine_results3`, `map_meet`,
   `meet_int_indexed_product` (with `meet_array_of_types`),
   `meet_function_type` (with `meet_code_id`), the two products
   indexed by slots, `meet_closures_entry`. Done.
2. Row-like structures (`FlambdaMeetRowLike*`): `meet_row_like` and
   its instances for blocks and for closures. Not started: it needs
   T4's statements about scopes (`Meet_env.enter_scope`,
   `Typing_env.cut`, the extension of a level, `add_defined_vars`,
   the join's contract), which T4 is writing.
3. Heads (`FlambdaMeetHeads*`): `meet_relation`, `meet_variant`,
   `meet_head_of_kind_value_non_null`, `meet_head_of_kind_value`, to
   T4's target: for every value `v`, `part_meet_ok` of
   `meet_head_of_kind_value` at "the type made of the head fits" and
   "`v` has the type made of the head".

T4 keeps: the scopes and `meet_disjunction`; the head of naked
immediates; `meet_expanded_head0`, the induction on fuel, `Meet.meet`
and the contracts of `Typing_env`; the instance for the compiler's
join.

What I may suppose, as premises under these names: `join` with
`join_scoped_envs_sound join`; `choices` with `define_again choices =
false` and `lift_variables_of_single_case choices = true`; `mh` with
`meet_expanded_head_keeps mh` and `meet_expanded_head_sound mh`.
Nothing else without telling T4.

## Slice 1: done

Ten statements, proved; `make -C rocq -j8 all` and
`make -C rocq assumptions` pass with them.

- `combine_results3_ok`: as T4's `combine_results2_ok`, for three
  meets. (`combine_results3` is `combine_results2` of the first meet
  and of `combine_results2` of the other two.)
- `map_meet_ok`: the meet of two maps is right if the meet of what
  they bind is. A map fits if its keys are distinct and what it binds
  fits; it is true if what it binds each key to is true for that key.
- `map_meet_keys`: an answer of the meet of two maps binds the keys
  that either input binds.
- `meet_int_indexed_product_ok`, `meet_int_indexed_product_length`:
  the fields of blocks; an answer has as many types as the longer
  input.
- `product_satisfied_fields`: what "true" is for the types of the
  fields, against T1's `fields_satisfied`.
- `meet_function_type_ok`.
- `meet_closures_entry_ok`, `meet_closures_entry_slots`: an answer
  has a type for a slot if one of the inputs has.
- `extract_value_answer`: `extract_value` is an answer.

Three choices in it, which T4 has agreed:

- "True" for a product is T1's predicate and that the value has every
  position that the product has a type for. T1's meaning asks nothing
  of the type of a field past the end of the block or of a slot that
  the set of closures has not, and the meet of two products meets the
  types of such a position all the same; with T1's predicate alone
  the statements are false. The index of the case and conditions 6
  and 8 of the well-formedness of types give the rest, in slice 2,
  for the fields of blocks, the function types and the value slots.
  For the closure types of an entry they do not (found by R1): see
  "Settled with T4 and T1" below.
- An entry of closures fits if it is well formed under some index:
  the two entries met are under two indices and the answer under a
  third. `meet_closures_entry_slots` and
  `meet_int_indexed_product_length` are what `meet_row_like` needs to
  put the answer under the index answered.
- The statements about keys, lengths and slots are about any answer
  (`meet_answer`): an input that the meet names, either if it names
  both, or the new thing. A meet of several parts that names its
  second input names it whole, though a part may have named both.

The statements follow T4's contract as it is now: the first half of
`meet_call_ok` has the new names (`new_names_avoided`), `type_fits`
has the kinds of the names of equations, and an entry of closures
that fits has them too. The kind of the type that
`Meet_env.meet_type` answers is in T4's `meet_type_keeps`; the
premise that stood for it here is gone.

## Slice 3: done, given the rows of blocks and of closures

In `FlambdaMeetHeadsSpec.v`, each proved:

- `meet_relation_ok`: the meet of two variables that stand for the
  result of one primitive on the value is right. Such a variable fits
  an environment that knows it and has it at the kind of naked
  immediates (`relation_variable_fits`), and is true where it holds
  the number that the primitive answers on the value
  (`relation_variable_satisfied`, T1's `variable_is`); the number may
  depend on the static environment. From T4's `add_alias_keeps` and
  `meet_env_add_alias_sound`.
- `meet_disjunction_answer`: what `meet_disjunction` answers for each
  of its two parts is the part of an input, the bottom of that side,
  or what the meet of that side answered (`side_answer`). It supposes
  nothing of environments or values.
- `meet_head_of_kind_value_non_null_ok`: the meet of two heads that
  are not null is right, for any value, if the meet of two variants
  (`meet_variant_parts`) and the meet of the rows of two sets of
  closures are. Both are premises in the form `type_part_meet_ok`: a
  part fits, and is true, as the type that it makes. Two heads of
  different constructors have no value in common (T1's
  `heads_compatible_satisfied`), but for a variant and a mutable
  block; no value has the type of a mutable block in T1's meaning,
  so every case with one is right whatever is answered, and what is
  answered fits.
- `meet_variant_ok`: the meet of two variants is right, if the meet
  of the rows of two sets of blocks is (a premise in the same form,
  at `blocks_type`: the variants that are blocks among them). By
  T4's `meet_disjunction_ok`, the alternatives being a tagged
  immediate and a block; the variable for `Is_int` holds 1 on a
  tagged immediate and 0 on a block, by `meet_relation_ok` at the
  number that reads which the value is. In the proofs: a variant
  fits exactly when its parts do (the lists of free variables, of
  aliases and of names of equations of a variant are those of its
  parts; an extension inside a type fits in T4's sense, by lookups,
  exactly when its lists do, its keys being distinct and the
  environment having its invariant).
- `meet_head_of_kind_value_ok`, T4's target: the meet of two heads
  that may be null is right, if the meet of two heads that are not
  null is. By `meet_disjunction_ok`, the alternatives being a value
  that is not null and null. T1's meaning says, of a value that is
  not null, that the variable for `Is_null` holds 0, which is about
  the other side: that is had from `meet_disjunction_answer` (the
  meet of that side answers the variable of an input, which the
  environment of the meet knew and which holds what it held).
- `meet_value_heads_ok`: the three together. The meet of two heads
  of kind value is right if the meets of the rows of blocks
  (`meet_row_like_for_blocks`) and of the rows of closures
  (`meet_row_like_for_closures`) are. Those two are slice 2, and
  what is left of the heads of kind value.

To come: slice 2.

## Settled with T4 and T1: a valid static environment

The closure types of an entry of closures, on a static environment
that is not valid (found by R1 in review). A closure bound to a
symbol is projected to another function slot g of its set only if
the static set names a symbol for g (`project_function_slot`), though
g is among the functions of the set (`closure_in_set`). T1's
`closures_entry_satisfied` asks nothing of the closure type at g
where the projection has no value. So a value has two entries whose
closure types at g have no value in common, and
`meet_closures_entry` answers bottom: on such a static environment
the meet loses a value. `meet_closures_entry_ok` was not touched (its
"true" asks that the projections have values), but the statement of
the rows of closures, in slice 2, cannot get that from the index and
the well-formedness alone. C3's `statics_valid` gives it
(`project_function_slot_valid_statement`).

T4 and T1 chose: the meaning stays, and every statement that says
that no value is lost supposes `statics_valid statics` (T4's
`meet_call_ok`, second half, and the contracts above it). The
statements here keep their form; the proofs take the hypothesis and
pass it on. T1 adds `well_formed_closures_case_closure_type`: with a
valid static environment, a well-formed case that is satisfied gives
the projection at each slot that has a closure type, and its type.
That is the bridge for slice 2.

## Found

Nothing of the compiler yet.
