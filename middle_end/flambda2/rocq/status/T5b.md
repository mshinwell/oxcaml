# T5b, the type traversal of the n-way join: status

Branch `flambda2-rocq/T5b-join-types`, on T5's `flambda2-rocq/T5-join`
(which is on T2's branch, and that on the integration branch). Under
it now: T1's second request (the equality of types, the boxable
numbers, D26 as amended in `relation_holds`), T2's kinds of
environments, the folds of `Keyed`, T1's third request, and T5's
proofs that the three functions of the environment side meet their
contracts. Not under it yet: T4's files. Files, all in
`middle_end/flambda2/types/rocq/`:

- `FlambdaJoinTypes.v`: the join functions of
  `types/meet_and_n_way_join.ml` and their helpers. Definitions only.
- `FlambdaJoinTypesSpec.v`: what the type traversal is proved to
  meet, and what it assumes of the other streams' functions.
- `FlambdaJoinTypesProofs.v`: the proofs.
- `FlambdaJoinTypesKeepsSpec.v`, `FlambdaJoinTypesKeepsProofs.v`:
  what the join of types does to the state, with no premise on the
  state or the types.
- `FlambdaJoinTypesWithEnvSpec.v`, `FlambdaJoinTypesWithEnvProofs.v`:
  the join of types with the functions of the join of environments,
  which is what the join of environments is given for its rounds.
- `FlambdaJoinTypesExamplesSpec.v`,
  `FlambdaJoinTypesExamplesProofs.v`: what the transcription answers
  on small types, by computation.

The interface is T5's `FlambdaJoinSpec.v`, section "The join of
types, inside a join of environments". I do not change that file.

## Done

- The transcription: the thirty join functions and their helpers
  (the tables below).
- `n_way_join_sound`: for every number that bounds its depth, the
  join of types meets `n_way_join_type_sound`, the contract that the
  join of environments assumes of it, under the six named premises
  of the Spec ("What is assumed" below).
- `n_way_join_bound_is_met`: its corollary with the witnesses of
  valid states: where the join answers a type, a value of a type
  given has it under some valuation of the target that extends the
  input's.
- `flat_heads_sound`: the eight conjuncts of the first slice.
- `n_way_join_keeps`: a reflexive and transitive relation on states
  that the three functions of the environment side keep is kept by
  the join of types, at every state and for every list of types.
  `n_way_join_keeps_definitions`: its instance at T5's
  `keeps_definitions`, with the three functions of `Join_env`; it
  is `join_of_types_keeps_definitions` (`FlambdaJoinEnvSpec.v`) of
  the model's join of types, which T5's statements about the rounds
  of the join of environments suppose of the join of types that
  they are given. T5 asked for it.
- `n_way_join_of_types_sound` (`FlambdaJoinTypesWithEnvSpec.v`):
  `n_way_join_of_types`, the traversal with the three functions of
  `Join_env` and T1's `type_eqb` and `block_shape_eqb`, meets
  `n_way_join_type_sound` at T2's `typing_env_invariant` and T5's
  `state_valid`, `state_kinded` and `kind_in_target_env`. Premises:
  mine of `expand_head` and of the reduction of naked immediates
  (T4's functions, still arguments), and those of T5's theorems
  (`fresh_avoids p`, `env_extension_eqb_sound p`). No premise about
  the constants of
  the environments joined, nor about the tests of equality.
  `n_way_join_of_types_keeps_definitions`: the same function keeps
  the definitions, with no premise. T5 asked for both.
- Twenty-nine examples, each an equation proved by computation:
  unions of sets of numbers and of strings, constants and other
  aliases, unknown and bottom inputs, heads of two forms, blocks of
  one tag (fields joined, or kept where they are the same; two
  sizes; two shapes), of two tags (a variable for `Get_tag`), a
  constant constructor and a block (a variable for `Is_int`), two
  variants, closures (one code, two codes, one input with no
  function type: T1-4), and the answers that are `None` (no type,
  two kinds, the bound reached, a closure type of another kind,
  T5b-3). The environment side of the
  examples is a stub defined in the file, not the join of
  environments; the two tests of equality are T1's. No answer was
  read off a run of the compiler.
- Proved on the way, each stated with its proof in
  `FlambdaJoinTypesProofs.v`, in the form of `join_step_sound` or
  what it becomes for a function that takes several lists or may
  answer bottom: `n_way_join_generic_product`,
  `n_way_join_int_indexed_product`, `n_way_join_closures_entry`,
  `generic_merge_map_known`, `n_way_join_index`, `n_way_join_case`,
  `n_way_join_knowns`, `n_way_join_row_like_for_blocks`,
  `n_way_join_row_like_for_closures`, `n_way_join_variant`,
  `n_way_join_head_of_kind_value_non_null`,
  `n_way_join_head_of_kind_value`, `n_way_join_expanded_head`,
  `n_way_join_body`.
- Validation at the tip: `make -C rocq -j8 all`,
  `make -C rocq assumptions` (the statements of the Flambda 2
  libraries depend on no axiom). No OCaml or extracted file changes;
  the semantics tests were not run.
- Discrepancies T5b-1, T5b-2 and T5b-3.

## Reviews

Reviewer R4.

- Heads with no types inside (the first slice): signed, with one fix
  of wording in the header of the Spec, made.
- Products and closures entries; row-like structures: being read.
- Variants and heads of kind value; expanded heads, the body, the
  bound on the depth and the two closed statements: asked.
- The two statements of `FlambdaJoinTypesKeepsSpec.v`: signed.
- The definition and the two statements of
  `FlambdaJoinTypesWithEnvSpec.v`, and the examples (the stub
  environment side and each equation against the compiler's code):
  asked.
- R4 asked that the premise `joined_envs_constants_of_kind` stay in
  the statements that are for any well-formedness of environments,
  and go only where the invariant gives that aliases are
  consistent. Done so.
- R4 asked where the kind of an expansion comes from, and that no
  condition on kinds be hidden in the well-formedness of
  environments: see "Decided overnight".

## Stand-ins carried

A copy under its owner's names, to go with a change of imports when
the owner's file is under this branch.

| What | Owner |
|------|-------|
| `Expanded_type` (`head`, `t`, `create`, `kind`, `descr`, `create_bottom`, `create_unknown`, `create_value`, `create_naked_immediate`, `create_naked_number`, `create_rec_info`, `create_region`, `unknown_like`, `to_type`) | T4, `FlambdaExpandHead.v` |

`expand_head` and `reduce_head_of_kind_naked_immediate` are
parameters of the traversal, with what is assumed of each a named
proposition of the Spec; they become T4's functions and theorems
when those are under this branch. `type_eqb` and `block_shape_eqb`
are parameters of the traversal too; `n_way_join_of_types` gives it
T1's. The fold over a map that threads a state is C0's
(`Keyed.filter_map_fold`); my copy is gone.

## Agreed with other streams

- T5: the plan; `joined_env = None` is `None`; the first input is the
  one of least index; in B3 the test is `type_eqb other first`. A
  symbol answered by the join of simples at kind naked immediate
  cannot happen under the contract's premises
  (`n_way_join_simples_sound` says a symbol is answered only at kind
  value); the two branches of the compiler for it are transcribed as
  they are. The proofs need nothing of the state beyond the four
  contracts of `FlambdaJoinSpec.v`.
- T4: the statements I take as premises are T4's of `expand_head`
  (values kept, scope, kinds, the kind of the expansion) and of
  `reduce_head_of_kind_naked_immediate` (no value lost), which T4
  has proved under T1's law of the relations of constants after D26
  was amended. The kind of the expansion is T4's statement word for
  word: it needs `constants_of_kind` of the environment (T4-7). My
  `n_way_join_expanded_head` goes by the head, not by the kind.
- T2 and T5: `constants_of_kind` of the environments joined is to
  follow from the kinds premise of the contract, when T2's
  `typing_env_kinded` (the types kinded, the aliases of one kind,
  the symbols of kind value) replaces T5's under the same name; T5
  tells me when. Done: `n_way_join_of_types_sound` has no such
  premise. The statements that are for any well-formedness keep it
  (R4).
- T5: no second form of `n_way_join_keeps` is needed for the kinds
  of the variables of the state: `n_way_join_sound` gives
  `state_grows` at valid states, which is where T5 uses it.
- T1: `type_eqb` identifies types with the same values;
  `block_shape_eqb` decides equality. `type_satisfied_coincide` is
  what the proofs use where a type is imported as it stands (no
  monotonicity is needed). `block_shape_element_kind` is mine to
  define (T1 will take it).
- C0: the fold, as above; I prove what I need from its equation.
- The orchestrator: D26 amended on my report: `Is_null` relates
  poison to 0; only `Is_int` and `Get_tag` are never true of a
  scrutinee that holds poison.

## What is transcribed

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
| `n_way_join_function_slot_indexed_product`, `n_way_join_value_slot_indexed_product` | 3010-3034 | in full; the first with the test of kinds of the creation function of its product |
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
mixed shape, a joined closure type that is not of kind value (the
test of `Product.Function_slot_indexed.create`, which R4 found
missing from the transcription). No other `None` but fuel.

## The shape of the recursion

Every cycle among the thirty goes through `n_way_join`. So:

- every function but `n_way_join` is an ordinary definition, in a
  `Section` whose variables are the abstract state with
  `joined_env`, the three functions of the environment side
  (`n_way_join_simples`, `import_type`, `n_way_join_env_extension`),
  `expand_head` and `reduce_head_of_kind_naked_immediate`, `type_eqb`
  and `block_shape_eqb`, and `n_way_join_rec`, the join of types that
  the function calls on the parts of its arguments
  (`n_way_join_expanded_head` is also a recursion on its list);
- `n_way_join_body n_way_join_rec` is the compiler's `n_way_join`;
- `n_way_join fuel` is `fun _ _ => None` at 0 and
  `n_way_join_body (n_way_join fuel)` at a successor.

Fuel is needed, not only convenient: `Expand_head` goes from an alias
to a type of the environment, which is no part of the type joined, so
no measure on the types given decreases (T5b-1).

## The shape of the proof

`n_way_join_type_sound` of `n_way_join fuel`, for every fuel, by
induction on the fuel: at 0 the function answers nothing, and at a
successor it is the body applied to a function that is sound by the
induction hypothesis. So what is proved is: if `n_way_join_rec` meets
the contract, so does `n_way_join_body n_way_join_rec`
(`n_way_join_body_is_sound`).

One predicate says what it is for a function of the traversal to be
sound, for any type of argument and of answer (`join_step_sound`):
the invariant is kept, the state grows, the answer is in the target,
the answer holds under every valuation that extends an input's
wherever that input's argument holds, and it is kinded in the target
if the state is kinded. Each function has it with its own "holds"
(`type_satisfied`, `head_of_kind_value_satisfied`,
`row_like_for_blocks_satisfied`, ...), and the proofs compose by
three facts about the interface: `state_grows` is transitive,
`extends_input` at a later state gives it at an earlier one, and
scope and kindedness of arguments do not depend on the state beyond
`joined_env`.

Where the compiler's own structure is generic, so is the proof: the
fold over a map that threads the state, `generic_merge_map_known`,
and the join of cases and of their indices are proved once, for any
index, shape and thing mapped to, and used for blocks and for
closures; the five sorts of head of `n_way_join_expanded_head` go by
one lemma.

Three things that the proofs rest on and that a reader may want to
check first:

- a key for which cases were gathered is never dropped by
  `generic_merge_map_known`, because the join of the cases of one key
  is not bottom (there is at least one case, and the join of the
  shapes of some cases is not bottom);
- the variable joined for `Get_tag` is given no `Simple` by a variant
  with no block, and is asked for the tag of no block of it;
- `n_way_join_variant` answers the state of before the extensions
  were joined when both joined extensions are empty: the answer then
  mentions nothing made since.

## What is assumed, and of whom

Hypotheses of the statements (no axiom, nothing admitted). Each is a
named proposition in `FlambdaJoinTypesSpec.v` until its owner's file
is on my base.

| Assumed | Where it stands |
|---------|-----------------|
| `environment_side_sound`: `n_way_join_simples_sound`, `import_type_sound`, `n_way_join_env_extension_sound`, `valid_states_have_witnesses` (`FlambdaJoinSpec.v`); the last is used by `n_way_join_bound_is_met` only | T5 has proved the four of the functions of `Join_env`, under `fresh_avoids p` and `env_extension_eqb_sound p`; those two are the premises of `n_way_join_of_types_sound` in its place |
| `expand_head_sound`: a value of a type has the expanded type under a valuation that satisfies the environment strictly; the expansion is in scope and kinded where the type and the environment are; it is of the kind of the type where the type is kinded and the environment has `constants_of_kind` | T4; a premise of `n_way_join_of_types_sound` until T4's files are under this branch |
| `joined_envs_constants_of_kind`: in each environment joined, a constant that is the canonical element of a `Simple` of a kind is of that kind | discharged in `n_way_join_of_types_sound`, from the contract's kinds premise and the invariant of typing environments (T2's `typing_env_kinded_constants_of_kind`) |
| `reduce_head_of_kind_naked_immediate_sound`: a number that has a head, under a valuation that satisfies the environment strictly, has the reduced head, which is then not bottom | T4, who has proved it with no premise on its branch; a premise of `n_way_join_of_types_sound` until T4's files are under this branch |
| `type_eqb_sound`: types that the test identifies have the same values | discharged with T1's `type_eqb` (`type_equal_satisfied`) |
| `block_shape_eqb_sound`: shapes that the test identifies are one shape | discharged with T1's `block_shape_eqb` |

## Decided overnight

- Where the kind of what `Expand_head` answers comes from. An alias
  whose canonical element is a constant expands to the type of the
  constant, whatever the kind of the alias (T4-7), so the join needs
  `constants_of_kind` of each environment joined to answer a type of
  the kind of the types given. The contract of the join of types has
  no premise that gives it. Options: (a) a condition of structure in
  the well-formedness of environments (the type of a name that is
  not canonical is the alias type of its canonical element): the
  compiler's environments do not have it (T2; T4-10); (b) a premise
  of my statements, about kinds only, beside the contract's
  `joined_envs_kinded`; (c) the contract's kinds premise asks the
  aliases of each use to be of one kind (`aliases_kinded`), from
  which it follows. Chosen: (b) now, as `joined_envs_constants_of_kind`
  with a `CR mshinwell` at its definition, and (c) asked of T5 and
  T2, who have done it. Why: kinds stay explicit premises and out of
  well-formedness (D10, D12; R4's reading). Where it stands: the
  statements for any well-formedness of environments keep (b); the
  statement at the invariant of typing environments
  (`n_way_join_of_types_sound`) has it from (c) and asks nothing
  more. What stays for the human: (c) makes "the aliases of each
  environment joined are of one kind" a premise of the contract;
  whether ill-kinded code that the compiler accepts can break it is
  not known (T5b-3).

- What the examples run on. Options: (a) the join of environments
  itself, on typing environments built for each example: the
  answers would show the types given to the variables made, and the
  terms would be large; (b) a stub of the environment side, defined
  in the examples file: a counter for the state, empty
  environments, the join of `Simple`s answering the `Simple` if all
  are the same and a variable made otherwise. Chosen: (b), with a
  header that says so and says that no answer was read off a run of
  the compiler. Why: the examples are there to show what the
  traversal computes, and the orchestrator asked for a small file.
  Cost to change: the equations are stated again over (a); nothing
  else depends on them.

## Found so far

- T5b-1: `n_way_join` has no bound on its depth and no test for a
  cycle (the binary join has one); on two inputs that are an alias
  and a type in turn it does not terminate. Shown by T7 with a test
  of the types library on two such environments (the stack
  overflows, in the n-way and in the binary join); not shown from a
  source program.
- T5b-2: the join gives an `is_null` variable to a join one of whose
  inputs is `Not_null`, which says `Is_null` is 0 of a poison value
  of that input. An unchecked assumption; it is why D26 was amended.
- T5b-3: the join trusts the kinds of what `Expand_head` answers.
  An alias of one kind whose canonical element is a constant of
  another expands to a head of the constant's kind, and
  `n_way_join_expanded_head` then meets its `assert false`, or
  answers a type of another kind than the types given. An unchecked
  assumption (that aliases are of one kind); the example
  `example_join_alias_of_another_kind` shows the first on the stub.
  The test that would show it in the compiler is described in the
  entry and was not run.
- Met again here: R1-16 (the empty set given to
  `create_naked_immediates_non_empty`: `None` in the model), X3-5
  (the joined relations are dropped when the join of the variant is
  unknown: transcribed as it is), T4-7 (the kind of an expansion:
  "Decided overnight").
- A mistake of mine that the reviewer found: the creation function of
  a product of function slots stops on a component that is not of
  kind value, and the transcription did not. Fixed; every creation
  function that the join functions call was then read for such a
  test, and that one is the only one (the empty set of R1-16 was
  there already).
- A mistake of mine that the proof found: a pattern in
  `n_way_join_head_of_kind_naked_immediate` that kept the tail of
  the set of numbers. Fixed before the first request.

## What is left

- T4's `Expanded_type`, `expand_head` and
  `reduce_head_of_kind_naked_immediate` and their theorems, when
  T4's files are under this branch: a change of imports, two
  arguments and two premises fewer in `n_way_join_of_types` and its
  statement; no proof changes shape.
- The examples against the compiler by running: asked of T7.
- Arrays, when the grammar has them (`Array`,
  `n_way_join_array_contents`, `join_array_element_kinds`).
- Code age and `rec_info`, with the function types.

## Asked of me next

- T5 is proving a stronger invariant of the state (`state_true`: the
  equations of the target made so far are true) and will ask for
  `n_way_join_type_sound` of `n_way_join_of_types` at it: an
  instance of `n_way_join_sound`, when T5 sends its statements.

## Open questions

None for the human.
