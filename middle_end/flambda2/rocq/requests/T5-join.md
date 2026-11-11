# T5: the contract of the n-way join, and how to divide the work

Branch `flambda2-rocq/T5-join`. For the reviewer (R1), the orchestrator
and the human. The contract is `types/rocq/FlambdaJoinSpec.v`; this
note explains it, says what is not settled, and proposes how to split
the transcription. Paths are from `middle_end/flambda2/`.

## 1. The contract in one page

The join is given a **source** environment (in Simplify: the handler's
environment before anything is known of the uses, parameters defined;
in the meet: the environment of the meet), a scope, and a list of
**use** environments with the caller's identifiers. It answers the
**target** (the source with one more level) and an **analysis**.

`join_guarantees`, for inputs that are well formed and kinded:

1. **Upper bound under one extension** (`join_admits_use`). For each
   use and each valuation that satisfies that use and the source
   strictly, some valuation satisfies the target strictly, gives every
   variable that the use or the source knows, and that had a value,
   that value, and gives every variable that has a definition in the
   analysis the value of that definition at that use, where it has
   one. One valuation for all the equations of the target. (A variable
   with no value may get one: the join can make it an alias of a
   constant where the use has for it a type that nothing has.)
2. **The target is the source extended** (`join_keeps_source`): same
   earlier levels, scope, symbols; every name keeps its binding time
   and name mode.
3. **Names** (`join_introduces`): a variable the target knows and the
   source does not is in types only, and is either known to a use that
   is not bottom (imported under its own name) or outside the list of
   names to avoid (made by the join). Membership only; which name is
   made is not specified (agreed with N1: the join takes `avoid`, and
   a `fresh` function is an argument of the implementation).
4. **The analysis** (`analysis_describes_uses`): its identifiers are
   those of uses that are not bottom; a definition is of a variable of
   the target of the kind given, by a `Simple` of that kind at the
   use; one at the normal name mode may occur in terms at that use.
5. The target is well formed (the typing environment's invariant, a
   parameter until that file names it).

In the machine (`join_guarantees_in_machine_statement` and
`join_admits_use_in_machine_statement`, proved): if a variable that
may occur in terms in the source may occur in terms at each use, a
state that satisfies a use satisfies the target, and the witness gives
a variable with a normal-mode definition the value the machine has for
that `Simple`. That is what entitles `join_points.ml` to add a
parameter for such a variable and pass the `Simple` at each use.

Inside the join, the functions on types are specified against a
reading of the join's state (`n_way_join_type_sound`,
`n_way_join_simples_sound`): a value of an input's type has the joined
type under any valuation of the target that extends that input's.

Proved now (ten statements, no axioms): the three in-the-machine
corollaries; what a constant in the analysis means, and that the two
lists Simplify folds over hold what the vectors have at their indices;
that the contract is met by the join that answers the source and is
not met by one that answers bottom (so it is neither contradictory nor
empty); and the two about closures below.

**What it does not yet cover of Simplify's joins.** The contract is a
foundation for runs in which one valuation satisfies a use and the
source strictly, through environments that are kinded. Outside it:

- a use made by variant unboxing with a poison argument (D26, T5-7;
  the unboxing workstream owes what holds at a join after an unboxed
  continuation);
- a source that holds the types of constants lifted in other branches
  (T5-4; the continuations workstream owes that the valuation of a use
  satisfies the source, once T2 has said where the type of a symbol
  may be used);
- a use environment that is not kinded: an alias at a kind that is not
  the kind the environment has for its target (T5-9). Ill-kinded code
  may make these; the compiler's join does not test for them when it
  makes a variable of a kind for simples, and with the depth limit it
  can answer without ever testing. `uses_kinded` is a premise, not an
  invariant claimed of the compiler's inputs.

## 2. What Simplify may read of the analysis

- `fold_variables_created_at_join` (`join_points.ml`): for each
  variable with a normal-mode definition, the `Simple` at each use. It
  may pass that `Simple` as an extra argument at that use for a new
  parameter that it declares equal to the variable. Despite the name,
  such a variable can be one of the source (a parameter chosen as the
  representative of an existential): the caller already skips those
  that have a normal-mode canonical.
- `simple_refined_at_join` with `fold_values_at_uses`
  (`simplify_switch_expr.ml`, `specialization_cost.ml`): `Known c` at
  a use means the variable is `c` there
  (`known_value_at_use_statement`). `Unknown` and
  `Not_refined_at_join` mean nothing (the source has a comment saying
  the latter is not accurate). Both callers use it for a decision
  (specialise or not, cost), which is out of scope; no rewrite rests
  on it.

## 3. Decisions in the contract, and what is not promised

- **Partial valuations, strict satisfaction.** Found while agreeing
  the interface with T4 and T2. The n-way join imports a variable that
  only some uses define, with the join of its types over those uses,
  and makes existentials for vectors that cover only some uses. At the
  other uses no value need have that type. The binary join gave such
  names bottom; the n-way one leaves them, reachable only through
  cases that are dead at those uses. So a valuation may leave a name
  without a value; a type that reaches it by an alias then has no
  value. The typing environment's Spec now has this
  (`typing_env_satisfied_strictly`, T2); T4 states the meet the same
  way.
- **Poison (D26).** The contract needs strict satisfaction of the
  use: a name that holds poison must have a type poison has. With the
  exemption of names that hold poison the statement is false, for the
  join and for anything that expands an alias (example in the comment
  at `join_admits_use`). So nothing is promised of a use made by
  variant unboxing with poison arguments. Relations say nothing of a
  poison scrutinee (T1's `relation_holds`); aliases and definitions
  are exact.
- **Not promised:** leastness; equality with the binary join; that
  the join answers (no fatal error, enough fuel); anything about code
  age, allocation modes, symbol projections.
- **Precision promised:** one case, `join_keeps_constants` (a source
  variable with an equation to the same constant in every live use's
  level is that constant in the target). Stated, not yet proved (it
  needs the functions). Aliases between source variables are a
  candidate second case, under `binding_times_coherent`; not promised.
- **Physical equality (D30).** Not in the model. Three places in my
  files change the result with sharing. The human has chosen
  `structural`: the model tests an equality of types there (T1's
  `type_eqb`, a parameter until it exists), as the compiler does under
  `-flambda2-join-sharing structural` (X3). The upper bound holds of
  either branch at each place. What the test gives in precision (an
  extension, or a field, equal in every input is kept as it is) will
  be stated separately, with the functions.

## 4. The hypotheses of the header of `join_env.ml`

- **"Any name defined in the source environment is also defined in
  all the joined environments."** Checked by the compiler: no.
  `check_join_inputs` says it is false (in-types variables made for
  lifted constants), and the header's next paragraph says that symbols
  of other branches are missing. In the contract: not required;
  replaced by the premise, for each valuation, that it satisfies the
  source as well as the use (that a use entails the source is false
  even of the environments the meet makes: R1's example, T7-4), and,
  only for the caller to conclude of the machine, by
  `terms_in_scope_at_uses`. Discrepancy T5-1.
- **"Any symbol defined in one of the joined environments is also
  defined in the source environment."** Checked: only of the set of
  symbols that Simplify passes, not of the environments, and not for
  the meet's calls. In the contract: `symbols_of_uses_in_source`, for
  the well-formedness of the target only. Discrepancy T5-2.
- **"The relative order of variables defined in the source
  environment is preserved across all the joined environments."**
  Checked: no. In the contract: `binding_times_coherent`, defined and
  not required for the guarantee (the compiler checks its candidate
  again with `equal_in_all_joined_envs`); a premise of precision
  only. Discrepancy T5-3.

Also required and not in the header: every environment well formed;
`cut` defined; the names to avoid include every known variable.

## 5. The known failure, and what else was found

- **Closures (T1-4, R3-7).** `n_way_join_closures_entry` keeps a
  function type that only some entries have (the cases
  `None, Some val2` and `Some _, None` of its merge).
  `n_way_join_function_types` in `FlambdaJoinTypes.v` is that part,
  transcribed. `n_way_join_closures_entry_not_upper_bound_statement`
  (proved) gives two closure types that differ only in function types
  and a value that has the first and not the type with the joined
  function types. The contract is not weakened. The change that
  repairs it: in that merge, answer `None` unless both sides have a
  function type (as `n_way_join_generic_product` and the binary
  `join_closures_entry` do).
  `n_way_join_function_types_proposed_sound_statement` (proved) says
  the changed function is an upper bound for closures entries. X2 has
  since shown the failure end to end (a correct program aborts with
  `-O3` and the n-way join) and is making the same change on its
  branch.
- **R1-16** (an empty set given to
  `create_naked_immediates_non_empty` when every head reduces to
  bottom): not looked at further; still traced, not shown reachable.
- **Lifted constants (T5-4).** The source holds the types of constants
  lifted in other branches. On a path that did not define such a
  symbol, the symbol is bound to nothing and its type is false, so no
  valuation satisfies the source there. Not a join problem: facts
  about a symbol may have to be asked only where the symbol is bound.
- **Kinds (T5-9).** See the third exclusion above.
- **Imported variables defined twice (T4-1)**, in the meet's callers
  of the join; T4 has it.
- **Order of names (T5-6):** the representative of an existential's
  aliases, the order of definition of imported and existential
  variables, the order of the rounds.

## 6. Dividing the work

Two halves, with `FlambdaJoinSpec.v` between them.

**E, the environment side (I keep it).** `types/env/join_env.ml`
(2031 lines) and the n-way entry of `types/join_levels.ml`.
- `FlambdaJoinEnv.v`: `Source_env`
  (`candidate_canonical_in_source_env`), `Bindings_in_target_env`,
  `Joined_envs`, the state `Join_env.t`,
  `n_way_join_canonical_simples`, the imports
  (`import_var_transitive` and the three with it),
  `join_aliases_into_bindings` (the leapfrog iterators become the
  intersection of the levels' domains, which is what they compute),
  `recover_inverse_relations`, the rounds,
  `define_or_eliminate_variables_and_add_equations`,
  `cut_and_n_way_join`, `Analysis.create`, and the three functions the
  type join calls (`n_way_join_simples`, `import_type`,
  `n_way_join_env_extension`).
- `FlambdaTypeProject.v`: `Type_grammar.project_variables_out`
  (substituting types for existentials), unless T1 wants it.
- `FlambdaJoinEnvSpec.v`, `FlambdaJoinEnvProofs.v`: the invariant and
  the meaning of the state, the statements of the three functions, and
  `sound_join_of_environments` for the transcription, with the meet
  and the type join as hypotheses.

**T, the type traversal (a second agent).** The 30 join functions of
`types/meet_and_n_way_join.ml` and their helpers
(`generic_merge_map_known`, `n_way_join_unknown`, `deduce_is_int`,
`deduce_get_tag`, `n_way_join_relation_simples`).
- `FlambdaJoinTypes.v` (handed over; it has the function-types part
  today), `FlambdaJoinTypesSpec.v`, `FlambdaJoinTypesProofs.v`:
  `n_way_join_type_sound`, by T1's `types_induction`, from the
  statements of the three environment functions.

**The interface.** Neither file imports the other. The type join is a
function of the state type and the three environment functions (a
section); the environment join takes `n_way_join_type` and the meet's
`meet_expanded_head` as arguments, as in the compiler. A third small
file ties the knot with fuel, with T4's meet. The statements each side
assumes of the other are in `FlambdaJoinSpec.v`, section "The join of
types, inside a join of environments", and are fixed there:

- the state is abstract, with three readings (`joined_env`,
  `definitions_of_existentials`, `exists_in_target_env`) and an
  invariant `state_valid` that is the environment side's;
- four contracts, each "the invariant is kept, the state grows, the
  answer is in the scope of the target, and the upper bound holds
  under every valuation that `extends_input`":
  `n_way_join_type_sound` (T proves it, E assumes it), and
  `n_way_join_simples_sound`, `import_type_sound`,
  `n_way_join_env_extension_sound` (E proves them, T assumes them);
- every argument at an index mentions only variables that the
  environment of that index knows (`join_args_in_scope`), each index
  is given once (`join_args_distinct`), and the types given are kinded
  in their environment (`type_kinded`, defined with
  `aliases_with_kinds`), so that the simples given to the join of
  simples are of the kind given;
- `valid_states_have_witnesses`, which E proves of its invariant: at a
  valid state every valuation of an input extends to one of the
  target. Without it the upper bounds could be vacuous (the reviewer's
  point).

T also needs from T4 `expand_head` and
`reduce_head_of_kind_naked_immediate` with their statements, from T1
`type_eqb`, and from C0 `Keyed.filter_map_fold_on`.

**With T4 (agreed by message).** The meet's parameter is
`join_scoped_envs meet_expanded_head cut_after initial_env
initial_tenv scoped_envs : option Meet_env.t`. Fuel is inside. Rely:
T4's `meet_expanded_head_sound`. Guarantee: T4's (J1) to (J4), which
are items 1, 2, 3 and 5 above with no analysis. Both of us ask, for
each valuation, that it satisfy the initial environment as well as the
scoped one. `Meet_env.t` carries the names to avoid. T4
defines `Meet_env.t`, `Expanded_type.t` and the functions on them that
I call (`add_variable_definition`, `add_env_extension`,
`make_bottom`).

## 7. What I need, by name

- **T2**: `typing_env_satisfied_strictly`, `env_satisfies_strictly`
  (partial valuations; in progress), `typing_env_well_formed` with
  `cut_defined` and `cut_equations_found`,
  `typing_env_satisfied_coincide`,
  `add_variable_definition_satisfied` (a variable defined in types
  may be given any value of its kind, or none),
  `increment_scope_satisfied`, renaming of an environment. Already
  there and used: `cut`, `mem`, `find`, `binding_time_and_mode`,
  `get_canonical_simple_ignoring_name_mode`,
  `get_canonical_simple_exn`, `add_variable_definition`.
- **T3**: there now: `simple_equal_eq`,
  `canonical_element_idempotent`, `canonical_element_mentioned`,
  `respected_aliased`, `respected_canonical_at_mode`. Later: renaming
  of the aliases.
- **T1**: `type_well_formed`, `rename_type`, a boolean equality of
  types if X3's `structural` is chosen, and a word on who writes
  `project_variables_out`.
- **T4**: the definitions file of `Meet_env` and `Expanded_type`;
  `expand_head`, `reduce_head_of_kind_naked_immediate`;
  `add_equation_sound`.
- **N1**: `fresh_name` and its statement; the form of equivariance
  (agreed: up to an explicit permutation of the names made).
- **X3**: the list of uses of `==` and the behaviour under the flag.

## 8. Questions for the human

1. **Closures.** (a) The model's `n_way_join_closures_entry` follows
   the proposed change, the compiler is changed to match (one merge),
   and the soundness theorem has no exception; (b) the model follows
   the compiler and the theorem excludes closure types that differ in
   function types. Recommendation: (a). Meanwhile both versions of
   that part are in `FlambdaJoinTypes.v`; the entry will be
   transcribed with the proposed one, and the compiler's kept beside
   it for the differential tests.
2. **Poison at joins.** Nothing is promised of a use satisfied only
   with the D26 exemption. Either that is accepted (the proof of
   unboxing must then treat a join after an unboxed continuation
   itself), or the environment records which names may hold poison so
   that the join can leave their types alone. Recommendation: accept,
   and revisit with the unboxing workstream.
3. **Lifted constants in the source (T5-4).** For T2 and the
   continuations workstream; the join only needs the premise.
4. **Kinds (T5-9).** The contract has the premise that the use
   environments are kinded. Either the compiler's environments always
   are (then whoever states the kinds of environments proves it, and
   the join's unchecked path is unreachable), or the join should test
   the kinds of the simples when it makes a variable for them (one
   test in `existential_for_these_canonicals`). Recommendation: find
   out which with a reproducer (X2 or X5), and keep the premise
   meanwhile.
