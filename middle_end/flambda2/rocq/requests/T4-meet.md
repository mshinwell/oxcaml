# T4: the meet of types: its contract and its functions

Second request of the meet stream. The first was the contract alone,
before any function; R1 reviewed it. This one has the contract as
revised after that review, the functions transcribed, statements about
them that are proved by running them, and what expanding the head of a
type keeps. It is for review by R1, and for T5 and T5b (the join), T2
(the environment) and T1 (the types) to check what is asked of them.
Section 14 says what changed since the first request.

Files, in `middle_end/flambda2/types/rocq/`:

- `FlambdaMeetSpec.v`: the contract. To be reviewed.
- `FlambdaMeetProofs.v`: its five closed statements, proved.
- `FlambdaMeetEnv.v`: the functions of `types/env/meet_env.ml`.
  `FlambdaExpandHead.v`: `Expanded_type` and `expand_head` of
  `types/expand_head.ml`. `FlambdaMeet.v`: the meet of
  `types/meet_and_n_way_join.ml`, `types/meet.ml`, and what
  `types/flambda2_types.ml` adds to `Typing_env`. Definitions only; to
  be reviewed against those files.
- `FlambdaMeetGrammar.v`: definitions that belong in the files of T1,
  T2 and C0 and wait for them there.
- `FlambdaMeetExamplesSpec.v`, `FlambdaMeetExamplesProofs.v`: eight
  statements about the transcribed functions, proved by running them.
- `FlambdaExpandHeadSpec.v`, `FlambdaExpandHeadProofs.v`: what
  `expand_head` keeps, six statements, proved.

The compiler read: `types/meet_and_n_way_join.ml` (lines 1 to 1883, the
meet), `types/meet.ml`, `types/env/meet_env.ml`, `types/expand_head.ml`,
`types/flambda2_types.ml` (what calls meet), and of
`types/env/join_env.ml` what the meet's two calls reach
(`cut_and_n_way_join`, `import_var_transitive`,
`define_or_eliminate_variables_and_add_equations`).

## 1. The decision it is written under

One specification of meet; the traversal transcribed once, with the join
of scoped environments as a parameter; the n-way join first (D27). In
the compiler the meet proper calls the join at two places only,
`meet_disjunction` and `meet_row_like`, each time as
`Join_env.cut_and_n_way_join`. That call is the parameter.

## 2. The contract

A contract is a proposition about a function of the type that the
compiler's function has (`meet_function`, `add_equation_function`,
`meet_expanded_head`, `join_scoped_envs`). `None` is a fatal error of
the compiler, or a meet that ran out of fuel. What is to be proved of
the transcribed meet is `transcription_sound meet_to_prove`: for every
join that has `join_scoped_envs_sound` and every fuel, `meet_contract`.
It is not proved yet, and is not among the statements of the file.

`meet_sound`: if

- the inputs are well formed (`meet_inputs_well_formed tenv t1 t2`),
- a valuation satisfies the environment
  (`typing_env_satisfied_strictly statics valuation tenv`),
- a value `v` has both types under it,
- and `meet tenv t1 t2 = Some result`,

then `result` is `Ok (t, tenv')`, and there is a valuation that has the
same value, or none, as the first for every variable that `tenv` knows
(`extended_from`), satisfies `tenv'`, and gives `v` the type `t`. The
agreement is exact, so that what the first valuation satisfied over
the variables that `tenv` knows, the second satisfies (T2's
`satisfied_but_coincide`). For a while it was weaker (a variable
without a value could be given one), to match the n-way join; R1
showed that the meet of an alternative of a disjunction could then not
give the join a valuation that still satisfies the environment of the
whole meet, and T5 found that the join can keep exact agreement if no
name has an obviously bottom type (section 4).

So: the values of both inputs are kept; one valuation accounts for all
the equations and definitions returned; bottom is answered only when no
value has both types (`meet_bottom_sound`, which follows:
`meet_answers_bottom_statement`, proved).

With it: `meet_keeps_well_formed` (the answer may be met again),
`meet_kinds`, `meet_bottom_env`; for `Typing_env.add_equation`,
`add_equation_sound`; and for `Typing_env.add_env_extension` and
`add_equations_on_params`, `add_env_extension_sound` and
`add_equations_on_params_sound`, each with the premise that every name
concerned has a value of the type given for it.

Not claimed: that the type answered has no more values than each input
(section 9).

## 3. What satisfies an environment, and poison (D26)

The contracts use T2's `typing_env_satisfied_strictly`
(`FlambdaTypingEnvSpec.v`): the environment is not bottom; every name
that has a value in the valuation has the type the environment gives
it, poison or not; aliases have the same value. A name may have no
value. They do not use `typing_env_satisfied`, which exempts the names
that poison touches.

Why, agreed with T2 and T5:

- **The exemption for poison is not enough, and a premise on one name is
  not either.** A meet reads the types of names (the target of an
  alias, the scrutinee of a relation, the names of an extension). If
  such a name holds poison and its type is not true of poison, the meet
  deduces from a false type. `x` holds poison, the environment has
  `x : null`: the value poison has the types `= x` and
  `any_non_null_value`, and their meet is bottom. With `x` and `y`
  holding poison, `x : Variant (is_int = z)`,
  `y : Variant (is_int = z')`, `z` holding 1 and `z'` holding 0, the
  meet of `= x` with `= y`, both of which poison has, makes `z` and
  `z'` aliases. The name can be reached through a field,
  so "the value of the name is not poison" for the name of
  `add_equation` does not cover it.
- **Strictness of every name does not survive the n-way join unless a
  name may have no value.** T5's example: the join defines in its result
  a variable `a` taken from one input, with the type it has there; under
  a valuation of another input no value need have that type. With
  partial valuations `a` has no value there. A type that mentions `a` in
  a live place has no value either, so the meet never reads the type of
  a name with no value for a value it has in hand.

- **A relation on a scrutinee that holds poison** (found by R1; D26 as
  revised). `p : unknown` holding poison and `t : Get_tag of p` holding
  0 was a strictly satisfied environment while T1's `relation_holds`
  related poison to every number; the meet of `= t` with the number 0
  gives `p` a type of blocks, which poison has not (for `Is_int`,
  `any_block`; and `Relation.of_const` reads `Is_int` of a poison
  constant as 1). Ruled: `Is_int` and `Get_tag` are not true of a
  scrutinee that holds poison, as in the core, where the primitives
  have no value on poison; T1 changes `relation_holds`; T2's
  `typing_env_satisfied` exempts a name whose type is a relation on a
  name that holds poison (done). The contract has no premise for it.
  Until T1's change is on this branch, `meet_sound` is false of the
  transcribed meet here, and the header says so. `Is_null` keeps its
  clause (it relates poison to 0): the n-way join needs it, and what
  meet deduces from 0, `any_non_null_value`, poison has. T4-5.
- **A name with no value whose type is a relation on a name that holds
  poison** (R3) is strictly satisfied and harmless to meet: a meet
  makes a deduction only on behalf of a value in hand, and what tells
  it that a name has a value is the type that this value has (an
  alias, a relation, an equation of an extension). The functions that
  have no value in hand take the premise that the name has one.

The premise is therefore the strictness of the environment. It is the
compiler's unchecked assumption, and there is a `CR mshinwell` at
`add_equation_sound`. `add_equation_no_poison` (proved from the
contract) is `add_equation` for `typing_env_satisfied` where no name
holds poison. `meet_through_poison` (proved by running the meet) is
the first example above.

What the contracts do not cover: a handler in which unboxing has given
types to parameters that hold poison on the path taken. There the
environment is not satisfied strictly. I suggested to T2 that the
machine's valuation may leave such parameters without a value, which
would put those environments back under the contracts. T2 finds that
D26 implies it, and that what must be left without a value is more than
the poison (the `Is_int` and tag parameters that hold 0, and any value
built from the poison), so that a rewrite then needs "this variable has
a value" as a premise about the path. T2 keeps both notions for now and
has passed the alternative to the orchestrator (question 2 below).

## 4. Well-formedness of the inputs

`meet_inputs_well_formed tenv t1 t2`: the environment fits, each type
fits it, and the two types have one kind.

- A type fits an environment (`type_fits`) if it is well formed
  (`type_well_formed`), the environment knows its variables, and it is
  kinded there (`type_kinded`): each alias is at the kind that the
  environment has for its target, and the variables for `Is_int`,
  `Get_tag` and `Is_null` are naked immediates. Meet does not need the
  kinds (it stops with a fatal error where they are wrong); the n-way
  join does, of the environments it is given, so meet takes them and
  gives them back. It is a premise about kinds, with a `CR mshinwell`
  (D10, D12, D32; T5-9). The traversal `aliases_with_kinds` is T5's.
- An environment fits (`typing_env_fits`) if it is well formed
  (`typing_env_well_formed`), no name has an obviously bottom type in
  it unless it is bottom (`no_bottom_types`), and each of its types
  fits it. `no_bottom_types` is there for the n-way join, which passes
  over an obviously bottom type and can then make the name an alias of
  what it is in the other environments joined, giving a value to a
  name that had none. The model is stricter than the compiler here
  (the binary join makes such environments with
  `Meet_env.add_env_extension_maybe_bottom`); meet keeps the
  condition; there is a `CR mshinwell` (T5-10).

`type_well_formed : flambda_type -> bool` is T1's
(`FlambdaTypeWellFormedSpec.v`, not on the branch this one is made
from); `typing_env_well_formed : Typing_env.t -> bool` is T2's
(`FlambdaTypingEnvInvariantSpec.v`, with `typing_env_invariant`, now on
this branch). Both are still parameters of the contracts (a `Section`):
T2's is to replace its parameter once it is checked that the invariant
holds at the environments in the middle of a meet. What meet needs of
`type_well_formed`, agreed with T1:

- (a) the product of a case of blocks is no wider than the size of its
  index (`meet_mapping` makes a product with an empty component empty);
- (b) the function types, closure types and value slot types of a case
  of closures are of slots among those of its index, and an exact index
  has the slot of the case among its closures;
- (c) shapes are written in one way (`meet_row_like_for_blocks` compares
  them with `equal`);
- (d) kinds: the immediates of a variant, the contents of a boxed
  number, the closure types;
- (e) a set of numbers that is a head is not empty (`set_meet` answers
  an input unchanged when one set is included in the other). Here the
  model is stricter than the compiler (D32); T1 has it as a condition.

That a type is not an alias to a poison constant was asked in the
first request and is not any more (R1): the compiler makes such types
(`Typing_env.type_simple_in_term_exn`), and the revised meaning of
relations makes them harmless.

The n-way join does not keep (b) (T1-4). So the types that it answers
are not all inputs that this contract covers: see T4-3.

## 5. The join that meet is given

Type: `join_scoped_envs`, that is
`meet_expanded_head -> Scope.t -> Meet_env.t -> Typing_env.t ->
list Typing_env.t -> option Meet_env.t`: the compiler's
`cut_and_n_way_join ~meet_expanded_head ~cut_after initial_env
initial_tenv scoped_envs`, with `n_way_join_type` inside it. Agreed with
T5, whose own functions take a fuel that does not show here.

Contract (`join_scoped_envs_sound`), for a call as meet makes it
(`initial_tenv` is the typing environment of `initial_env`, `cut_after`
its scope, every scoped environment made from it by adding definitions
and equations: `scoped_env_of`), supposing that the
`meet_expanded_head` given has its contract, which is in two parts:
`meet_expanded_head_sound` (what it says of values) and
`meet_expanded_head_keeps` (the environment answered is the first
extended, it fits, and the type answered fits it and is of the kind of
the inputs; no value and no valuation is supposed):

- J1: a valuation that satisfies `initial_tenv` and one of the scoped
  environments extends to one that satisfies the result and agrees
  with it on every variable that this scoped environment knows;
- J2: the result is `initial_env` extended (`meet_env_extends`): same
  scope, earlier levels and `adding_equations_for_names`; every name it
  knew still has a type of the same kind, binding time and name mode;
- J3: a variable of the result that no environment given knows is not
  in `Meet_env.names_to_avoid initial_env`, and is in that of the
  result;
- J4: the result fits.

J1 is about one valuation and both environments. The first request
had instead, in `scoped_env_of`, that whatever satisfies a scoped
environment satisfies `initial_tenv`. R1 showed that meet cannot give
that: adding an equation can forget. With
`x : Value (unknown, may be null, is_null = z)`, adding
`x : any_non_null_value` answers `x : any_non_null_value` and says
nothing of `z` any more (`meet_disjunction`, where one alternative is
bottom); R1 ran it on both of the compiler's meets, and
`add_equation_forgets` proves it of the transcribed function.
`scoped_env_of` now says that the scoped environment fits and has
every name of `initial_tenv` with its binding time and a type of the
same kind. T5 has made the matching change (its premise on the source
is per valuation), and asks the scoped environments to be kinded,
which `scoped_env_of` gives. The join needs the environment of the
meet to be satisfied by that valuation: for a name that every
environment joined has an equation on, it answers the meet of the
joined type with the type that `initial_tenv` records. The meet
supplies it by exact agreement: the valuation that an alternative
answers agrees with the one before on what `initial_tenv` knows.
`forgetful_join_sound` (proved) shows that the contract can be had:
the join that answers `initial_env` has it.

Found by T5 (T5-10), and decided: the compiler's n-way join has J1
only under a condition on what it is given. Where the type joined for
a name `x` is a variant with a variable `r` for `Is_int`, it gives `r`
the type "`Is_int` of `x`" (`recover_inverse_relations`), also where
`x` has no value in the run (it was imported by an earlier join from
other uses) and `r` has one. Weakening the conclusion of J1 (the names
whose type is a relation on a name with no value exempt) does not work
for the meet that follows: it reads the relation on behalf of the
value of `r` and adds an equation to `x`, whose stored type nothing
constrains when it has no value, and the meet of the two can be
bottom. A premise that the valuation gives every known variable a
value cannot be supplied after a join that imports from a subset. So
J1 stays strict, as the hypothesis under which the meet is to be
proved; T5 states the condition under which the compiler's join has
it (the scrutinee of every relation recovered has a value in every
run in which the result has one), and the instance of the meet for
the compiler's own join carries that condition.

Physical equality in the join: X3's audit finds four uses that change a
result, all in the join. The behaviour to assume of the parameter is
that of the compiler flag X3 is adding (`-flambda2-join-sharing
structural`); it does not change the contract above.

## 6. Names

Meet creates no name: there is no `Variable.create` in the 33 functions
or in `meet_env.ml`. The join does, and meet defines again, in outer
environments, variables that the join or a branch defined. The contract
speaks of names by membership only ("a variable that the environment
knows", `Typing_env.mem None`), never by number or order. On N1's
advice the model's `Meet_env.t` carries `names_to_avoid`, which the
compiler has not: the join makes variables outside it and adds them,
and meet hands it from one branch to the next so that two branches do
not make the same variable (the compiler's variables are globally
fresh). N1 asks that equivariance be stated up to a permutation of the
names created; that statement needs the renamings of types (T1),
environments (T2) and aliases (T3), and is not in this request.

## 7. Kinds, code ids, modes, physical equality

- Kinds: `meet_kinds`: in an environment that is not bottom, a meet of
  types of two kinds is `None` (the compiler's fatal error), never
  bottom or a type. `meet_bottom_env`: in a bottom environment the
  answer is bottom before the kinds are looked at (`Meet.meet` tests
  `is_bottom` first).
- Code ids: the model has no code age relation. Its `meet_code_id` will
  answer bottom for two different code ids; the compiler answers the
  newer when one is a later version of the other, and either input when
  it cannot tell. The contract claims nothing about inputs whose code
  ids the relation relates (T4-4), and nothing about which code a
  closure runs.
- Allocation modes and `is_unique`: transcribed, no claim.
- Physical equality (D30 as revised): in the meet it is only a
  shortcut (`meet_inverse_relations`; `reduce_head_of_kind_naked_
  immediate` compares names, which are integers; and the `Left_input` /
  `Right_input` / `Both_inputs` answers that keep sharing). X3's audit
  agrees: no use in the meet changes a result. The transcription
  follows the slow path; the contract is about the type answered
  (`extract_value`).

## 8. The step that is not sound

`reduce_inverse_relations`, case `Get_tag` (in both files): when the
numbers of a naked immediate that is `Get_tag` of a name become known,
it adds to the name the equation `blocks_with_these_tags tags`, which
has no immediate. T1's relation holds of an immediate with any number,
because unboxing records it of parameters that may be immediates and
passes 0.

- The contract is stated as it should be; T1's meaning is not changed.
- Proved: `get_tag_reduction_unsound`: a value that is not poison, a
  number that `Get_tag` relates to it, and the value has not the type
  that the step adds. On the transcribed functions:
  `compiler_meet_get_tag` (the meet answers an environment that no
  valuation that keeps the scrutinee satisfies) and
  `compiler_meet_not_sound` (so the compiler's meet has not
  `meet_sound`, whatever the join and whatever well-formedness asks,
  if the input below is well formed).
- The input on which any meet that makes this step fails `meet_sound`:
  the environment `p : Variant (get_tag = tag)`,
  `tag : (numbers unknown, Get_tag p)`, as
  `Typing_env.add_get_tag_relation` builds it; the valuation `p` = the
  tagged immediate 7, `tag` = 0, which satisfies it strictly; the meet
  of `= tag` with the type of the naked immediate 0. The value 0 has
  both types. The environment answered has
  `p : blocks_with_these_tags [0]`, which no valuation that keeps `p`
  satisfies. `example_get_tag_env_made` proves that
  `add_get_tag_relation` makes that environment.
- The change that makes it hold: build the type with
  `~immediates:Unknown` instead of the bottom type of naked immediates
  (`immediate_or_blocks_with_these_tags`). Proved:
  `get_tag_reduction_repaired`, for the tags that the step computes,
  and `meet_to_prove_get_tag` (on the same input the repaired meet
  answers an environment that the run satisfies). Nothing is lost
  where the name is already known to be a block.
- The transcription takes the type added in this case as a parameter.
  With the compiler's type it is the function T7 compares
  (`compiler_meet`); with the repaired type it is the function that is
  to be proved (`meet_to_prove`).
- Tags out of range (found by R1; T4-6). The step keeps of the numbers
  those that are tags of blocks (0 to 255) and drops the others. A
  block of the model may have any integer for its tag (that tags are
  in range is a rule of well-formed terms, D23), so a block of tag 999
  with the numbers {0, 999} would get "block with tag 0". Agreed with
  T1: `relation_holds Get_tag` relates a block to its tag only if the
  tag is in range, so the rule is used once, where a relation is made
  from a primitive, and the contract of meet has no premise for it.
  Until T1's change is on this branch `get_tag_reduction_repaired`
  has the range, and that the value is not poison, as premises.

No miscompiled program is known (T1-1 says why T1 thinks none arises).

## 9. Precision

No claim that the meet is below its inputs. It is not, in the compiler:
an equation on a name is dropped while one is being added on that name;
a case that is impossible falls back to the case of the other tags
(`meet_knowns`, with a comment by bclement); a `Mutable_block` met with
a `Variant` loses the fields; extensions are joined. A statement of
precision for named cases can follow the functions if the reviewer
wants one.

## 10. Termination

The meet is not a recursion on its two types: a meet with an alias
meets the type that the environment has for the name. The compiler
stops because an equation on a name is ignored while one is being
added on it, and between two additions the types get smaller. Nothing
in the compiler states this.

Choice: fuel. The 33 functions are one `Fixpoint` on a `nat`; out of
fuel is `None`; the meet gives itself at the smaller fuel to the join.
The contracts are about answers that are not `None`, so soundness needs
no bound. "Some fuel is enough for every well formed input" is a
separate statement; I will attempt it after the soundness proofs, with
the measure above (names not in `adding_equations_for_names`, then the
size of the types), and say so if it does not go through. A measure in
place of fuel would need that argument before a single function could
be defined; `types_induction` does not apply, the recursion not being
on a type.

## 11. The transcription

Under the compiler's names. Each file's header says function by
function what the model has and every difference.

- `FlambdaMeetEnv.v`: the functions of `meet_env.ml` for its default
  strategy (`Dfs`: no delayed equation), with `meet_expanded_head` as
  an argument as there. The exception `Bottom_equation` is an
  `Or_bottom.t`; a fatal error is `None`.
- `FlambdaExpandHead.v`: `Expanded_type`, `expand_head_of_alias_type`,
  `expand_head0`, `expand_head`.
- `FlambdaMeet.v`: the helpers and the functions of the meet. Every
  cycle among them goes through `meet`, which is given the meet of
  expanded types as a parameter; so each function is a plain
  definition in a section, and one fixpoint on the fuel,
  `Meet.meet_expanded_head`, ties them. The parameters of what is
  exported: the join; a record of the three places where the meet can
  do other than the compiler (`meet_choices`: the type that the
  `Get_tag` step adds; whether a variable that the environment knows
  is defined again after a join, T4-1; whether the variables of a
  single case of a row-like structure are lifted, T4-9), with
  `compiler_choices` and `repaired_choices`; and the fuel.
  `Meet.meet`, `Meet.meet_shape`, and
  `Flambda2_types.add_equation`, `add_equations_on_params`,
  `add_env_extension`, `add_is_null_relation`, `add_is_int_relation`,
  `add_get_tag_relation`.
- Differences: `Dfs` only; no coercions; no arrays; the eleven
  `meet_head_of_kind_naked_*` are one; no `rec_info`; no code age;
  exceptions become results; the references of `meet_row_like` become
  a record that is handed on; names to avoid (section 6). The cases of
  blocks are gone through in the order of their tags, as in the
  compiler; function slots, value slots and the names of an extension
  in the order of the lists, which is not the compiler's (it goes by
  its maps). So the file is the compiler's algorithm on maps in
  another order, and it is not claimed that the two answer the same
  thing: the order can show in which fatal error or bottom comes
  first, in what a later meet reads, in the binding times of variables
  defined after a join, and in the order of the bindings answered; and
  giving the inputs in the compiler's order does not remove that, the
  maps and levels built on the way being lists in the order in which
  they were built. A comparison with the compiler is to be made up to
  the order of bindings and to binding times, until a statement says
  that the answer does not depend on the order.
- `FlambdaMeetGrammar.v` holds what the transcription needs of other
  streams' files, each definition to move to its owner under the same
  name: for T1, `naked_number_kind_eqb`, `block_shape_eqb`,
  `const_of_naked_number`, `must_be_singleton`,
  `head_of_kind_value_null`, `head_of_kind_value_tagged_immediate`,
  the three functions on `set_of_closures_contents`, and T5's
  `aliases_with_kinds`; for T2, `fold_on_defined_vars` and
  `kind_of_simple`; for C0, `fold2_on`, `keys_of_both` and
  `merge_fold_on` (the forms agreed with C0, which take the equality
  first).
- The functions extract. For the differential tests (T7): the
  compiler is `Meet.meet join compiler_choices fuel`, with the join
  read as the compiler under `-flambda2-join-sharing structural`.

## 12. Discrepancies recorded

The entries of this stream:

- T4-1: after the n-way join, `meet_disjunction` and `meet_row_like`
  define again every variable of the branch levels, among them those
  that the join imported under their own names and gave equations to.
  With invariant checks it is the fatal error "Cannot rebind"; without,
  the variable gets the unknown type and a later binding time while the
  level keeps the join's equation and the aliases keep the old order.
  T5 reads `join_env.ml` the same way. Candidate; test described, not
  run. A consequence for the contract: a meet that does this does not
  keep the invariant of an environment, so `meet_keeps_well_formed`
  cannot be proved of the function as the compiler has it (soundness
  can: a variable of unknown type asks nothing). Question 4.
- T4-2: a meet through a name that holds poison (section 3).
- T4-3: a function type of a slot that the index does not have: the
  meet answers bottom for two different code ids at such a slot, and a
  closure whose set has no such slot has both types. Same root as T1-4.
- T4-4: code age (section 7).
- T4-5: a relation on a scrutinee that holds poison (section 3).
- T4-6: tags out of range in the `Get_tag` reduction (section 8).
- T4-7: `expand_head` answers the type of a constant for an alias
  whose canonical element is a constant, whatever the kind of the
  alias (`expand_head_other_kind`). So "the type expanded is of the
  kind of the type" needs a premise, `constants_of_kind`, with a
  `CR mshinwell`; it belongs with T2's invariant.
- T4-8: `is_int_for_scrutinee` says 1 for every constant scrutinee,
  `Null` included; `Relation.of_const` says 0 for `Null`.
- T4-9 (found by R1): where `meet_row_like` keeps one case only
  (`need_join` is false) it makes no extension of the case and does
  not record the variables that the environment of the case defines;
  the join is then given that one environment and keeps of its
  variables those that the equations it joins mention. A variable
  that a meet inside the case defined, and that only the type answered
  mentions, is then unknown to the environment answered, and the type
  answered does not fit it. `meet_disjunction` defines such variables
  again after its join. The transcription has the compiler's
  behaviour and the other as a choice
  (`lift_variables_of_single_case`); the contract is to be proved of
  the meet that lifts.

## 13. The questions of the first request, as answered

1. **The `Get_tag` step.** Prove the meet with the repaired type and
   keep the compiler's as a second instance for the tests. Done as
   far as the functions and the instance; the proof is next.
2. **Poison.** The handlers that unboxing makes stay outside the
   contracts. Since then D26 was revised for relations (section 3).
3. **T4-3.** Goes to the developers with T1-4, which was demonstrated
   as a miscompilation; the human has taken a fix of the n-way join of
   function types (it keeps one only if every input has one). When
   that fix is on the integration branch the n-way join keeps
   condition (b) for function types, and the entry will say so.
4. **T4-1.** Transcribed as the compiler has it, as a choice
   (`define_again` in `meet_choices`); the contract is to be proved of
   the meet that defines only what the result does not know.

## 14. What changed since the first request

From R1's review of the contract:

- `meet_expanded_head_sound` is split: the semantic part, and
  `meet_expanded_head_keeps` with the frame, the fit and the kind of
  the answer, which supposes no value. The join's contract supposes
  both.
- `scoped_env_of` lost "what satisfies the scoped environment
  satisfies `initial_tenv`"; J1 is about a valuation that satisfies
  both (section 5).
- Condition (f) is gone (section 4).
- Poison under a relation, and tags out of range (sections 3 and 8).

From T5: `type_fits` has kindedness; `typing_env_fits` has
`no_bottom_types`. The frame condition is exact agreement, as in the
first request.

From T2: its strict notion replaces my stand-in; `satisfied_no_poison`
is T2's `satisfied_no_poison_strictly`.

New: `add_env_extension_sound`, `add_equations_on_params_sound`,
`fits_kinded`; `compiler_meet` and `meet_to_prove`; the examples; the
statements about `expand_head` (asked for by T5b, for the type
traversal of the join): `expand_head_sound` (values are kept, under
strict satisfaction, with no other premise), `expand_head_closed`,
`expand_head_kinded`, `expand_head_kind`, `expand_head_head_of_kind`.

## 15. Next

- The proofs of the contract for `meet_to_prove`, with the join's
  contract as a hypothesis; then that some fuel is enough.
- `reduce_head_of_kind_naked_immediate` is sound (T5b needs it too):
  when T1's change to relations is on this branch.
- Replace the two parameters by T1's and T2's predicates.

For reviewers: whether a precision statement is wanted.
