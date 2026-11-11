# T4: the contract of the meet of types

First request of the meet stream: what a meet guarantees, as definitions
and statements, before any function is transcribed. It is for review by
R1, and for T5 (the join), T2 (the environment) and T1 (the types) to
check what is asked of them.

Files, in `middle_end/flambda2/types/rocq/`:

- `FlambdaMeetSpec.v`: the contract. To be reviewed.
- `FlambdaMeetProofs.v`: the five closed statements, proved.
- `FlambdaExpandHead.v`, `FlambdaMeetEnv.v`: the types that the join is
  written against (`Expanded_type.t`, `Meet_env.t`, `Meet_result.t`,
  `meet_expanded_head`). Definitions only; to be reviewed against
  `types/expand_head.ml` and `types/env/meet_env.ml`.

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
the compiler, or a meet that ran out of fuel. The statement that the
transcribed meet has its contract will have the form
`transcription_sound`: for every join that has `join_scoped_envs_sound`
and every fuel, `meet_contract`.

`meet_sound`: if

- the inputs are well formed (`meet_inputs_well_formed tenv t1 t2`),
- a valuation satisfies the environment
  (`typing_env_satisfied_strictly statics valuation tenv`),
- a value `v` has both types under it,
- and `meet tenv t1 t2 = Some result`,

then `result` is `Ok (t, tenv')`, and there is a valuation that has the
same value, or none, as the first for every variable that `tenv` knows
(`extended_from`), satisfies `tenv'`, and gives `v` the type `t`.

So: the values of both inputs are kept; one valuation accounts for all
the equations and definitions returned; bottom is answered only when no
value has both types (`meet_bottom_sound`, which follows:
`meet_answers_bottom_statement`, proved).

With it: `meet_keeps_well_formed` (the answer may be met again),
`meet_kinds`, `meet_bottom_env`, and for `Typing_env.add_equation`,
`add_equation_sound`.

Not claimed: that the type answered has no more values than each input
(section 9).

## 3. What satisfies an environment, and poison (D26)

The contracts use `typing_env_satisfied_strictly`: the environment is
not bottom; every name that has a value in the valuation has the type
the environment gives it, poison or not; aliases have the same value. A
name may have no value. This is not T2's `typing_env_satisfied` as it is
on this branch, which exempts a name whose value is poison and gives
every name a value. T2 is adding the strict notion, with partial
valuations, to `FlambdaTypingEnvSpec.v` under this name and with these
arguments; my definition is a stand-in and goes when T2's is on my
branch.

Why, both found while writing this and agreed with T2 and T5:

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

The premise that the orchestrator asked for is therefore the strictness
of the environment. It is the compiler's unchecked assumption, and there
are two `CR mshinwell`, at `typing_env_satisfied_strictly` and at
`add_equation_sound`. In the words of D26: `satisfied_no_poison`
(proved) says that an environment satisfied in T2's sense by a valuation
that gives poison to none of its names is satisfied strictly, and
`add_equation_no_poison` (proved from the contract) is `add_equation`
with that premise.

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
  (`type_well_formed`) and the environment knows its variables.
- An environment fits (`typing_env_fits`) if it is well formed
  (`typing_env_well_formed`) and each of its types fits it.

`type_well_formed : flambda_type -> bool` is T1's next request
(`FlambdaTypeWellFormedSpec.v`, with one predicate for each head and for
an extension); `typing_env_well_formed : Typing_env.t -> bool` is in
T2's second request (or a `Prop`, `typing_env_invariant`, if a part
cannot be boolean). Until they exist they are parameters of the
contracts (a `Section`). What meet needs of `type_well_formed`, agreed
with T1:

- (a) the product of a case of blocks is no wider than the size of its
  index (`meet_mapping` makes a product with an empty component empty);
- (b) the function types, closure types and value slot types of a case
  of closures are of slots among those of its index, and an exact index
  has the slot of the case among its closures;
- (c) shapes are written in one way (`meet_row_like_for_blocks` compares
  them with `equal`);
- (d) kinds: the immediates of a variant, the contents of a boxed
  number, the closure types, the fields of a block against its shape;
- (e) a set of numbers that is a head is not empty (`set_meet` answers
  an input unchanged when one set is included in the other);
- (f) no type is an alias to a poison constant (`Relation.of_const`
  reads `Is_int` of one as 1; the relation says nothing of poison).

(e) and (f) are new to T1's list; T1 has taken (e).

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
`meet_expanded_head` given has `meet_expanded_head_sound`:

- J1: a valuation that satisfies one of the scoped environments extends
  to one that satisfies the result and agrees with it on every variable
  that this scoped environment knows;
- J2: the result is `initial_env` extended (`meet_env_extends`): same
  scope, earlier levels and `adding_equations_for_names`; every name it
  knew still has a type of the same kind, binding time and name mode;
- J3: a variable of the result that no environment given knows is not
  in `Meet_env.names_to_avoid initial_env`, and is in that of the
  result;
- J4: the result fits.

T5 has said it can give J2 to J4 as written, and J1 once the strict
notion with partial valuations is T2's (it could not with a strict
notion and total valuations; that is what changed section 3). T5 asked
for the premise that what satisfies a scoped environment satisfies
`initial_tenv`; it is in `scoped_env_of`, for me to establish.

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
  that the step adds.
- The input on which any meet that makes this step fails `meet_sound`:
  the environment `p : Variant (get_tag = tag)`,
  `tag : (numbers unknown, Get_tag p)`, as
  `Typing_env.add_get_tag_relation` builds it; the valuation `p` = the
  tagged immediate 7, `tag` = 0, which satisfies it strictly; the meet
  of `= tag` with the type of the naked immediate 0. The value 0 has
  both types. The environment answered has
  `p : blocks_with_these_tags [0]`, which no valuation that keeps `p`
  satisfies. The lemma about the transcribed function comes with the
  function.
- The change that makes it hold: build the type with
  `~immediates:Unknown` instead of the bottom type of naked immediates
  (`immediate_or_blocks_with_these_tags`). Proved:
  `get_tag_reduction_repaired`. Nothing is lost where the name is
  already known to be a block.
- Plan: the transcription takes the type added in this case as a
  parameter. With the compiler's type it is the function T7 compares;
  with the repaired type it is the function that is proved.

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

## 11. The transcription, in outline

Under the compiler's names, in `FlambdaMeetEnv.v` (the functions of
`meet_env.ml`, with `meet_expanded_head` as an argument as there),
`FlambdaExpandHead.v` (`expand_head0`, `expand_head`) and a new
`FlambdaMeet.v` (the helpers and the 33 functions, in a `Section` with
the join and the type of the `Get_tag` step as variables). The header
will say function by function what the model has. Differences known
now: `Dfs` only; no coercions; no arrays (`meet_array_type`,
`meet_array_contents`, `meet_array_element_kinds` left out, as `Array`
is in the grammar); the eleven `meet_head_of_kind_naked_*` are one; no
`rec_info`; no code age; exceptions (`Bottom_equation`,
`Bottom_result`) become results; the references of `meet_row_like`
become a state threaded through a fold. For that fold C0 is adding
`Keyed.fold2_on`, `fold2` and `merge_fold` to the map module, with the
order of the keys an argument: tags in numeric order, as the compiler;
slots in the order of the lists, which is not the compiler's (it goes
by stamps), a difference to record.

## 12. Discrepancies recorded

In `discrepancies/T4.md` of the team directory:

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

## 13. Questions

For the human or the orchestrator:

1. **The `Get_tag` step.** (a) Prove the meet with the repaired type and
   keep the compiler's as a second instance for the tests (what I plan);
   (b) prove with a premise that excludes scrutinees that may be
   immediates; (c) change the compiler first. Recommendation: (a), and
   the one-line change to the compiler (`~immediates:Unknown`) offered
   to the developers.
2. **Poison.** The contracts say nothing where a name holds poison and
   its type is not true of poison. (a) Leave it: the proof of unboxing
   (S6) handles those paths itself. (b) The machine's valuation gives
   no value to such parameters and to what depends on them, the
   contracts apply, and a rewrite that uses a fact about a variable
   needs "it has a value" (T2's analysis, section 3). Recommendation:
   (b) when S6 is designed; nothing in this request waits for it.
3. **T4-3.** The meet is right only if a function type is under an
   index that has its slot; the n-way join answers types where it is
   not. Either the join is changed to drop such function types (the
   binary join's rule), or the meet's bottom for two code ids is wrong
   for some closures. Recommendation: treat it with T1-4 as one
   candidate for the developers; meanwhile the contract keeps (b) as a
   premise, and the theorem about a meet after an n-way join will have
   it as a stated gap.

4. **T4-1.** (a) Transcribe the second definition as it is, for the
   comparison with the compiler, and prove the contract for a meet that
   defines only the variables that the result of the join does not
   know (one test of `Typing_env.mem` in `add_defined_vars`); (b) the
   same test proposed to the developers. Recommendation: both; it is
   the same treatment as the `Get_tag` step, and X2 or T7 should first
   see whether "Cannot rebind" can be provoked.

For reviewers: whether `meet_env_extends` and the frame parts of
`meet_expanded_head_sound` belong in a reviewed contract or with the
transcription; whether a precision statement is wanted.
