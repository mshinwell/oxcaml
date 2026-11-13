# T2: the call of the join in the rewrites from the types. A request

From T2, for the orchestrator (who decides whether it is done, and
has the second question of section 7), V2 (whose validation would
call it), C5 (whose test of the lifted verdict from the imports
computes the same call again, and whose static environment of the
imports a unit starts in), C1 (the range of a run), T5 and N3 (the
join and its renaming), R1 and R3 (who read it).

It is a request and nothing else: no file of the model, of the
validation or of the tool is changed with it. Section 6 says what was
run, with a tool changed by hand and not committed.

## Why

At `-O2` and `-O3` Simplify knows, in the handler of a continuation
that is applied at two places or more, what the applications have in
common: a parameter that is one of two constants, a variant that is a
block of one tag at every application. It folds a test of such a
parameter and removes an arm of a `Switch` on it. The validation
knows nothing of a parameter of a handler that is applied twice, so
the term before keeps the test and the unit is not validated. At the
default flags Simplify does not know it either, and the same unit is
validated.

## 1. What the compiler does

- **The flag.** `simplify/join_points.ml`: a join of the environments
  at the applications of a continuation is made if
  `Flambda_features.join_points ()` holds or the continuation is
  applied at most once (`should_do_join`). The flag is off by default
  and on at `-O2` and `-O3` (`driver/oxcaml_flags.ml`). Without the
  join the parameters of the handler have unknown types of their
  subkinds (`add_parameters_with_unknown_types`).
- **The join.** With it, the handler is simplified under the
  environment at the fork with the parameters defined and the
  equations that the n-way join of the use environments gives
  (`types/env/join_env.ml`): on the parameters and on any other name
  of the environment at the fork whose type an application has
  refined.
- **What follows.** A primitive on a parameter whose type is a set of
  constants is computed on every member (`Binary_arith_like.simplify`
  of `simplify/simplify_binary_primitive.ml`), a comparison is folded
  where every pair agrees, and a `Switch` loses the arms that the
  type of its scrutinee excludes (`simplify/simplify_switch_expr.ml`).

## 2. What is asked

One function more, in the types library, and its call in one of the
two places where the validation calls the rewrites from the types
today.

- **One application, first, and not part of this request.** The
  function called today rewrites the handler of a continuation under
  the environment of its one application where `find_use` finds
  that application, which it does not where the application is in
  the handler of another continuation.
  FlambdaSimplifyPassSpec.gather_uses gathers the applications there
  too. Where it gathers one, no join is needed: the handler is
  rewritten under the environment made for that application
  (`use_env`). Simplify knows as much at the default flags
  (`should_do_join`: at most one use). Nothing of section 3 is
  needed for it: `gather_uses_refines_statement` says, of every
  state, that the handler may be rewritten under any environment
  that every application gathered admits, and
  FlambdaSimplifyUsesSpec.use_env_satisfied_statement that the
  environment made for an application is one that it admits. It is
  a case more of the function called today, to be stated and proved
  apart, before anything of the join. This request supposes it;
  section 6 says what it turns.
- **The function.** FlambdaSimplifyCarriedSpec.simplify_expr_carried,
  which the validation calls today, with a boolean `join` and one
  case more. The case is taken where `join` is true and the boolean
  of the environment is true, at a non-recursive `Let_cont` of whose
  continuation `find_use_carried` finds no single application and
  the gathering finds two or more. The gathering is the recursion of
  `gather_uses` on the forms of FlambdaSimplifyCarriedSpec.v. The
  source is the environment of the `Let_cont` with the parameters of
  the handler defined at their kinds. Each application gives a use
  made from the source. The model's join is asked
  (FlambdaJoinMeetSpec.model_join_with). The handler is rewritten
  under the source with what is read of the answer for each
  parameter, if none of the binders passed on the way to the
  applications is free in what the handler becomes. Where a test
  fails, or the join answers nothing, the handler is rewritten as it
  is today.
- **With `join` false it is the function called today.** That is to
  be a theorem, by the recursion of the two. So nothing that is
  stated of the function called today is lost, and where the flag is
  off no verdict can move.
- **No arm is pruned.** It is the first function with the case
  added, not the function that prunes
  (FlambdaSimplifyPruningSpec.simplify_expr_pruning): the arms of a
  `Switch` that the type of the scrutinee excludes stay. Pruning
  them is a request of its own (below).
- **Which join.** `model_join_with` at the repaired test for
  recovering relations (`Join_env.repaired_choices`), given the meet
  of expanded types made with the join that forgets
  (`Meet.meet_expanded_head forgetful_join repaired_choices`), at a
  fuel that is fixed. The contract that the call rests on holds of
  any test for recovering relations, so the human's decision 9
  (status/T5.md, "the changed join") is not needed for it: the
  choice is which function is run, and both are proved.
- **The uses.** A use is the source one scope further, in which each
  parameter is then given what the application has for its argument.
  Where the canonical element of the argument at the application is a
  `Simple` that the source knows, the parameter is made equal to it
  (FlambdaJoinUsesSpec.alias_with_equation). Otherwise, where it is a
  variable, the parameter is given the type that the application has
  for that variable, with the variables that the source does not know
  put out of it (`Join_env.expand_variable`). A step is made only if
  the side conditions of FlambdaJoinUsesSpec.made_from pass as tests;
  a parameter whose step is not made is left with its kind. Nothing
  is given to a variable of the source that is not a parameter.
- **What is read of the answer.** For each parameter, the type that
  the target has for it, with the variables that the target knows
  and the source does not put out of it
  (FlambdaTypeProject.project_variables_out), given to the parameter
  in the source by the same two steps under the same tests. So no
  variable that a join made is known to an environment of the
  function, and a later join has no name of an earlier one to avoid.
- **The tests.** Each is a boolean function, and where one fails the
  handler is rewritten as today: a meet may be made in the source
  (`types_fit_b`, with the boolean of the environment); every
  variable that the source knows may occur in terms; no use is
  bottom; the variables kept are defined at the uses
  (`kept_defined_at_uses_b`); the binders passed are not free in the
  result.
- **What the validation calls.** A function of a boolean and a term.
  Where the boolean is true, the sets of closures of the term are
  well formed (`sets_well_formed`) and its numbers are in range
  (FlambdaWellFormedSpec.numbers_in_range), it is the function above
  with `join` true, from the environment that knows nothing.
  Otherwise it is FlambdaSimplifyCarriedSpec.simplify_by_types_carried,
  as today. The two tests are of the term alone. The second is
  needed: a term that fails it may make a block of tag 300, which the
  machine runs (FlambdaRangeSpec.tag_out_of_range_statement), and the
  contract of the join is false of a run that holds such a block
  (FlambdaJoinSpec.v, at `blocks_have_tags`). No primitive changes
  its meaning for it, and no statement gains a premise.
- **The flag.** The boolean is given by the tool from the flag that
  it is run with: a validation that joins where Simplify did not
  makes the term before more reduced than the term after (section
  6). How `validate_unit` is given it is V2's (question 3). An
  argument of `validate_unit` changes the text of every statement
  that names `validate_unit`.
- **Where it is called.** In `normalise_lifted`, where `guard_scope`
  of the rewrites from the types is called today, and not in
  `normalise_before`: section 4 says why. No new call site.
  FlambdaValidateImportsSpec.normalise_lifted_free_in computes the
  terms of `normalise_lifted` again and has the same call: it changes
  with it.

Not asked here; each is a request of its own, and section 6 says
what each turned: the arms of a `Switch` pruned by the same
function; what an application knows of a variable of the source that
is not a parameter, carried into its use; the environment of an arm
made by the meet; the relation of `Is_int` and `Get_tag` to their
argument; a second call before the rounds on parameters; the call in
`normalise_before`.

## 3. The statement, and what its proof rests on

Of the function that the validation calls, `joining`:

    ∀ flag e, program_refines e (joining flag e)
    ∀ imports flag e, unit_refines imports e (joining flag e)

with no premise: the conditions are tests made by the function. And
of the function under it, that with `join` false it is
`simplify_expr_carried`.

The proof is from the states of the run of a unit, not from every
state: those that have `run_valid` and are in range. Nothing below
is a premise of the two statements. What is named is in the tree;
what is to be shown is listed again in section 5.

- **`run_valid`** (FlambdaSimplifyPruningSpec.v): the sets of
  closures of every term that the state holds are well formed and
  every value is valid. A step keeps it
  (`run_valid_kept_statement`), and the state that a unit starts in
  with nothing imported has it if its sets pass the test
  (`run_valid_initial_statement`).
- **The range** (FlambdaRangeSpec.v). `state_in_range` says that the
  term left to run, the values of the variables, what the
  continuations keep, the code and what the symbols are bound to are
  in range. A step keeps it (`step_in_range_statement`), a unit
  whose numbers are in range starts in it with nothing imported
  (`run_in_range_statement`), a block that a variable holds then has
  a tag in range (`blocks_in_range_statement`), and the check does
  not look at names (`numbers_in_range_renamed_statement`). The
  contract of the join asks something else, of the valuation that it
  is given and not of the state: `blocks_have_tags`
  (FlambdaJoinSpec.v, a part of `run_with_values`) is of every
  `Simple` whose variables the use knows, a symbol among them, and
  says that the block it stands for has a tag that a type can speak
  of. The passage from the one to the other is to be shown.
- **The contract of the join in the machine**
  (`model_join_with_in_machine_statement`, FlambdaJoinInTermsSpec.v).
  Its premises, and where each is to come from:
  - of the meet that is given, its two contracts:
    `meet_with_forgetful_join_has_contracts_statement`
    (FlambdaJoinMeetSpec.v);
  - of the inputs (`join_inputs_well_formed`, `uses_kinded`,
    `uses_agree_with_source_on_kinds`, `uses_fit_otherwise`,
    `uses_know_the_source`, `terms_in_scope_at_uses`):
    `uses_made_from_source_statement` (FlambdaJoinUsesSpec.v). Its
    own premises are three. A meet may be made in the source: the
    test `types_fit_b` with the two conditions that the boolean of
    the environment stands for (`types_fit_b_fits_statement`). The
    variables to avoid include every variable that the source knows:
    to be shown of the list that the function gives
    (`Join_env.variables_of_env` of the source). Each use is
    `made_from` the source: to be shown step by step from the tests,
    for a parameter made equal that the two are canonical, different
    and of one kind, and for a parameter given a type that the
    parameter is of the kind of the type in the environment
    (`simple_of_kind`), that the type fits the environment
    (`type_fits`), is not an alias, and is neither obviously unknown
    nor obviously bottom;
  - that the join answers, that the use is the one that the inputs
    have at an index (`use_at`: the index of the application in the
    list gathered, which the function makes the inputs from), that
    the use is not bottom, and `kept_defined_at`: the case of the
    function, the list and two of its tests
    (`kept_defined_at_uses_b_sound_statement`);
  - of the state at the handler and a valuation: that the valuation
    satisfies the use and the source strictly; that the state binds
    the variables that may occur in terms at the use, and agrees with
    the valuation on them; and `run_with_values`, which is that the
    static environment is valid (`run_valid_statics_statement`), that
    the valuation gives a value to every variable that the use knows
    (`known_in_terms_have_values_statement`, with the test that every
    variable of the source may occur in terms), and
    `blocks_have_tags`. These are to be shown from what the recursion
    has at each application: that the state there satisfies the
    environment of the application, which says no less than the
    environment of the `Let_cont` (`gather_uses_weaken_statement`). A
    parameter made equal holds because the jump gives the parameter
    the value of the argument. A parameter given a type holds by the
    laws of the projection (`expand_variable_sound_statement`,
    `project_variables_out_sound_statement`, FlambdaJoinDefineSpec.v).
    Those laws ask that each type put for a variable be true of that
    variable in the state (`expansions_true`); the types put are the
    ones that the environment of the application has, so that is had
    from the satisfaction of that environment. The statement about
    the shape of the uses gives none of this.
- **What is read of the answer.** The contract concludes that the
  state at the handler satisfies the target, through a valuation that
  agrees with the first on what the use knows. That the state
  satisfies the source with what is read for the parameters is to be
  shown, by the same two laws at the variables that the target knows
  and the source does not.
- **The handler and the `Let_cont`.** `gather_uses_refines_statement`
  is of every state: it asks that each application admit the
  environment (`application_admits`) whatever the state that
  satisfies the environment of the application. The answer of the
  join is admitted only for the runs above. So what is needed is the
  form of that statement from the states that have `run_valid` and
  are in range, as `find_use_refines_from_valid_statement` is the
  form of `find_use_refines_statement`. That the environments
  gathered have the two conditions is
  `gather_uses_known_to_fit_statement`.

## 4. What the call reaches in the landed statements

The theorem of the function is from the states that have `run_valid`
and are in range. The theorem of the function called today is of
every state (`expr_refines`).

- In `normalise_lifted` no landed statement gains a premise. Only
  the verdict of the comparison of lifted terms rests on that
  function, and what is stated of that verdict is of the unit run on
  its own from the state that it starts in: with nothing imported
  (`validate_unit_sound_statement`, by
  `normalise_lifted_program_refines`), and from the static
  environment of its imports
  (`validate_unit_sound_verdict_imports_statement`,
  FlambdaValidateImportsSpec.v), each with its form for the second
  asking. The static environment of the imports has no code and
  binds each import to an object of which nothing is known
  (`Static_imported`), which passes the test of validity and the test
  of the range. That the state that a unit starts in from it has
  `run_valid` and is in range is to be shown, and is not a premise.
  That `normalise_lifted` keeps scope is had by `guard_scope`, as
  today; that it commutes with renaming up to the names it makes
  needs item 3 of section 5. The definition changes, and the
  statements that it reaches, which the search of
  `rocq/check-changed-defs.py` lists when it does, say of the
  function with the added case what they said, as when the first
  function was added there.
- In `normalise_before` it is otherwise. `normalise_before_refines`
  is `expr_refines`, and the statements of FlambdaValidateImportsSpec.v
  use it of a unit run from its imports and from any static
  environment (`validate_unit_sound_imports_statement`,
  `validate_unit_sound_from_statement`, the two of the head and
  their forms for the second asking). With the function there, those
  from any static environment would gain a premise: that the static
  environment is valid and in range. That is a strengthened premise
  of landed statements, and it is not asked here.

So the call asked is the one of `normalise_lifted`. On the units
measured it turns what the call in both places turns (section 6): a
unit that the join turns through the term before normalised, where
the call is in both places, is turned through the comparison of
lifted terms where the call is in `normalise_lifted` alone.

## 5. What is in the tree, and what is not

In the tree: the statements named in section 3; `gather_uses` with
what is proved of it; the function called today and its equality
with the first function; the range of the run of a unit with nothing
imported. Also, in FlambdaSimplifyUsesSpec.v,
`let_cont_handler_joined_statement`, for a `Let_cont` whose body is
the application: the handler may be rewritten under any environment
that has the guarantees of a join of the environments made for the
applications. It is not what the call rests on: it asks the
guarantees of every run (FlambdaJoinSpec.join_guarantees), where
what is proved of the model's join is of the runs that have
`run_with_values`; and its uses are those made for one application
(`use_env`), not uses made from the source.

Not in the tree:

1. The range, for the join: from `state_in_range` of the state at
   the handler, `blocks_have_tags` of the valuation that the contract
   is given. For a variable that the use knows, by the value that the
   state has for it, the valuation agreeing with the state on the
   variables that may occur in terms and the test saying that every
   variable known is one. For a symbol, by what the static
   environment binds it to. A tag in range is a tag that a type can
   speak of.
2. The start from the imports: `run_valid` and `state_in_range` of
   the state that a unit starts in from the static environment of
   its imports.
3. Renaming. The validation asks that a rewrite commutes with
   renaming up to the names it makes. FlambdaJoinMeetRenameSpec.v
   says what is proved: the join that Simplify calls, with the
   renamed source of new names, answers the renamed answer
   (`model_join_related_statement`). That is of the model's join at
   the model's meet, and of a renamed source. Needed here, and stated
   nowhere:
   - the same of `model_join_with` given the meet made with the join
     that forgets;
   - that two sources of new names give answers that differ by a
     renaming of the variables made (that file says it is not
     stated);
   - that what is read of the answer, the variables made being put
     out of it, is then the same for the two;
   - that the uses, the steps and the tests commute with renaming.
4. The function and its proofs: that the valuation at the handler
   shows each use (the last premise of the contract, in section 3);
   that what is read of the target is satisfied; the form of
   `gather_uses_refines_statement` from the states of the run; the
   theorem of section 3 by the recursion; that the function with
   `join` false is the one called today.
5. How `validate_unit` is given the flag, and the tool giving it.

## 6. What was run

Diagnostics, with a copy of the tool in which the function and the
place of its call are chosen when it is run. The functions are
drafts with no proof. The tool is built from the tree that this
request is cut on. None of the units named by a count below is in
this tree unless it says so.

**The function asked.** The draft is the function of section 2 with
its tests and its two guards, on the forms of
FlambdaSimplifyCarriedSpec.v. With no join and nothing done where one
application is gathered it gives, byte for byte, the outputs of the
tool as it is, on the 125 units of the first two lines below. At
`-O3`, the units validated with the one application of section 2
only, with the join called in `normalise_lifted`, and with the join
called in both places:

    58 units written for what the join knows       32   47   47
    67 units written for the types                 52   57   57
    600 generated units                           591  594  594
    240 generated units with loops and exceptions 140  140  140
    the corpus as it was, 259 units               240  240  240

No unit is lost, and the units turned are the same in the last two
columns. With the call in `normalise_lifted` each of them is
validated by the comparison of lifted terms; with the call in both
places three generated units are validated by the term before
normalised instead. Of the 58, the fifteen turned are of the sixteen
whose first cause was the join; the sixteenth has a value that is the
result of `Boolean_not`, of which the function knows the kind only.
The seven of the 58 whose handler has a parameter for a field that
Simplify reads in scope are not turned.

Processor time for a whole set, with the one application only and
with the join called in `normalise_lifted`: 3.5 and 2.6 seconds for
the 58, 2.1 and 2.1 for the 67, 12.3 and 12.6 for the 600, 16.0 and
16.7 for the 240, 3.6 and 3.8 for the 259. On ten units written to be
slow for the function (hundreds of bindings in a row), 3.9 and 4.5
seconds. The function is to be on the forms that carry what is known
of the environment: on a tree a few changes of the validation
earlier, the same ten units took 36 seconds with the draft on those
forms and 332 with it on the forms that test the environment at
every `Let`.

**The terms of the other workstreams' probes** (16,057 files, each
with the flag that its directory names; not N1's renamings, X4's
mutants, nor the sets above). With the join called in
`normalise_lifted` at `-O3`, six units more are validated than with
the one application only. None is lost. One unit that is validated
at the first asking is validated at the second: the join there makes
the term before more reduced than the term after, and the second
asking reduces both.

**The flag.** At the default flags, with the join made wherever
several applications are gathered, 14 of the 58 that are validated
are not, and 5 of the 67: the term before is then more reduced than
the term after. Hence the boolean.

**One application** (section 2; apart from this request). At
the default flags one unit more of the corpus of this tree is
validated, `exn_with_argument`, and three more of the other
workstreams' probes; no unit of the corpus (370 units), of the
probes, of the 58, the 67, the 600 or the 240 is lost, and every
other output of those sets is the same.

**A second call of the function called today**, after the last
rounds of `normalise_lifted` and with no join, changed no verdict on
any of the sets above at either setting, on a tree a few changes of
the validation earlier, and cost time.

**The arms pruned by the same function** (not asked): one more of
the 58 and one more of the 67, none of the other sets.

**Wider functions, on an earlier tree** (not asked; the counts are of
that tree). With the environment of an arm made by the meet and the
relation of `Is_int` and `Get_tag` to their argument: one more unit
of fifteen. With a second call before the rounds on parameters: none
more with the join alone; with those two additions, two more of the
fifteen, three more of the 600 and one more of the corpus (the
validation has by then unboxed a variant parameter into parameters
that nothing ties).

## 7. Questions

1. Settled, and not asked again: verdicts at `-O3` count
   (status/T2.md, "Next", with item 35 of "Decided"), which is why
   this measure was asked for. All that the join turns is at the
   settings where Simplify makes its joins, `-O2` and `-O3`; what was
   run here was run at `-O3`, and what is recorded of the ruling
   speaks of `-O3`. The one application of section 2 turns a unit at
   the default flags and does not wait for the join.
2. For the orchestrator: whether the join is done, given what is to
   be shown (section 5, items 1 to 4, of which item 3 has a fact
   that is stated nowhere) and what it turns (section 6); and whether
   the call of `normalise_lifted` alone is the one wanted (section
   4), the statements from a static environment being left as they
   are.
3. For V2: how `validate_unit` is given the flag, an argument of it
   changing the text of every statement that names it; and whether
   the tool is to give the flag from `-O2` and `-O3` alone or from
   the flag of the join points when it is passed.
4. For T5 and N3: item 3 of section 5, and who states each part.
5. For C1 and C5: item 2 of section 5 for the range, which is of
   FlambdaRangeSpec.v and of the static environment of
   FlambdaImportsSpec.v. `run_valid` of that state is T2's.
