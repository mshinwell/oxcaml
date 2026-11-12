# Names in the model of Flambda 2

How the model treats bound names, what is proved about them, and what a
change to the model owes. Owner: N1. The compiler's side is
`middle_end/flambda2/nominal/`; section 10 says what it would take
for it to obey the same laws.

## Where it stands

As of the tree that has the first step of the heap, the passes for
loops and the meet of types under renaming. The sections below say
each thing in full.

**One account of the free names.** The free names of a term are one
function for each sort (`FlambdaBindersSpec.v`), which goes into code.
Written with it: the three conditions on binders of well-formedness;
the statements that the names a binder binds may be renamed
(`FlambdaCanonicalFreeNamesSpec.v`); the rules of `alpha_equivalent`;
what a rewrite that makes names owes. An older account, relations
that do not go into code, is still defined. The statements that a
binding not used may be removed are written with it on purpose
(`FlambdaNominalSpec.v`): they ask nothing of the code, a name that
occurs only in code does not stop a binding from being removed, and
the rewrites of the validator that remove bindings are proved from
them. The other places where it is still used are in the last table
here.

**What commutes with renaming.**

| What | Where | By |
|------|-------|----|
| The machine: a step, a run, a behaviour; equivalence and refinement, of states and of expressions | `FlambdaEquivarianceSpec.v` | N1 |
| The machine with a stack of exception handlers and of calls | `FlambdaTrapSpec.v` | the owner of exceptions |
| The machine with a heap, and its refinements; the heap is left as it is | `FlambdaHeapEquivarianceSpec.v` | N1 |
| The free names; the three conditions on binders; `alpha_equivalent` | `FlambdaAlphaSpec.v` | N1 |
| The comparison `expr_eqb` | `FlambdaCompareAlphaSpec.v` | N1 |
| The rewrites of the normalisation, the passes for loops, the checks of well-formedness (exception handlers and trap actions among them), the check of kinds, the normalisation of the term after and the first phase of that of the term before | `FlambdaValidatorEquivarianceSpec.v` | N3 |
| The normalisation of the term before and that of a term in which something was lifted: up to the names that a round makes. `validate_unit`: where the code of the term before is closed | `FlambdaValidatorEquivarianceSpec.v` | N3 |
| Identities of primitives, lifting, lifting out of code, the binding of `my_closure`, ranges, sharing of primitives and of projections, folding at known symbols, unused and known value slots, the order of static bindings, the static closures in sight, code moved up, code and static bindings bound first, lifting out of the arms of a test, inlining within a group of code, the unboxing of parameters, the merging of the arms of a `Switch`, the demotion of exception handlers | the `Spec` file of each pass | the owner of each |
| The second asking of the validation, `validate_unit_knowing`: where the code of the term before is closed | `FlambdaValidateKnowingSpec.v` | the owner of that file, N3 |
| Typing environments and their levels, extensions, aliases, types, provers | the types library (`FlambdaEnvRenameSpec.v`, `FlambdaTypeRenameSpec.v`, `FlambdaEnvAliasesRenamingSpec.v`, `FlambdaTypingEnvExtensionSpec.v`, `FlambdaProversRenameSpec.v`) | N3 and the owners |
| The model of Simplify: the function that rewrites a term from the types, the same with pruning, the rewrites of a `Switch`, following aliases with the aliases of the library | the types library (section 7 has the files) | the owners of those files |
| The meet of types and of expanded types, and the functions that add to a typing environment, given a join that commutes with renaming; with the join that forgets, with no premise | the types library (`FlambdaMeetRenameSpec.v`) | the owner of the meet, N3 |
| The join of typing environments and the join that Simplify calls, with the source of new names renamed; with them, the meet of the model with its own join | the types library (`FlambdaEnvRenameJoinSpec.v`, `FlambdaJoinMeetRenameSpec.v`; the traversal of types, as lemmas of `FlambdaEnvRenameJoinTypesProofs.v`) | N3; N1 for the traversal |

Those of the machines, and of the rewrites and checks of the first
six rows, are equations that hold of every state and of every term.
The seventh row is not, nor the second asking of the validation: a
round of the term before makes names.

**What has a finite support.** Every expression and every state
(`FlambdaStateSupportSpec.v`); a state with a stack (the same file); a
state with a heap (`FlambdaHeapEquivarianceSpec.v`). So what each of
the three machines runs is a nominal set, and its execution is an
equivariant function. None of the three is an instance of the
interface; section 6 says why. The locations of the heap are a sort
of names of their own; their permutations are not defined yet (they
are owed when the heap is in the state of the machine).

**A rewrite that makes names** does not commute with renaming. It
owes two things, defined in `FlambdaValidatorEquivarianceSpec.v`:
that it commutes up to the names that it makes (`equivariant_up_to`),
and that it keeps scope (`keeps_scope`). Rewrites that have both
compose, and the comparison answers the same on their results. Two
are in the tree: inlining at fresh names (`FlambdaInlineFreshSpec.v`:
two choices of names give alpha-equivalent terms) and giving every
binder a name of its own (`FlambdaRenameApartSpec.v`: the result on a
renamed term is the result under a renaming that agrees with the
first on the names of the term). The validation applies the second
in each round of the term before. Every rewrite of a round keeps
scope (`FlambdaKeepsScopeSpec.v`, `FlambdaValidateScopeSpec.v`,
`FlambdaLoopsScopeSpec.v`, `FlambdaStaticsScopeSpec.v`), so the
normalisation of the term before
commutes with renaming up to the names that it makes, and
`validate_unit` answers the same on a pair of terms and on the pair
renamed where the code of the term before is closed. A lifting holds
the two continuations of its unit, which the term may no longer
mention when the lifting is made. So the rounds after a lifting are
given those continuations, make no name that is one of them
(`rename_apart_avoiding`), and are stated up to the names that they
make with one clause more: the second renaming does to the
continuations given what the first does
(`equivariant_up_to_avoiding`).

**Still written in the older style.** `requests/N1-one-free-names.md`,
section 7, has the reason for each and what it would take.

| What | Whose |
|------|-------|
| The three statements that a binding not used may be removed, and three that say that their premise is kept by renaming and by alpha-equivalence: on purpose | N1 |
| The relations `var_free_in_expr` and `cont_free_in_expr`, as definitions: for those six statements, the rows below and the proofs | N1 |
| `FlambdaApplySpec.inlinable` | the integrator |
| The checks `FlambdaNormaliseSpec.expr_in_scope` and `FlambdaWellFormedSpec.free_continuations`, which run | the integrator |
| The tests of freedom `var_free_b` and `cont_free_b` of the rewrites that remove bindings | the integrator |
| The older forms of the statements that rename, as lemmas of `FlambdaNominalProofs.v` and `FlambdaAlphaProofs.v`, for the proofs that use them | N1 |

**Owed.** That the join of typing environments, with one source of
new names, answers the renamed answer up to the variables that it
makes (section 7); the
permutations of locations; the functions on types that have no
statement yet; and the rows of the table above.

## 1. The names

Two sorts of name are bound by terms and moved by renamings: variables
and continuations. Symbols, code ids, value slots and function slots
are global: no renaming moves one. A run-time value holds no variable
and no continuation (a closure holds code ids and values), so nothing
is renamed in a value. If a new place comes to hold names, it is a
sort of its own. The locations of the heap (`FlambdaHeapSpec.v`) are
one: no renaming of variables or of continuations moves a location,
and the permutations of locations, when they are defined, move nothing
in a term.

Names are compared by equality only. The one function that looks at
the number of a name is `fresh_name` (`FlambdaNameAbstractionSpec.v`),
which gives a name outside a list of names.

## 2. Where things are

| File | What it has |
|------|-------------|
| `FlambdaBindersSpec.v` | What each binder binds and where; the free variables and free continuations of a term, as one function for each (they go into code); the three conditions on binders: `names_in_scope`, `binders_distinct`, `code_closed` |
| `FlambdaScopeSpec.v` | `state_in_scope`: what a run keeps of scope; a state in scope reads no variable without a value and leaves only by a continuation it was given |
| `FlambdaNominalSpec.v` | Permutations and renamings; the action on terms, `rename_expr`, code included; that the binders of code may be renamed; the older relations of free names, and with them that a binding which is not used may be removed |
| `FlambdaAlphaSpec.v` | The action is that of a group; the free names and the three conditions are equivariant; `alpha_equivalent`, by its generators, is equivariant, keeps the free names and the three conditions, and is sound for the semantics |
| `FlambdaCompareAlphaSpec.v` | The comparison `expr_eqb` is an equivalence relation, contains `alpha_equivalent` and does not depend on the names; two pairs of terms that it accepts outside well-formed terms |
| `FlambdaEquivarianceSpec.v` | The action on states; a step, a run and a behaviour commute with it; two rewrites commute with it |
| `FlambdaNameAbstractionSpec.v` | The interface of `nominal/`: things that contain names, bindable names, name abstractions, `pattern_match`, with their laws; `fresh_name` |
| `FlambdaNominalInstancesSpec.v` | The terms as instances of the interface; each binder as a name abstraction |
| `FlambdaFreeNamesSpec.v` | The older accounts of free names agree with the one function where code is closed, and what is free by them is among the free names on every term |
| `FlambdaCanonicalFreeNamesSpec.v` | The names that a `Let`, a `Let_cont` or a handler binds may be renamed; corollaries, with the one function, of the statements about a binding that is not used |
| `FlambdaStateSupportSpec.v` | Every expression and every state has a finite support: with the action, the states are a nominal set |
| `FlambdaHeapEquivarianceSpec.v` | The action on the states of the machine with a heap, which leaves the heap alone; a step, a run and a behaviour of that machine commute with it; its refinements are preserved by renaming; its states have a finite support |
| `FlambdaFreshQuantifierSpec.v`, `FlambdaFreshAbstractionSpec.v` | The quantifier "for all but finitely many names"; `fresh_names`; equal abstractions of one name and of a list of distinct names, said with the quantifier |
| `FlambdaFreshBindersSpec.v`, `FlambdaAlphaFreshSpec.v`, `FlambdaAlphaGroupSpec.v` | For each binder, the rule that compares two binders at fresh names, and that it can be read both ways on terms with distinct binders and closed code; the recursive group as a name abstraction |
| `FlambdaCompareConverseSpec.v` | What the comparison accepts is alpha-equivalent, on terms with distinct binders and closed code |
| `FlambdaInlineFreshSpec.v` | Inlining a call with the binders of the code exchanged for fresh names; two choices give alpha-equivalent terms |
| `FlambdaValidatorEquivarianceSpec.v` | Each rewrite and each check of the validator commutes with renaming: the rewrites of the normalisation, the checks of well-formedness and of kinds; what a rewrite that makes names owes instead, and with it the normalisation of the term before and `validate_unit` |

The four rows before the last are the second prover's files, and the
last is the third prover's.

In the types library, `FlambdaEnvAliasesRenamingSpec.v` has the action
on the aliases, and `FlambdaTypeRenameSpec.v` and
`FlambdaTypeNominalSpec.v` the action on types and on environment
extensions, each with the same laws, as instances of the interface.
`FlambdaEnvRenameSpec.v` has the action on typing environments and
their levels, with the same laws, and says that the functions of a
typing environment commute with it. `FlambdaMeetRenameSpec.v` has the
action on the environment of the meet, and says that the meet
commutes with it when the join that it is given does.

## 3. The binders

| Binder | Binds | In scope in |
|--------|-------|-------------|
| `Let x kind d body` | `x` | `body` |
| `Handler params metadata handler` | `params` | `handler` |
| `Let_cont_non_recursive k h body` | `k` | `body` |
| `Let_cont_recursive handlers body` | the continuations of `handlers` | `body` and every handler |
| `Code params my_closure ret exn metadata body` | `params`, `my_closure`, `ret`, `exn` | `body` |

A `Let_static` binds no variable and no continuation. Code is closed:
its body has no free name but what the code binds (decision D31).
Kinds, arities and metadata have no names in them: a renaming leaves
them as they are, and two terms that are the same up to bound names
have the same ones.

Two places name without binding. A trap action of an `Apply_cont`
names the continuation of an exception handler, and the exception
continuation of a call may come with extra arguments, which are
simples. The continuation and the simples are renamed, and are among
the free names.

A well-formed unit meets three conditions, which are checks:

- `names_in_scope`: no free variable, and no free continuation but the
  unit's return and exception continuations;
- `binders_distinct`: the names of one binder are distinct, and a
  recursive group has a handler;
- `code_closed`: all code, at any depth, is closed.

The last two ask more than the compiler checks (decision D32;
discrepancies N1-3 and N1-4). Each of the three is unchanged by a
renaming.

## 4. Renaming

A renaming is a permutation of the variables and one of the
continuations, each a list of swaps. It acts on everything that holds
names: terms, code, static constants, environments, continuation
closures (and a continuation kept with the extra arguments of a call:
the arguments are values, the continuation is renamed), the code of
the static environment, states, the result of a step and behaviours.
It renames bound and free occurrences alike, so it never captures. The
laws of a group hold of the action.

It is the action of the compiler's renamings that are permutations
within one unit (what the freshening of a binder uses). A renaming with
an import map is another operation and is not modelled (discrepancy
N1-8).

Execution commutes with renaming, with no condition:
`step (rename_state r s) = rename_result r (step s)`, and the same of
`run` and of `behaves`. So a rewrite that is correct with one choice of
names is correct with every other.

The same holds of the machine with a heap (`heap_step`, `heap_run`,
`heap_behaves`, and its refinements `heap_refines` and
`heap_expr_refines`): the action renames the state without its heap
and leaves the heap as it is, since a cell holds values.

## 5. The same up to bound names

There are two accounts, and they are related.

- `alpha_equivalent`: the least equivalence, closed under contexts,
  that relates a binder with its scope to its image under a renaming
  that fixes the free names of the two. Each rule asks that the code in
  what is renamed is closed; the rule for the binders of code asks
  nothing else. It is sound: alpha-equivalent terms behave alike under
  all environments. Alpha-equivalent terms have the same free names,
  and satisfy the same of the three conditions of section 3
  (`alpha_equivalent_code_closed_statement` and the statements beside
  it), so the conditions are conditions on the classes.
- `expr_eqb`: the comparison that the validator runs, by recursion on
  the two terms with a map of paired names. It is sound, it is an
  equivalence relation, it accepts every two alpha-equivalent terms,
  and its answer does not change when the two terms and the names
  paired so far are renamed (`expr_eqb_equivariant_statement`).

The comparison is the primary notion (it is a function and it is what
runs); the rules of `alpha_equivalent` are facts about it. The converse
(what the comparison accepts is alpha-equivalent) is for terms with
distinct binders and closed code, which are the terms that
well-formedness admits. It is proved
(`FlambdaCompareConverseSpec.expr_eqb_iff_alpha_equivalent_statement`):
on those terms the comparison and alpha-equivalence are one relation,
and the comparison decides it.

At each binder alpha-equivalence can also be said as the papers on
nominal sets say it: two binders are alpha-equivalent exactly when
two things hold. What is outside the scope agrees: the two `Let`s
have the same kind and the same defining expression, the two handlers
or the two pieces of code the same metadata, and the handlers of the
two non-recursive `Let_cont`s are themselves alpha-equivalent (the
handlers of a recursive group are in the scope of its continuations,
and are compared with them exchanged). And the scopes are
alpha-equivalent once the bound names of both are exchanged for the
same fresh names, for all but finitely many choices of them
(`FlambdaCompareConverseSpec.alpha_let_iff_statement`, and the
statements of `FlambdaAlphaFreshSpec.v` and `FlambdaAlphaGroupSpec.v`
for a `Let_cont`, a handler, code, a `Let_static` and a recursive
group). That is how the compiler compares two binders
(`Name_abstraction.pattern_match_pair`).

Outside those terms the comparison accepts more, and is still sound.
Two pairs of terms are accepted and proved not alpha-equivalent:

- `expr_eqb_repeated_parameter_statement`: a handler that repeats a
  parameter, against one that does not. The first has not distinct
  binders.
- `expr_eqb_open_code_statement`: a variable bound around code that
  mentions it, against the same term with the binder, and its uses
  outside the code, renamed. Both have distinct binders; their code is
  not closed, so no rule renames the binder.

Every statement that a bound name may be renamed has the premise that
the code in what is renamed is closed. The comparison, from which
they are proved, treats code as closed. Where code is not closed the
comparison and the rules part: `expr_eqb_open_code_statement` is a
pair that the comparison accepts and that is not alpha-equivalent. No
more than that is shown: the statements about behaviour are not
proved of terms whose code is not closed, and no such term is known
to refute them. Well-formedness admits none.

## 6. The interface

`FlambdaNameAbstractionSpec.v` is the interface of `nominal/` with the
laws the compiler leaves unsaid, for one sort of name at a time: a
type whose values contain names has an action, free names and an
equality (`=` where there is no binder, alpha-equivalence for
expressions); a name abstraction is a pair of bound names and a scope,
equal to another when each can be opened, by a permutation that fixes
its free names, to the same bound names and equal scopes.

Instances: `simple`, `named`, static constants and environments;
expressions whose code is closed, for each sort; and, in the types
library, the aliases, the types and the environment extensions. Each
binder of section 3 is shown to be a name abstraction: equal
abstractions give alpha-equivalent terms
(`FlambdaNominalInstancesSpec.v`; for the
recursive group, whose scope is its handlers and its body together,
`FlambdaAlphaGroupSpec.group_abstraction_statement`). The laws of
abstractions, and that opening two equal abstractions at the same
names gives equal scopes (`pattern_match_pair_statement`), then hold
of them with no further proof.

The quantifier "for all but finitely many names" is a derived view of
equal abstractions (`FlambdaFreshQuantifierSpec.v`,
`FlambdaFreshAbstractionSpec.v`), for one bound name and for a list of
distinct bound names. The definition by permutations stays. Section 5
says what the quantifier gives at the binders of terms.

States. The renamings act on the states of the machine
(`FlambdaEquivarianceSpec.v`: the identity, composition, inverses), a
step, a run and a behaviour commute with the action, and every state
has a finite support (`FlambdaStateSupportSpec.v`): so the states are
a nominal set and execution is equivariant between nominal sets. A
state is not an instance of the interface. The interface is for one
sort of name at a time and the machine is renamed in both; and its
`free_names` go with an equality under which a permutation that fixes
them changes nothing. For a state as it is written that equality is
`=`, and the names are then all that occur, bound ones included,
which is the support of `FlambdaStateSupportSpec.v` and not the free
names of anything. For a state up to bound names, the equality would
have to be defined through every handler held by a continuation and
all the code of the static environment, and the laws would hold only
of states whose code is closed, as for expressions. So the
equivariance of execution stays stated directly, for both sorts at
once.

## 7. What is owed for each function on terms

A function on terms that models something the compiler does owes that
it commutes with renaming, in one of these forms:

- a transformation: `f (rename_expr r e) = rename_expr r (f e)`;
- one that takes names, or a map keyed by names: the same with that
  argument renamed too;
- a check: `c (rename_expr r e) = c e`, with any names it carries
  renamed;
- one that makes a name: it takes the names to avoid and uses
  `fresh_name`, and its statement relates two choices by the
  permutation that swaps them.

**Why a function that makes names cannot commute with every
renaming.** A source of new names is a function from the names to
avoid to a name outside them; `fresh_name` is one. No such function
commutes with every renaming. Take a list `l`, the name `n` that the
source gives for `l`, and a name `y` that is not in `l` and is not
`n`. The renaming that swaps `n` and `y` moves no name of `l`, so the
source gives `n` for the renamed list; and `n` renamed is `y`. The
same goes for a function that asks the source for a name and lets
that name show in its answer: swap the name with one that is neither
in the arguments nor in the answer; the arguments are as they were
and the answer is not. So such a function does not commute with every
renaming, whatever the source is. This is not a defect of
`fresh_name`, and another choice would not help: that no function
which respects renaming can pick a name out is what it is for names
to be compared by equality only.

Of this, what is a theorem is the first part, of the source alone
(`no_source_commutes_statement`, in
`types/rocq/FlambdaEnvRenameJoinSpec.v`). That the join of typing
environments with one source does not commute with every renaming is
the argument above applied to it. It is proved of one join of the
model, by computation
(`types/rocq/FlambdaJoinMeetRenameExampleSpec.v`): the join makes a
variable, and the renaming that exchanges it with a variable which is
nowhere in the inputs leaves the inputs as they are and changes the
answer. It is not proved of every source.

**What the caller of such a function owes.** `fresh_name` gives a
name outside the names that it is given, and no more. A name that a
function makes and leaves in its answer is a binder of that answer.
Two answers that were made apart may each hold a made name that is
spelt as the other's is, and whatever then reads the two side by side
takes the two for one name. The compiler does not meet this: its
names are distinct on every path. The model met it in the tests of
types, at joins of environments that joins had made. So the names to
avoid are every name that the answer may later stand beside, not only
the names of the arguments.

For the join of typing environments the premise is `avoids_known`
(`types/rocq/FlambdaJoinSpec.v`): the variables to avoid include
every variable that the source or a use knows. It is enough where
every use knows exactly the variables of the source
(`uses_know_the_source`, `types/rocq/FlambdaJoinInTermsSpec.v`): no
variable is then known to two uses without being one variable of the
source. Uses that are made from a source in which a meet may be
made, by going one scope further and then by steps that make a
variable equal to a `Simple` or give it a type (`made_from`, which
has the conditions of each step), are such, and with variables to
avoid that include those of the source they have the premise
(`uses_made_from_source_statement`,
`types/rocq/FlambdaJoinUsesSpec.v`): no step defines a variable. Of
inputs in which a use knows a variable that the source
does not, the part about valuations is not stated: the join takes a
variable that two uses know for one variable, and a caller that gives
it such inputs owes that it is one. The same is owed for the join
that the meet calls, by whoever shows of the model's meet what the
statements suppose of a meet.

**What such a function owes instead.** One of two things.

- *With the source renamed.* The source is an argument of the
  function, and a renaming acts on it as on any function, by
  conjugation: the renamed source, given a list, undoes the renaming
  on the list, asks the source, and renames what it answers. That is
  a source of new names again. The function then owes an equation of
  the second form above: with the renamed source, on the renamed
  arguments, it gives the renamed answer. Nothing is up to anything,
  nothing is asked of scopes or of code, the equation composes with
  the others of this section, and its proof is the recursion of a
  function that makes no name with one more case, the call of the
  source, which is the definition of the conjugate.
- *With one source on both sides.* The answer for the renamed
  arguments is the answer under a second renaming, which agrees with
  the first on the names that the function was given and may differ
  on the names made. It follows from the first and one more fact,
  that the choice does not matter: two sources give answers that
  differ by a renaming which fixes the names given.

Where the source can be an argument, state the first: a caller that
only has to push a renaming through the function needs no more, and
the second is derived from it.

For a rewrite of terms, the names made are bound in the result, and
the second says that the two results are the same up to bound names.
It is in `FlambdaValidatorEquivarianceSpec.v`, with what makes it
compose:

- `equivariant_up_to`: on a term whose code is closed, the result on
  the renamed term is the result under a second renaming, which
  renames the free names of the result as the first does. The two may
  differ on the names bound in the result;
- `keeps_scope`: on a term whose code is closed, the code of the
  result is closed and no name is free in the result that was not
  free in the term.

A rewrite that is not known to keep scope is made to by a test
(`FlambdaGuardScopeSpec.guard_scope`): it keeps scope whatever the
rewrite is, it is the rewrite where the rewrite keeps scope, and it
commutes with renaming where the rewrite does
(`FlambdaValidateScopeSpec.v`). The normalisation of the term before
applies so, once, between its rounds, the function of the model of
Simplify that rewrites a term from the types (below).

Rewrites that have both compose and iterate, a rewrite that commutes
with renaming has the first, and the comparison answers the same on
the results (`expr_eqb_up_to_statement`).

A caller may hold names that the term does not mention, and need the
second renaming to do to them what the first does: `equivariant_up_to`
says nothing of a name that is not free in the result. Such a rewrite
is given those names to avoid, and owes `equivariant_up_to_avoiding`
(the same file, for continuations): the names given are renamed with
the term, the second renaming renames the free names of the result as
the first does, and it does to the names given what the first does.
It is kept by a rewrite that commutes with renaming and keeps scope,
applied before or after, and by the rewrite applied a number of times
with the same names; with no name given it is `equivariant_up_to`.

Where the names made stay free in the answer, the second is about
answers up to a renaming of the names made, and says less. The join
of typing environments is such a function: it defines the variables
that it makes in the environment that it answers. It owes the first,
and has it, by the third prover
(`types/rocq/FlambdaEnvRenameJoinSpec.v`): what a renaming does to
the source of new names and to the state of the join; that no source
commutes with every renaming; the equation for the two functions that
ask the source; and the equation of the join as a whole, for two sets
of parameters that the renaming relates, as the model's parameters
and the same with the source renamed are. With it
(`types/rocq/FlambdaJoinMeetRenameSpec.v`) the meet of the model with
its own join, and the join that Simplify calls, answer the renamed
answer with the renamed source. The traversal of types that the join
calls (`types/rocq/FlambdaJoinTypes.v`) makes no name and compares no
two variables itself: the variables that it finds in types it hands
to the functions that it is given. Each of its functions gives the
renamed answer on renamed arguments when those do (lemmas of
`types/rocq/FlambdaEnvRenameJoinTypesProofs.v`). The second is not
stated for the join: it needs that two sources give answers that
differ by a renaming of the variables made. Nothing calls it today.
Its caller would be a pass that calls the join on renamed inputs with
the model's one source, as a call of the join in the pass that
rewrites a term from the types would; that call is not made. The
fact that is missing is a simulation of two runs of the whole join
under a renaming that grows at each call of the source, with the
names to avoid containing every name of the state. The third
prover's estimate is a few thousand lines of proof. It stays owed.

Prove it by one recursion over expressions, handlers, bindings and
code. A function whose answer depends on the order or the number of a
name is a finding: record a discrepancy.

Proved: the machine (`step`, `run`, `behaves`); the free names, as
relations and as functions; `code_closed`, `binders_distinct`,
`names_in_scope`; `alpha_equivalent`; `expr_eqb`; `fold_constants`;
`inline_calls`; and, in the fourth form, inlining at fresh names
(`FlambdaInlineFreshSpec.v`: the names made are bound in the result, so
two choices give alpha-equivalent terms).

Proved by the third prover, in `FlambdaValidatorEquivarianceSpec.v`:
the other rewrites of `FlambdaNormaliseSpec.v`,
`FlambdaUnusedStaticsSpec.v`, `FlambdaUnusedContsSpec.v`,
`FlambdaBlockLoadSpec.v` and `FlambdaUnboxSpec.v`; the checks of
`FlambdaWellFormedSpec.v`, those of exception handlers and of trap
actions among them; the check of kinds; the passes for loops
(`FlambdaRecHandlersSpec.v`, `FlambdaSinkContsSpec.v`,
`FlambdaSinkUsesSpec.v`, `FlambdaShortcutSpec.v`, `FlambdaUnusedParamsSpec.v`,
`FlambdaLoopAliasesSpec.v`, `FlambdaLoopifySpec.v`, those of the
second series, `FlambdaParamAliasesSpec.v`, `FlambdaForwardSpec.v`,
`FlambdaInlineTailSpec.v`, `FlambdaLoopLetsSpec.v`, and that of the
third, `FlambdaDeadParamsSpec.v`); the forwarding, in the term
after, of an application of a continuation of no parameters whose
handler only applies another (`FlambdaForwardJumpsSpec.v`); the
removal, in the body of code, of the unused `Let`s of its parameters
(`FlambdaCodeLetsSpec.v`); the
test for inlining a call that gives tupled code a tuple; the demotion
of exception handlers with the rounds that tidy after it
(`demote_and_tidy`); the placing of continuations that the check
makes of each term that it compares (`FlambdaValidateSpec.placed`),
which also keeps scope; the normalisation of the term after and the
first phase of that of the term before. Every one is an equation
that holds of every term. By
the same prover, in the types library (`FlambdaEnvRenameSpec.v`): the
functions of typing environments.

The validation applies one rewrite that makes names, `rename_apart`,
in each round of the second phase of the term before. In the fourth
form, by the second and third provers: each rewrite of a round keeps
scope (`FlambdaKeepsScopeSpec.v`, `FlambdaValidateScopeSpec.v`,
`FlambdaLoopsScopeSpec.v` for the passes for loops,
`FlambdaStaticsScopeSpec.v`); a round, the normalisation of the term
before and that of a term in which something was lifted keep scope
and commute with renaming up to the names that they make; and
`validate_unit` answers the same on a pair of terms and on the pair
renamed (`validate_unit_equivariant_statement`) where the code of the
term before is closed. Nothing is said of a term before whose code
is not closed. What the validation is given that holds continuations
is renamed with the terms: the liftings, and the continuation given
for each loop that it makes of the self tail calls of a function
(`FlambdaLoopifySpec.loopify_unit`, which it applies to the term
before ahead of every rewrite that makes names).

The liftings are made in turn, each followed by a normalisation, and
each holds the two continuations of its unit. The term that a later
lifting is applied to need not mention them. The normalisation before
it commutes with renaming up to the names that it makes, and that
alone does not say that the lifting renamed by the first renaming is
the lifting renamed by the second. So each of those normalisations is
given the continuations of the units of all the liftings
(`FlambdaValidateSpec.unit_continuations`), its rounds make no name
that is one of them (`FlambdaRenameApartSpec.rename_apart_avoiding`,
which is `rename_apart` when it is given none), and it is stated with
`equivariant_up_to_avoiding`
(`normalise_lifted_equivariant_up_to_statement`). While the rounds
were not given those continuations the statement of `validate_unit`
had a second premise, on the terms that the liftings after the first
are applied to; it has none now.

The same holds where the term before is under a second renaming,
which does to its free names, and to the continuations that the
validation is given, what the first does
(`validate_unit_renamed_alike_statement`); the statement above is its
case of one renaming. That is the form for a caller that rewrites the
term before, ahead of the validation, with a rewrite that makes
names. In general: whoever rewrites a term with a rewrite that makes
names, ahead of a function that reads names which its caller holds,
gives the rewrite those names to avoid, and the law of the function
is stated with a second renaming that agrees with the first on them.

The second asking of the validation is such a caller
(`FlambdaValidateKnowingSpec.validate_unit_knowing`): it gives
`validate_unit` the two terms normalised by rounds in front of each
of which aliases are followed by a function that knows what symbols
are bound to. The rounds of the term before make names, and are given
the continuations of the units of the liftings and those given for
the loops to avoid. It answers the same on a pair of terms and on the
pair renamed where the code of the term before is closed
(`validate_unit_knowing_equivariant_statement`), by the statement
with a second renaming. That a unit validated at the second asking is
correct does not rest on this.

Proved by the owner of the meet and the third prover, in the types
library (`FlambdaMeetRenameSpec.v`): the meet of types, of expanded
types at every fuel, and the functions that add to a typing
environment. The meet makes no variable; where it chooses between two
names it is by their binding times, which a renaming keeps. The join
that it is given is a parameter. The first statements are for a join
that commutes with renaming; the join that forgets does, so with it
the meet commutes with no premise. The join that the model has makes
variables and is not such a join: the statements of the second part
of that file are for two joins that a renaming relates, and the
model's join and the same with the source of new names renamed are
two such (above).

Proved by the owners of the passes, each in the file of its pass: the
identities of primitives (`FlambdaIdentitiesSpec.v`), the lifting of
constants (`FlambdaLiftSpec.v`) and out of the code of a function
(`FlambdaLiftFromCodeSpec.v`), the binding of `my_closure`
(`FlambdaMyClosureSpec.v`), the check of ranges (`FlambdaRangeSpec.v`),
the sharing of primitives (`FlambdaCseSpec.v`) and of the
projections of a value slot (`FlambdaShareProjectionsSpec.v`; that
it keeps scope, `FlambdaShareProjectionsScopeSpec.v`), the folding
at known symbols (`FlambdaKnownSymbolsSpec.v`), the removal of unused
value slots (`FlambdaUnusedSlotsSpec.v`), the reading of a value slot
that every set of closures of the unit gives the same symbol or
constant (`FlambdaKnownSlotsSpec.v`), the order of static bindings
(`FlambdaStaticsOrderSpec.v`), the use of the static closures in
sight (`FlambdaKnownClosuresSpec.v`), the move of code to the head of
what it is in (`FlambdaFloatCodeSpec.v`), the binding first of the
code of a unit (`FlambdaHoistCodeSpec.v`) and of its static bindings
that need nothing from around them (`FlambdaHoistStaticsSpec.v`), the
lifting out of the arms of a test (`FlambdaLiftFromArmsSpec.v`), the
inlining, in the body of code, of the calls of the other code of its
group (`FlambdaInlineSiblingsSpec.v`), the unboxing of the parameters
of continuations and of variants (`FlambdaUnboxParamsRenameSpec.v`,
`FlambdaUnboxVariantsRenameSpec.v`, each with the statement that the
pass keeps scope), the merging of the arms of a `Switch` that apply
one continuation (`FlambdaMergeSwitchesSpec.v`), the demotion of the
exception handlers that no call names (`FlambdaDemoteSpec.v`, with
the list of continuations that it is given renamed; that it keeps
scope is `FlambdaDemoteScopeSpec.v`), and the machine with a stack of
exception handlers (`FlambdaTrapSpec.v`). In the fourth form: giving
every binder a name of its own (`FlambdaRenameApartSpec.v`).

Proved by the owners of the model of Simplify, in the types library.
Each is an equation: on the renamed typing environment and the
renamed arguments the function gives the renamed answer. Some take a
function as a parameter and ask that it commutes with renaming. Where
that is asked of a join, it is in the sense of the paragraph on the
meet above: the join that forgets is such a join, and the join of
the model, which makes variables, is not.

- The function that rewrites a term from the types, and its parts
  (`FlambdaSimplifyPassRenamingSpec.v`,
  `FlambdaSimplifyPrimitivesRenamingSpec.v`,
  `FlambdaSimplifyHandlersSpec.v`, `FlambdaSimplifyApplySpec.v`,
  `FlambdaSimplifyStaticsSpec.v`, `FlambdaSimplifyCodeEnvSpec.v`,
  `FlambdaSimplifyValueSlotsSpec.v`), with no premise. From the
  environment that knows nothing it is a rewrite in the form of those
  of the validation.
- The same function with pruning
  (`FlambdaSimplifyPruningRenamingSpec.v`): for a rewrite of a
  `Switch` that commutes with renaming; with the meet that the
  contract is proved of, for a join that does; and with the join that
  forgets, with no premise.
- The rewrites of a `Switch` (`FlambdaSimplifySwitchSpec.v`,
  `FlambdaSimplifySwitchArmsSpec.v`, `FlambdaSimplifySwitchMergeSpec.v`):
  for a meet, and for a rewrite of an `Apply_cont` where one is
  taken, that commute with renaming; with the meet that the contract
  is proved of, for a join that does. The rewrite that merges the
  arms binds variables. It does not make them: they are an argument,
  and are renamed with the term. `FlambdaSimplifySwitchRewriteSpec.v`
  has the same with the variables kept as they are, for a renaming
  that fixes them, which is less. It also has that the rewrite of
  `FlambdaSimplifySwitchArmsSpec.v` (`simplify_switch_arms`, which
  merges nothing) is a rewrite of a `Switch` that commutes with
  renaming, for such a meet and such a rewrite of an `Apply_cont`:
  that is what the function with pruning asks of the rewrite that it
  is given. The rewrite that merges the arms, with its variables kept
  as they are, is not such a rewrite.
- Following aliases in a term with the aliases of the library
  (`FlambdaEnvAliasesFollowSpec.v`; that it keeps scope,
  `FlambdaEnvAliasesFollowScopeSpec.v`), and the sets of aliases
  (`FlambdaEnvAliasesSetSpec.v`), with no premise. What is renamed
  with the term there is what is known of the names where a subterm
  is, not a typing environment; and a function that one of these is
  given (a filter, the binding times of names) is renamed with the
  other arguments.
- The accessors and the creators of types (`FlambdaTypeAccessSpec.v`,
  `FlambdaTypeCreatorsSpec.v`), with no premise.

Owed:

- each pass of the validator that is merged after this was written,
  by its owner or by the third prover, and `validate_unit` again with
  it;
- a rewrite that the validation is to apply owes `keeps_scope` with
  its equation: a round makes names, and `validate_unit` answers the
  same on renamed terms only because every rewrite of a round keeps
  scope;
- statements for five functions of `FlambdaValidateSpec.v` that the
  check applies, whose laws are proved as lemmas of
  `FlambdaValidatorEquivarianceProofs.v` and are not yet stated in a
  `Spec` file (N3): `with_lifting`, `without_slots` and `with_known`,
  each an equation; `lifted_in_turn`, up to the names made, with the
  continuations to avoid; and `with_statics_first`, which reads the
  continuations of the units, for a second renaming that does to
  them what the first does;
- by their owners, the functions on types that have no such statement
  yet.

## 8. What a change to the model owes

- **A new term form.** Its case in `rename_expr` and the functions
  beside it, in the free names of `FlambdaBindersSpec.v`, in the three
  conditions if it binds, in `expr_eqb`, and in the proofs that go by
  cases on terms. If it binds, a row in the table of section 3, a rule
  of `alpha_equivalent`, and a statement that it is a name abstraction.
- **A new place in a term that names** (as a trap action does): it is
  renamed, it is among the free names, and the comparison pairs it as
  it pairs the other occurrences of that sort.
- **A new function on terms.** Section 7.
- **A new place for names.** A sort of its own, an action, and an
  instance of the interface. Tell N1 before putting a variable or a
  continuation into a value.
- **A statement that renames.** The premise that code is closed, or a
  reason why it is not needed.
- **A fresh name.** `fresh_name`, never a count of your own.

## 9. Not done

- The older accounts of free names are not gone. The statements that
  a bound name may be renamed and the rules of `alpha_equivalent` are
  written with the one function, and their older forms are lemmas
  that proofs still use. What is left in the older style is in the
  last table of "Where it stands"; `requests/N1-one-free-names.md`
  says, statement by statement, what was replaced, what is left and
  why, and how to go back.
- The functions listed as owed in section 7.

## 10. The compiler's side

Nothing in the compiler was changed. What follows is what was found by
reading `nominal/` and its users against the laws of section 6; the
labels are those of the discrepancies with the compiler.

Where the code follows the discipline: no caller outside
`name_abstraction.ml` reads an abstraction without `pattern_match`
(`descr` is not exported; `pattern_match_for_printing` is used by the
printers only); `Compare` opens both sides at one fresh name and then
compares names by equality. The canonical alias is chosen by binding
time, and CSE sorts by `stable_compare_simples`, which compares binding
times; but both fall back on the order of names where binding times do
not decide: two variables of one binding time are ordered by their
stamps, and among symbols, none of which is earlier than another, the
alias chosen is the least in the order of the map (N1-7).

What it would take for the compiler to obey the same laws:

1. **Make the precondition of a binder structural.** Check distinct
   parameters in `Bound_parameters.create` always, as
   `Bound_continuations.create` does, and the two continuations of
   `Bound_for_function`. Both eliminators then agree (N1-3).
2. **Make the pair eliminator total.** `pattern_match_pair` returns an
   error value when the two bindables differ in shape, for every
   bindable, and no caller tests first (N1-2).
3. **Check closed code against the body** when invariant checks are
   on: `Code0.create` compares the claim with the free names of the
   abstraction (N1-4).
4. **Put the remaining binders behind `Name_abstraction`**: the
   existential variables of an environment extension, and the
   variables a level defines where a level is cut or joined. Freshness
   for the environment then comes from `pattern_match` and not from
   the caller (N1-6).
5. **Take static patterns out of `Name_abstraction`.** They are not
   abstractions: they are never renamed. A `Let` of static constants as
   a constructor of its own makes `free_names` and `apply_renaming`
   agree (N1-5).
6. **Two types for the two things `Renaming.t` is**: permutations,
   which form a group and are what binders use; and import maps, which
   are injections that also prune value slots (N1-8).
7. **No term structure from the order of names.** Where an order is
   needed, use binding time or position. A rule that is easy to state
   and to search for: never fold over a `Variable.Map` or a
   `Variable.Set` to build a list that ends up in a term (N1-7).
8. **A test of equivariance.** Run Simplify on a unit and on the same
   unit with its names created in another order, and compare the two
   results up to bound names. A pass that depends on names shows as a
   difference; it needs no model. Run once by hand, on 81 units with
   unused bindings put first: no dependence on the order of a set or a
   map of names was seen; the names of lifted symbols contain the
   stamp of a variable, so symbols too have to be compared up to
   renaming (N1-7).
9. **Repair `compare.ml`**: the maps of slots (N1-1) and the missing
   case for primitives of four arguments, without which a term is
   judged different from itself (N1-9). Or replace its core by the
   comparison of section 5. That one is proved to be an equivalence
   relation for the terms of the model only: it would need the
   pairing of slots, symbols and code ids, and every construct and
   annotation of the compiler's terms that the model has not got, and
   what is proved here does not carry over to those without proof.
