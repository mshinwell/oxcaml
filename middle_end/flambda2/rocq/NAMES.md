# Names in the model of Flambda 2

How the model treats bound names, what is proved about them, and what a
change to the model owes. Owner: N1. The compiler's side is
`middle_end/flambda2/nominal/`; section 10 says what it would take
for it to obey the same laws.

## 1. The names

Two sorts of name are bound by terms and moved by renamings: variables
and continuations. Symbols, code ids, value slots and function slots
are global: no renaming moves one. A run-time value holds no variable
and no continuation (a closure holds code ids and values), so nothing
is renamed in a value. If a new place comes to hold names (the
locations of a heap), it is a sort of its own.

Names are compared by equality only. The one function that looks at
the number of a name is `fresh_name` (`FlambdaNameAbstractionSpec.v`),
which gives a name outside a list of names.

## 2. Where things are

| File | What it has |
|------|-------------|
| `FlambdaBindersSpec.v` | What each binder binds and where; the free variables and free continuations of a term, as one function for each (they go into code); the three conditions on binders: `names_in_scope`, `binders_distinct`, `code_closed` |
| `FlambdaScopeSpec.v` | `state_in_scope`: what a run keeps of scope; a state in scope reads no variable without a value and leaves only by a continuation it was given |
| `FlambdaNominalSpec.v` | Permutations and renamings; the action on terms, `rename_expr`, code included; the free names as relations; that each binder may be renamed |
| `FlambdaAlphaSpec.v` | The action is that of a group; the free names and the three conditions are equivariant; `alpha_equivalent`, by its generators, is equivariant, keeps the free names and the three conditions, and is sound for the semantics |
| `FlambdaCompareAlphaSpec.v` | The comparison `expr_eqb` is an equivalence relation, contains `alpha_equivalent` and does not depend on the names; two pairs of terms that it accepts outside well-formed terms |
| `FlambdaEquivarianceSpec.v` | The action on states; a step, a run and a behaviour commute with it; two rewrites commute with it |
| `FlambdaNameAbstractionSpec.v` | The interface of `nominal/`: things that contain names, bindable names, name abstractions, `pattern_match`, with their laws; `fresh_name` |
| `FlambdaNominalInstancesSpec.v` | The terms as instances of the interface; each binder as a name abstraction |
| `FlambdaFreeNamesSpec.v` | The older accounts of free names agree with the one function where code is closed, and what is free by them is among the free names on every term |
| `FlambdaCanonicalFreeNamesSpec.v` | The statements about binders, and the rules of `alpha_equivalent`, written with the one function for the free names |
| `FlambdaStateSupportSpec.v` | Every expression and every state has a finite support: with the action, the states are a nominal set |

In the types library, `FlambdaEnvAliasesRenamingSpec.v` has the action
on the aliases, with the same laws, as an instance of the interface.
The action on types comes with the files of the types.

## 3. The binders

| Binder | Binds | In scope in |
|--------|-------|-------------|
| `Let x d body` | `x` | `body` |
| `Handler params handler` | `params` | `handler` |
| `Let_cont_non_recursive k h body` | `k` | `body` |
| `Let_cont_recursive handlers body` | the continuations of `handlers` | `body` and every handler |
| `Code params my_closure ret exn body` | `params`, `my_closure`, `ret`, `exn` | `body` |

A `Let_static` binds no variable and no continuation. Code is closed:
its body has no free name but what the code binds (decision D31).

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
closures, the code of the static environment, states, the result of a
step and behaviours. It renames bound and free occurrences alike, so it
never captures. The laws of a group hold of the action.

It is the action of the compiler's renamings that are permutations
within one unit (what the freshening of a binder uses). A renaming with
an import map is another operation and is not modelled (discrepancy
N1-8).

Execution commutes with renaming, with no condition:
`step (rename_state r s) = rename_result r (step s)`, and the same of
`run` and of `behaves`. So a rewrite that is correct with one choice of
names is correct with every other.

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
well-formedness admits. It is proved, by a second prover, in a series
that follows this one; with it the comparison decides
alpha-equivalence on those terms.

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
the code in what is renamed is closed. The relations of free names do
not look into code, and the comparison treats code as closed, so
without the premise the statements are false.

## 6. The interface

`FlambdaNameAbstractionSpec.v` is the interface of `nominal/` with the
laws the compiler leaves unsaid, for one sort of name at a time: a
type whose values contain names has an action, free names and an
equality (`=` where there is no binder, alpha-equivalence for
expressions); a name abstraction is a pair of bound names and a scope,
equal to another when each can be opened, by a permutation that fixes
its free names, to the same bound names and equal scopes.

Instances: `simple`, `named`, static constants and environments;
expressions whose code is closed, for each sort; the aliases, in the
types library (types are to follow). Each binder of section 3 except
the recursive group is shown to be a name abstraction: equal
abstractions give alpha-equivalent terms. The laws of abstractions, and
that opening two equal abstractions at the same names gives equal
scopes (`pattern_match_pair_statement`), then hold of them with no
further proof.

The quantifier "for all but finitely many names" is a derived view of
equal abstractions (`FlambdaFreshQuantifierSpec.v`,
`FlambdaFreshAbstractionSpec.v`), for one bound name and for a list of
distinct bound names. The definition by permutations stays. Its use on
the binders of terms follows this series.

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

Prove it by one recursion over expressions, handlers, bindings and
code. A function whose answer depends on the order or the number of a
name is a finding: record a discrepancy.

Proved: the machine (`step`, `run`, `behaves`); the free names, as
relations and as functions; `code_closed`, `binders_distinct`,
`names_in_scope`; `alpha_equivalent`; `expr_eqb`; `fold_constants`;
`inline_calls`.

Owed, and being proved by a third prover in a series of its own: the
other rewrites of `FlambdaNormaliseSpec.v`, `FlambdaUnusedStaticsSpec.v`,
`FlambdaUnusedContsSpec.v`, `FlambdaBlockLoadSpec.v` and
`FlambdaUnboxSpec.v`, the checks of `FlambdaWellFormedSpec.v`, and
`validate_unit`. Owed by their owners: the lifting of constants, the
ranges, and the functions on types.

## 8. What a change to the model owes

- **A new term form.** Its case in `rename_expr` and the functions
  beside it, in the free names of `FlambdaBindersSpec.v`, in the three
  conditions if it binds, in `expr_eqb`, and in the proofs that go by
  cases on terms. If it binds, a row in the table of section 3, a rule
  of `alpha_equivalent`, and a statement that it is a name abstraction.
- **A new function on terms.** Section 7.
- **A new place for names.** A sort of its own, an action, and an
  instance of the interface. Tell N1 before putting a variable or a
  continuation into a value.
- **A statement that renames.** The premise that code is closed, or a
  reason why it is not needed.
- **A fresh name.** `fresh_name`, never a count of your own.

## 9. Not done

- The recursive group as a name abstraction: its scope is the handlers
  and the body together. In progress.
- The older accounts of free names (`var_free_in_expr`,
  `cont_free_in_expr`, `FlambdaWellFormedSpec.free_continuations`,
  `FlambdaNormaliseSpec.expr_in_scope`) are still what many statements
  are written with. `FlambdaCanonicalFreeNamesSpec.v` has the
  statements about binders and the rules of `alpha_equivalent` in the
  form they take with the one function, each proved from the older
  one; the older ones and the relations are still there. Whether they
  are replaced, and the bridges of `FlambdaFreeNamesSpec.v` deleted, is
  for the human to say: the status of this stream lists what would
  change, owner by owner.
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
