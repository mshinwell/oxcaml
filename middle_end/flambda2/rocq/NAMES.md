# Names in the model of Flambda 2

How the model treats bound names, what is proved about them, and what a
change to the model owes. Owner: N1. The compiler's side is
`middle_end/flambda2/nominal/`.

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
| `FlambdaAlphaSpec.v` | The action is that of a group; the free names and the three conditions are equivariant; `alpha_equivalent`, by its generators, is equivariant, keeps the free names and is sound for the semantics |
| `FlambdaCompareAlphaSpec.v` | The comparison `expr_eqb` is an equivalence relation and contains `alpha_equivalent` |
| `FlambdaEquivarianceSpec.v` | The action on states; a step, a run and a behaviour commute with it; two rewrites commute with it |
| `FlambdaNameAbstractionSpec.v` | The interface of `nominal/`: things that contain names, bindable names, name abstractions, `pattern_match`, with their laws; `fresh_name` |
| `FlambdaNominalInstancesSpec.v` | The terms as instances of the interface; each binder as a name abstraction |
| `FlambdaFreeNamesSpec.v` | The older accounts of free names agree with the one function where code is closed |

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
  all environments.
- `expr_eqb`: the comparison that the validator runs, by recursion on
  the two terms with a map of paired names. It is sound, it is an
  equivalence relation, and it accepts every two alpha-equivalent
  terms.

The comparison is the primary notion (it is a function and it is what
runs); the rules of `alpha_equivalent` are facts about it. The converse
(what the comparison accepts is alpha-equivalent) can hold only of
terms with distinct binders and closed code:
`expr_eqb_repeated_parameter_statement` is the term that shows why. It
is being proved for those terms.

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
types library (types are to follow). Each binder of section 3 except the recursive group
is shown to be a name abstraction: equal abstractions give
alpha-equivalent terms. The laws of abstractions, and that opening two
equal abstractions at the same names gives equal scopes
(`pattern_match_pair_statement`), then hold of them with no further
proof.

A quantifier "for all but finitely many names" is being added as a
derived view of equal abstractions, for one bound name and for a list
of distinct bound names. The definition by permutations stays.

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
`names_in_scope`; `alpha_equivalent`; `fold_constants`; `inline_calls`.

Owed, with the owner of the function: the other rewrites of
`FlambdaNormaliseSpec.v`, `FlambdaUnusedStaticsSpec.v`,
`FlambdaUnusedContsSpec.v` and `FlambdaBlockLoadSpec.v`, and
`validate_unit` (the validator's owners, with N1); that `expr_eqb` is
unchanged when both terms and both maps are renamed (N1); the checks of
`FlambdaWellFormedSpec.v` (the integrator, with N1).

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

- The converse of section 5.
- The recursive group as a name abstraction: its scope is the handlers
  and the body together.
- The older accounts of free names (`var_free_in_expr`,
  `cont_free_in_expr`, `FlambdaWellFormedSpec.free_continuations`,
  `FlambdaNormaliseSpec.expr_in_scope`) are still what many statements
  are written with. `FlambdaFreeNamesSpec.v` lets each be restated by
  the one function; that is to be done a statement at a time, and the
  file then goes.
- States are not an instance of the interface: their equivariance is
  stated directly.
- The functions listed as owed in section 7.
