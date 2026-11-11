# N3, on the side of the types: status

Owner: N3, on `flambda2-rocq/N3-types`. The status of the validator's
side of the same stream is `status/N3.md`. N1 leads the work on names.

This branch is on the integration branch.

The task: what the work on names asks of everything that holds names,
for the typing environment: its renaming, its free names, and that its
functions commute with renaming. The owner of the environment had none
of it and left it to this stream.

Files (new, mine): `middle_end/flambda2/types/rocq/FlambdaEnvRenameSpec.v`
and `FlambdaEnvRenameProofs.v`. No file of another owner is edited.

## Done

Seventy-nine statements.

- **The action** on a level, on what the environment knows of its
  names, and on an environment (`rename_level`, `rename_cached_level`,
  `rename_typing_env`); the free variables; the laws (identity,
  composition, inverse, two renamings that agree on the free variables,
  one that fixes them, the free variables of what is renamed); the two
  instances of the interface for things that contain names, with its
  laws (fourteen).
- **The functions of a level** and of what the environment knows of its
  names (sixteen): `defined_variables`, `find_kind`, `is_empty`,
  `add_definition`, `add_or_replace_equation`, `concat`,
  `as_extension_without_bindings`, `variables_in_order`,
  `fold_on_defined_vars`, and those of `Cached_level`.
- **What an environment is asked** (eighteen): `find` and the two
  functions beside it, `binding_time_and_mode`, `mem`,
  `binding_time_resolver`, `alias_is_bound_strictly_earlier`,
  `get_canonical_simple_exn` and the two beside it,
  `type_simple_in_term_exn`.
- **What is done to an environment** (fifteen): `add_variable_definition`,
  `add_definition`, `add_definitions_of_params`, the definitions of
  symbols, `replace_equation`, `aliases_add`, `add_alias`, `cut`,
  `cut_as_extension`, and the changes of scope.
- **What satisfies a renamed environment** (seven): the renamed
  valuation satisfies the renamed environment exactly when the
  valuation satisfies the environment, in each sense of
  `FlambdaTypingEnvSpec.v` (`typing_env_satisfied_but` with the exempt
  names renamed, `typing_env_satisfied_strictly`,
  `typing_env_satisfied`, `env_satisfies`, `env_satisfies_strictly`),
  with the same of `exempt_by_poison` and `in_scope_in_terms`. The
  owner of the environment asked for these.
- **The invariant and the kinds of a renamed environment** (nine): the
  test of the invariant answers the same of the renamed environment
  (`typing_env_well_formed`); `levels_agree`, `typing_env_invariant`,
  `types_well_formed` and `typing_env_kinded` hold of the renamed
  environment exactly when they hold of the environment, and the test
  of the types being well formed (`types_well_formed_b`) answers the
  same of the two (the owner of the pass that rewrites primitives from
  the types asked for it: the pass runs the test); a renamed
  `Simple` is of a kind in the renamed environment exactly when the
  `Simple` is in the environment (`simple_of_kind`); the same of the
  second condition on kinds, of the names that have an equation in an
  extension inside a type (`type_equations_kinded`,
  `types_equations_kinded`). The owner of the environment asked for
  these too. Each condition of the invariant is
  shown to be kept by a renaming, one lemma a condition (seventeen
  conditions, with the one that a variable that has a type is defined
  by a level); the converse is the same fact of the inverse renaming.

Each statement about a function is an equation with no premise on the
environment; one has a premise on an argument that is a function
(`fold_on_defined_vars`).

## To do

- The functions added to the environment since (the operations of the
  meet on an environment, the extensions).

## Decided overnight

1. **The free variables of an environment are every variable written
   in it, and its equality is that of Rocq.** Options: (a) that; (b)
   the variables that its levels define are bound, and environments
   are equal up to their renaming. Chosen: (a). An environment is the
   context of a term; the variables it defines are free in the term,
   and it records the identity of those that no term may mention too
   (type-only variables, variables out of scope). With (b) the
   functions that look a name up (`find`, `mem`, the canonical element
   of a name) are not functions of the class of an environment: they
   do not descend to the quotient as they are. Where a level is cut
   out and its variables made anew (the levels that a join is given),
   the level with what it scopes over is a name abstraction: that is
   for the stream of the join, with the interface. Cost of changing:
   the two instances and the header.
2. **The files are named `FlambdaEnvRename*`**, not
   `FlambdaTypesEquivariance*` as first suggested: `FlambdaTypes*` and
   `FlambdaTypingEnv*` are patterns of other owners in `OWNERS.md`.
3. **The base was at first the series with the renaming of types**,
   not the integration tip of that time: the action on an environment
   needs that renaming. That series is merged, and the branch is on
   the integration branch.
4. **Statements are written with the renaming of a name of the types'
   file** (`FlambdaTypeRenameSpec.rename_name`). The file of the
   aliases had the same function under the same name; its owner has
   removed it, and there is one renaming of names. The same of
   `variables_renaming`, which the types' file of instances and N1's
   file of instances both define: N1's stays.

## Found

- Nothing that is not equivariant. No function of the environment makes
  a name or goes by the order of names: the order of binding is read
  from binding times, which a name keeps, and a tie is settled by the
  order of a list of the model.
- The functions of the aliases take the environment's map from names to
  types and read only its binding times; their statements under
  renaming keep the types of that map as they are. The action here
  renames those types, so the proofs here first show that the functions
  of the aliases do not read them (`add_alike`,
  `get_canonical_element_exn_alike` in the `Proofs` file). The owner of
  the aliases has since stated them in its own file, with the proofs
  from here, and the proofs here use its statements.
- The check of claims (`make claims`) reads a statement only where
  `Definition ..._statement : Prop` is on one line. A statement whose
  name is long enough for `: Prop` to go to the next line is not
  checked, and nothing says so. Two statements here were so; they are
  on one line now. The integrator is told.

## Review

The reviewer of the types read the seventy statements and the
definitions and asked for two repairs of the header (it cited a file
that is not in the tree of this base; it said that the variables of
the levels are those in scope in the term, which leaves out the
type-only variables and those out of scope) and one of this file (the
reason against binding the variables of the levels was put too
broadly). They are folded into the commits they belong to. The owner
of the environment read the statements against its definitions and
had no objection.

The reviewer then read all seventy-eight statements of that time and
signed them, and asked for two repairs of comments (the file cited for
`variables_renaming`; what the header says the model has of the
compiler's two structures with a renaming). They are folded into the
commits they belong to. The statement about `types_well_formed_b` was
added after that and is to be read.

## Obstacles

None.
