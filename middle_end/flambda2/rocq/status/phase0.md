# Phase 0: status

Branch `flambda2-rocq/phase0`, from `flambda2-rocq-semantics` at
2c7ad8346a. The task is section 4 of `PARALLEL-PLAN.md`: the eight items
that make the repository safe for parallel work.

## Done

- Item 1, the step lemmas. `FlambdaSemanticsProofs.v` has one equation
  for each construct (`step_let`, ..., `step_invalid`), `step` is opaque
  after them, and every proof goes through them. Checked by one build in
  which `step` was a `Parameter` with only those eight equations: all the
  other proofs built unchanged.
- Item 2, the state as a record. `state` is a `Record` with the
  projections `state_expr`, `state_vars`, `state_conts` and
  `state_statics`; no proof destructs a state by position
  (`FlambdaSemanticsProofs.state_eta` and `simpl_state` are what to use).
- Item 3, finite maps. `FlambdaMapSpec.v` and `FlambdaMapProofs.v`:
  association lists keyed by `positive`, first binding wins, and lists of
  names as sets. `lookup`, `among`, `all_among`, `without` and `distinct`
  moved there; `is_bound`, `unbind`, `map_values`, `domain`, `tabulate`,
  `compact`, `filter_bindings`, `merge`, `union_with`, `inter_with`,
  `inter` and `dedup` are new, each with a statement of what it does to
  `lookup` or `among`. The lemmas that were scattered (`lookup_app`,
  `lookup_fresh`, `among_In`, `distinct_NoDup`, ...) are in
  `FlambdaMapProofs.v`. The header of the Spec says why lists and what
  was rejected.

## In progress

- Item 4, one expected file per example.

## To do

- Item 5, the lists of `rocq/Makefile` and of `FlambdaExtract.v`.
- Item 6, the rule for the extracted files.
- Item 7, the trust ledger.
- Item 8, the ownership table.

## Blocked

Nothing.

## Open questions

None yet.

## Spec text changed

Each change keeps the meaning. A reviewer reads the `Spec` diff against
this list.

- `FlambdaSemanticsSpec.state`: an `Inductive` with the one constructor
  `State (e : expr) (vars : env) (conts : cont_env) (statics : static_env)`
  became a `Record` with the same constructor and the fields
  `state_expr`, `state_vars`, `state_conts`, `state_statics`, in that
  order. `step` and every statement that builds a state with `State` are
  as they were.
- `FlambdaWellFormedSpec.statics_of` is gone: it was the projection
  `state_statics`, written as a match. `step_extends_statics_statement`
  and `run_extends_statics_statement` say `state_statics s` where they
  said `statics_of s`.
- `FlambdaWellFormedSpec.static_fault` matches on `state_expr s` and
  reads `state_vars s` and `state_statics s`, where it matched on
  `State e vars _ statics`. The cases and what each answers are the same.
- `lookup` moved, as it was, from `FlambdaSemanticsSpec.v` to
  `FlambdaMapSpec.v`; `among`, `all_among`, `without` and `distinct`
  moved, as they were, from `FlambdaWellFormedSpec.v` to
  `FlambdaMapSpec.v`.
- `FlambdaNormaliseSpec.name_in` is gone: it was the same function as
  `among` (`existsb (Pos.eqb name) names`). `simple_in_scope`,
  `apply_cont_in_scope`, `expr_in_scope` and `var_free_in_handler_b` of
  `FlambdaNormaliseSpec.v`, and `symbol_kept` and `code_kept` of
  `FlambdaUnusedStaticsSpec.v`, say `among` where they said `name_in`.
- New, in `FlambdaMapSpec.v`: the definitions listed under item 3 and
  sixteen statements about them. No statement that existed mentions them.
