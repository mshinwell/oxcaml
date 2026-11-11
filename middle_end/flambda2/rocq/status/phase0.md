# Phase 0: status

Branch `flambda2-rocq/phase0`, from `flambda2-rocq-semantics` at
2c7ad8346a. The task is section 4 of `PARALLEL-PLAN.md`: the eight items
that make the repository safe for parallel work.

## Done

- Item 2, the state as a record. `state` is a `Record` with the
  projections `state_expr`, `state_vars`, `state_conts` and
  `state_statics`; no proof destructs a state by position
  (`FlambdaSemanticsProofs.state_eta` and `simpl_state` are what to use).

## In progress

- Item 1, the step lemmas.

## To do

- Item 3, finite maps.
- Item 4, one expected file per example.
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
