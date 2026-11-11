# C4, the heap: what the prototype costs on the integration branch

The prototype was written on the integration branch at 0a2933e7c9. It is
rebased here on 1160b780f0, after C1's law that no primitive has a value
on a symbol bound to nothing and its numbers in range, C3's sets of
closures and valid values, C2's kinds on terms, C0's well-formedness,
N1's names, V2's normalisations, and the types, T1's to T6's. This note
says what applying its edits to the model costs each owner there, and
what changed in the prototype's own two files. Paths are in
`middle_end/flambda2/` unless they say otherwise. The counts are on
1160b780f0. Of what came to the integration branch after C3's epoch,
three files needed an edit (two of C2's and one of T6's, below); the
rest did not (T2's typing environments, T3's aliases, T5's joins, N1's
renamings, N2's binders, more of C1's laws).

## The edits to existing files, by owner

The prototype's edits are: a value `Value_location` and the types
`location`, `cell` and `heap` in `FlambdaValueSpec.v`; the primitives of
the heap under one new constructor `Heap` of `prim` in
`FlambdaPrimitiveModel.v`; and the kind of their results in
`FlambdaPrimitiveSpec.v`. Everything else in the table is a repair that
they force: a case where a match or a proof by cases had none for the
new constructor. "+a -b" counts lines added and removed.

| File | Owner | Lines | What changes |
|------|-------|-------|--------------|
| `rocq/FlambdaValueSpec.v` | C0 | +29 -1 | `location`; `Value_location` in `value`; `cell`, `heap`, `empty_heap`, `cell_of`. No observation changes: each has a wildcard, so a location is no closure, block, boxed number or string, and is not allocated. |
| `rocq/FlambdaPrimitiveModel.v` | C1 | +36 -1 | `cell_mutability`, `init_or_assign`, `equality_comparison`, `heap_primitive`, and `Heap` in `prim`. |
| `rocq/FlambdaPrimitiveSpec.v` | C1 (the signature of `eval_prim` and the laws are C0's; neither changes) | +31 -1 | `result_kind_of_heap_primitive`, and a case of `prim_result_kind`. `access_in_range` and `heap_primitive_in_range`, and a case of `prim_in_range`: a primitive of the heap carries the numbers of the `Make_block` or `Block_load` that it stands for. `value_in_range`: a location is in range (it holds no number). `eval_prim` has a wildcard already: it has no value on `Heap _`, and treats a location as any value that no observation reads. |
| `rocq/FlambdaPrimitiveProofs.v` | C1 | +8 -6 | `eval_prim_arity`: a fourth branch (`Heap`: no value). `eval_prim_static_values`, `eval_prim_statics_extend`: a fourth pattern in the destruct on `prim`. `eval_is_null_statics_extend`: a seventh pattern in the destruct on `value`. |
| `rocq/FlambdaSemanticsProofs.v` | C0 | +3 -3 | `closure_in_set_of`, `closure_in_set_slot`, `project_function_slot_defined`: one more name in the pattern of the destruct on `value`; the existing catch-all branches take it. |
| `rocq/FlambdaClosuresSpec.v` | C3 | +2 -1 | `value_valid`: a location is valid (there is nothing in it). |
| `rocq/FlambdaClosuresProofs.v` | C3 | +4 -4 | Four destructs on `value` (among them `closure_in_set_valid`): one more name in the pattern; the existing catch-all branches take it. |
| `rocq/FlambdaBlockLoadProofs.v` | V2 | +2 -2 | `block_made_spec`, `unary_applied_spec`: a fourth pattern in the destruct on `prim`. |
| `rocq/FlambdaUnusedStaticsSpec.v` | V1 (unassigned) | +1 | `value_avoids`: a location avoids every name. |
| `rocq/FlambdaUnusedStaticsProofs.v` | V1 (unassigned) | +6 -3 | `closure_of_erased`, `closure_in_set_erased`, `project_function_slot_erased`: one more name in the pattern, and one more branch, that of a boxed number (no closure, nothing erased). |
| `types/rocq/FlambdaTypeMeaningBoolSpec.v` | T1 | +1 | `value_eqb`: two locations are equal when they are the same location. Without it `value_eqb_decides_equality_statement` would be false: a location would not be equal to itself. |
| `types/rocq/FlambdaTypeMeaningBoolProofs.v` | T1 | +11 -7 | `value_induction`: a hypothesis and a case for a location. `value_eqb_eq`: a branch for two locations. Three destructs on `value` (`is_poison_b_eq`, `relation_holds_b_eq`, `naked_numbers_satisfied_b_eq`): one more pattern. |
| `types/rocq/FlambdaTypeMeaningProofs.v` | T1 | +13 -13 | Ten destructs on `value`: one more pattern, and one more empty branch where the destruct lists the branches. |
| `rocq/FlambdaWellKindedSpec.v` | C2 | +3 -1 | `value_well_kinded`: a location is well kinded (there is nothing in it; the fields of its cell are for the heap's own condition, when the heap is in `state`). |
| `rocq/FlambdaWellKindedProofs.v` | C2 | +3 -3 | Three destructs on `value`: one more name in the pattern; the existing catch-all branches take it. |
| `types/rocq/FlambdaProversProofs.v` | T6 | +3 -3 | `tagged_immediate_of_value`, `eval_is_null_cases`: one more pattern in three destructs on `value`. |
| `rocq/Makefile` | C0 | +2 | `FlambdaHeapProofs.v` and `FlambdaHeapSpec.v` in `FLAMBDA2` (the commit of lines for the shared lists). |
| `tests/tools/flsemantics.ml` | C0 (the tool stays C0's for now) | +6 | An observation `Location`, printed `<location n>`; a case of `print_prim` for `Heap`, which the converter never makes. No expected output changes. |

Nothing else matches on `value` or `prim` without a wildcard. T1's
meaning of types needed no case beyond `value_eqb`: it reads a value
through the observations and its kind, so a location satisfies what any
value of kind `Value` that is not null satisfies (an unknown head), and
no shape of variant, block, boxed number, closure or string.

## Statements of existing `Spec` files whose text changed

None.

## What changed in `FlambdaHeapSpec.v`

The machine (`heap_step`, `exec_named`, `heap_call_function`,
`heap_apply_cont_value`) is unchanged: `step`, `call_function` and
`apply_cont_value` are as they were on the old base, and the new forms
of `named` reach the heap machine through `eval_named`, which
`exec_named` calls on everything that is not a primitive.
`heap_step_agrees` is proved as before. On C2's epoch the machine
follows `step` again: `heap_step` ignores the kind of a `Let`,
`heap_apply_cont_value` the metadata of a handler, and
`heap_call_function` takes the two arities of the call and is undefined
unless the call agrees with the code called, as `call_function` is.
Two related lists of arguments have the same kinds, so the relation on
states is kept. Each statement about a `Let` has the kind of its
variable as one more variable. `exec_prim` is unchanged: its
test `forallb (argument_bound statics h) vs` and `exec_bound_prim` are
as they were, and `eval_prim` takes the same arguments.
`equality_comparison` and `Phys_equal` are not in the integration
branch's primitives, so the prototype's are kept, under `Heap`.

Definitions:

- `named_at_most_generative_effects`, `named_has_no_effects`: the list
  of what is not a primitive gains `Closure_of_set`,
  `Project_value_slot_from` and `Project_function_slot` (true, as for
  everything that is not a primitive).
- `locations_of_value`: a `Value_closure_of_set` has the locations of
  its value slots, as a `Value_closure` has.
- `values_of_static`: a `Static_closure_of_set` holds the values of its
  value slots, as a `Static_closure` does.
- `value_step`, the rule for closures. Old:

      Step_closure v v' code slots slots' :
        closure_of statics v = Some (code, slots) ->
        closure_of statics' v' = Some (code, slots') ->
        map fst slots = map fst slots' ->
        Forall2 R (map snd slots) (map snd slots') ->
        value_step R v v'

  New:

      Step_closure v v' slot function_decls slots slots' :
        closure_in_set statics v = Some (slot, function_decls, slots) ->
        closure_in_set statics' v' = Some (slot, function_decls, slots') ->
        map fst slots = map fst slots' ->
        Forall2 R (map snd slots) (map snd slots') ->
        (set_bound statics v ∧ set_bound statics' v')
        ∨ ((∀ move_to w,
             project_function_slot statics slot move_to v = Some w ->
             ∃ w', project_function_slot statics' slot move_to v' = Some w'
                   ∧ R w w')
           ∧ (∀ move_to,
               project_function_slot statics slot move_to v = None ->
               project_function_slot statics' slot move_to v' = None)) ->
        value_step R v v'

  The first four premises are the rule asked for: closures at the same
  function slot of sets with the same function declarations, whose
  value slots have the same names and related values. The fifth is
  new; see below. `set_bound statics v` says that the set of `v` is
  known in full: `v` was made by a `Let`, or is a symbol bound to the
  closure of one function, or is a symbol of a static set that names
  a symbol for each of its functions, each bound to the closure of the
  set at its slot (`FlambdaClosuresSpec.static_set_bound`).
- `value_step` gains a tenth rule, `Step_same_closure_of_set`: a
  `Value_closure_of_set` at a function slot that its set has not got is
  itself. No observation reads it, as none reads the boxed number of
  `Step_same_boxed_number`; without the rule a closed outcome that holds
  one would not be related to itself.

Statements: no text changed in the adaptation. The 25 statements that
the prototype proved on the old base are proved with the same text, and
so are the three that C4 proved since (`heap_step_closed_statement`,
`exchange_lets_statement`, `cse_adjacent_statement`), which needed only
extra cases. Since the rebase `lift_block` is proved, with three
statements for the relation that it needs (`requests/C4-heap.md`,
section 4.2), and its statement lost a premise that the proof does not
use; `lift_closure`, `lift_closure_of_set`, `related_projections` and
`outcome_equivalent_symmetric` are stated and proved. Thirty-six
statements are proved, and there is no conjecture.

## What surprised me

- A projection of a function slot breaks a relation of closures by
  their contents. From a symbol, `project_function_slot` gives the
  symbol that its static set names for the slot, whatever that symbol
  is bound to (the CR before `project_function_slot`, decision D4); from
  a closure made by a `Let` it gives the closure of the same set at the
  slot. So two closures with the same slot, the same declarations and
  related value slots can have unrelated closures at another slot, and
  the machine, which runs `Project_function_slot`, would not respect
  the relation that the four premises alone define. Hence the fifth
  premise: the closures at the other slots are related. For two sets
  that are known in full this follows from the first four, and nothing
  more is asked; a closure made by a `Let` is then related to a symbol
  of a static set with the same functions and related value slots,
  which is what lifting a set of closures needs. For a static set of
  which nothing is known, the projections themselves are asked to be
  related, from both closures or from neither. A first form of the
  premise compared the two projections by whether they were symbols.
  It was wrong twice over: it related two symbols of a static set whose
  other symbols were bound to different things, and it did not relate a
  closure to its lifted symbol.
- The prototype had not met C1's law: `Opaque_identity` and `Make_block`
  now test `bound_if_symbol`. Two lemmas of the proofs cover it: a
  value related to one that passes the test passes it.
- `Is_int` and `Is_null` of `eval_prim` have no value on a location,
  which `is_allocated` does not count as allocated, as on a symbol bound
  to nothing. The heap machine never asks: `exec_bound_prim` reads a
  unary primitive of a location from its cell (`exec_unary_on_cell`).
  T1's relation `Is_null` answers 0 of a location, as of any value of
  kind `Value` that is not null. The two do not meet today; they will
  when the heap is in `state` and `eval_prim` is asked of a location.
- `FlambdaSemanticsSpec.state_values_all` says where a state holds
  values, and that a new place for them, such as a heap, is added
  there. The prototype's machine is a copy beside `state`, so it does
  not add its heap there; its own invariant (`state_closed`) walks the
  heap and the static environment. Putting the heap in `state` adds the
  cells to `state_values_all`.
- The cost to the other owners is small: eighteen files, most of them
  a name in a pattern. The work is in the prototype's own proofs, which
  gain the lemmas on closures of a set (a closure of a set is a closure;
  what a closure that is not a symbol projects; a projection does not
  change as the static environment grows) and a case in each proof by
  cases on the relation.
