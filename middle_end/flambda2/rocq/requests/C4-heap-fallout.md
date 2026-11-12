# C4, the heap: what the prototype costs on the integration branch

The prototype was written on the integration branch at 0a2933e7c9. It
was merged on fcd6e9c15c, after C1's law that no primitive has a value
on a symbol bound to nothing and its numbers in range, C3's sets of
closures and valid values, C2's kinds on terms, C5's exceptions, P1's
primitives, V3's lifting, C0's well-formedness, N1's names, V2's
normalisations, and the types, T1's to T6's. This note says what
applying its edits to the model cost each owner there, and what
changed in the prototype's own two files. Paths are in
`middle_end/flambda2/` unless they say otherwise. The counts are on
fcd6e9c15c. Of what came to the integration branch after C3's epoch,
eleven files needed an edit (two of C2's, one of T6's, one of N3's,
one of P1's, three of V3's, one of V2's, one of T7's and one more
function of C3's, below); the rest did not (T2's typing environments,
T3's aliases, T4's meet, T5's joins, N1's renamings, N2's binders,
N3's rewrites up to renaming, C5's exceptions and its second machine,
more of C1's laws, V3's known symbols).

## The edits to existing files, by owner

The prototype's edits are: a value `Value_location` and the types
`location`, `cell` and `heap` in `FlambdaValueSpec.v`; the two
primitives that only the heap has, under one new constructor `Heap` of
`prim` in `FlambdaPrimitiveModel.v`; and the kind of their results and
the test of their numbers in `FlambdaPrimitiveSpec.v`. Everything else
in the table is a repair that they force: a case where a match or a
proof by cases had none for the new constructor. "+a -b" counts lines
added and removed.

| File | Owner | Lines | What changes |
|------|-------|-------|--------------|
| `rocq/FlambdaValueSpec.v` | C0 | +29 -1 | `location`; `Value_location` in `value`; `cell`, `heap`, `empty_heap`, `cell_of`. No observation changes: each has a wildcard, so a location is no closure, block, boxed number or string, and is not allocated. |
| `rocq/FlambdaPrimitiveModel.v` | C1 (P1 adds to it) | +30 -1 | `cell_mutability`, `init_or_assign`, `heap_primitive` (two constructors, `Make_block_with_identity` and `Block_set`), and `Heap` in `prim`. `mutability`, `equality_comparison`, `Block_load` with its mutability and `Phys_equal` are P1's, and are used as they are. |
| `rocq/FlambdaPrimitiveSpec.v` | C1 (the signature of `eval_prim` and the laws are C0's; neither changes) | +27 -1 | `result_kind_of_heap_primitive`, and a case of `prim_result_kind`. `access_in_range` and `heap_primitive_in_range`, and a case of `prim_in_range`: a primitive of the heap carries the numbers of the `Make_block` or the access that it stands for. `value_in_range`: a location is in range (it holds no number). `eval_prim` has a wildcard already: it has no value on `Heap _`, and treats a location as any value that no observation reads. |
| `rocq/FlambdaPrimitiveProofs.v` | C1 | +8 -6 | `eval_prim_arity`: a fourth branch (`Heap`: no value). `eval_prim_static_values`, `eval_prim_statics_extend`: a fourth pattern in the destruct on `prim`. `eval_is_null_statics_extend`: a seventh pattern in the destruct on `value`. |
| `rocq/FlambdaSemanticsProofs.v` | C0 | +3 -3 | `closure_in_set_of`, `closure_in_set_slot`, `project_function_slot_defined`: one more name in the pattern of the destruct on `value`; the existing catch-all branches take it. |
| `rocq/FlambdaClosuresSpec.v` | C3 | +5 -2 | `value_valid`: a location is valid (there is nothing in it). `value_sets_are`: a location holds no closure, so the property of the closures in a value holds of it. |
| `rocq/FlambdaClosuresProofs.v` | C3 | +6 -6 | Six destructs on `value` (among them `closure_in_set_valid`): one more name in the pattern; the existing catch-all branches take it. |
| `rocq/FlambdaValidatorEquivarianceProofs.v` | N3 | +1 -1 | `block_made_equivariant`: a fourth pattern in the destruct on `prim`. |
| `rocq/FlambdaBlockLoadProofs.v` | V2 | +2 -2 | `block_made_spec`, `unary_applied_spec`: a fourth pattern in the destruct on `prim`. |
| `rocq/FlambdaIdentitiesProofs.v` | P1 | +2 -2 | `binary_applied_spec`, `identity_named_equivariant`: a fourth pattern in the destruct on `prim`. |
| `rocq/FlambdaLiftProofs.v` | V3 | +4 -4 | `lift_named_lifted`, `lift_named_no_code`, `lift_named_rename`: a fourth pattern in the destruct on `prim`; in the first, one more pattern in a destruct on `value`. |
| `rocq/FlambdaMyClosureProofs.v` | V3 | +5 -4 | `value_free` (a definition of the proofs: a value free of a code id): a location is free of it, as a constant is. `closure_of_free`, `closure_in_set_free`, `project_function_slot_free`: one more name in the pattern of the destruct on `value`. |
| `rocq/FlambdaUnusedSlotsProofs.v` | V3 | +4 -2 | `closure_of_drop`, `closure_in_set_drop`: one more name in the pattern of the destruct on `value`. |
| `rocq/FlambdaStaticsOrderProofs.v` | V2 | +2 -1 | `value_avoids_nothing`: one more name in the pattern of the destruct on `value`. C0 made this repair when it merged the series: the file came to the integration branch after the series was cut. |
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
| `tests/semantics/types/types_difftest.ml` | T7 | +5 -3 | Four matches on a value of the model. A location is no tagged immediate and not the contents of a boxed number, so the generator of values for a type makes none from it; it has no parts; it is printed `<location n>`. The tests make no location, and no expected output changes. |

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
variable as one more variable. `exec_prim` was not changed by
that: its test `forallb (argument_bound statics h) vs` is as it was,
and `eval_prim` takes the same arguments.

On C5's epoch the machine follows `step` once more. `heap_step`
evaluates the extra arguments of the exception continuation of a call
and gives the callee that continuation with them
(`FlambdaSemanticsSpec.with_extra_args`); `heap_apply_cont_value` is a
`Fixpoint`, as `apply_cont_value` is, and applies a continuation with
extra arguments to the arguments followed by them. A trap action is
not executed, as in `step`. `cont_value_closed`, `cont_related` and
`cont_code_free_of` have a case for a continuation with extra
arguments: its extra arguments are closed, and related to those of the
continuation it is related to; the handlers it holds are those of the
continuation inside. No statement changes text. In the proofs, what
was said of the application of a continuation by cases is now three
lemmas by induction on the continuation (the heap is left as it is;
the state after is closed; its handlers name no symbol left out), and
the simulation has the case.

On P1's primitives the prototype loses what P1 defines, and keeps what
it says of a location. Gone: its `mutability` and
`equality_comparison`; `Phys_equal` and `Block_load_mutable` under
`Heap`; `immediate_or_null` and its own `eval_phys_equal`. Two
primitives are left under `Heap`, `Make_block_with_identity` and
`Block_set`. `exec_bound_prim` has three cases before `eval_prim`: a
primitive under `Heap`; a unary primitive of a location, which reads
the cell (`exec_unary_on_cell`); and `Phys_equal` with a location
among its two arguments (`eval_phys_equal_location`). What changed in
what the machine does:

- A `Block_load` of a location reads the field where its mark allows
  (`load_allowed`): a load marked `Mutable` reads any cell, and one
  marked `Immutable` or `Immutable_unique` a cell made
  `Immutable_unique`. That is what the two constructors of before
  did; the load marked `Immutable_unique` is new, and is treated as
  the one marked `Immutable`. A `Block_load` of a value that is not a
  location is P1's, whatever its mark.
- `exec_unary_on_cell` ends in a wildcard: P1's unary primitives on
  numbers and on strings have no value on a location.
- `Phys_equal` without a location is P1's `eval_phys_equal`, which has
  no value on null. The prototype's own had one: two nulls were
  equal, and null differed from an allocated value and from a
  location. Now a location against null has no value either. This
  narrows what is defined, and follows the CR that is in the tree
  (the request, section 2.6 and decision 3).
- `coeffects_of_prim`: the load with coeffects is `Block_load` marked
  `Mutable`. `effects_of_prim` has no effects on every unary primitive
  but `Opaque_identity` and `Box_number`, and on every binary one,
  which is what the compiler says of P1's (`String_or_bigstring_load`
  here is a load from a string, which is immutable).

Statements: `load_known_field_statement` is now of a load with any
mark, where it was of the load marked `Immutable`; a load from an
immutable block does not look at its mark. No other statement changed
text. In the proofs, what was proved of each primitive of `eval_prim`
by cases now comes from its laws: `eval_prim_related` (V3's: no
primitive tells apart values that the observations read alike) for
related arguments, and `eval_prim_preserves` for closedness. So no
proof lists the unary or the binary primitives, and one that P1 adds
needs no case in the heap's files unless it reads a cell.

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

Statements: no text changed in the adaptation to the three epochs (one
changed on P1's primitives, above). The 25 statements that the
prototype proved on the old base are proved with the same text, and
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
- The cost to the other owners is small: twenty-five files, most of
  them a name in a pattern. The work is in the prototype's own proofs,
  which gain the lemmas on closures of a set (a closure of a set is a
  closure; what a closure that is not a symbol projects; a projection
  does not change as the static environment grows) and a case in each
  proof by cases on the relation.

## The heap in `state`: a rehearsal of the sweep

The step after the first is the sweep: `state` gains the heap, and
nothing else changes. It was rehearsed on a scratch branch that is not
for merging (`flambda2-rocq/C4-sweep-rehearsal-3`: its first commit is
what the script does, its second what the rules then repair), over a
base that has C2's tests of kinds at binders and C3's partial
applications and over-applications. The real sweep is run again on the
tip of its day, after the validator's series and C0's commit that
names the initial state of a unit. The script is
`requests/C4-heap-sweep.py`; the checker with the rules is
`requests/C4-heap-sweep-check.py`; each says at its head how it is
run.

### The change

In `rocq/FlambdaSemanticsSpec.v`: `state` has a fifth field,
`state_heap : heap`, last. `Exit k vs hp` and `Exits k vs hp` carry
the heap, last. `call_code`, `run_call`, `apply_cont_value`,
`apply_continuation` and `call_function` take it as their last
argument, and `step` gives every state it builds the heap of the state
it was given. `behaves s (Exits k vs hp)` is `∃ fuel, run fuel s =
Exit k vs hp`, so `refines` and `equivalent` compare the heap at an
exit, exactly. No term makes a cell, so the heap of a run is the heap
it started with. `state_values_all` is not changed.

### What was decided where nothing said

1. The heap is named `hp` in every statement. `h` is a handler in
   some four hundred places of the proofs.
2. A statement gains one binder, `(hp : heap)`, after the binder of
   the static environment beside which the heap is first used, and
   the two states of a statement share it, also where their static
   environments differ. With a heap for each side the statement would
   be false: exits are compared by their heaps.
3. `Exits` carries the heap, as `Exit` does.
4. A state that an example builds has `empty_heap`, and so has its
   exit. C0's definition of the initial state will carry it.
5. The functions of `Proofs` files that compare two results (`ended`,
   `result_related` and `result_simulated` of
   `FlambdaSemanticsProofs.v`, `related` of `FlambdaTrapProofs.v`)
   compare the heaps of two exits, as they compare their values.
6. C5's machine with a stack follows: `Stack_exit` carries the heap,
   and `unwind`, `stack_enter`, `stack_call`, `stack_run_call` and
   `stack_apply_cont` take it.
7. N1's `rename_state` builds the state with the heap it was given: a
   cell holds values, and values hold no names.
8. The heap's own machine stays beside `step` until `step` runs the
   primitives of the heap. `forget_heap` keeps the heap, and
   `heap_step_agrees_statement` changes by one pattern.
9. A section whose statements build states from a `Variable` that is
   a static environment gains `Variable hp : heap`.
10. `state_values_all` gains the cells with the primitives, not here:
    no cell exists before, and C0 asked for a commit that adds the
    component and nothing else.

### What a script does

The script edits the text of the `.v` files, and compiles nothing. On
the base of the rehearsal it changes 66 files:

- 965 applications of `State`, `Exit`, `Exits`, `Stack_exit` and of
  the ten functions that take the heap gain it: `hp`; `_` in the 40
  patterns that do not use it; `empty_heap` beside
  `empty_static_env` and in the 23 exits and states that examples
  write out;
- 299 statements, lemmas and constructors of relations gain the
  binder, 64 of them in 19 `Spec` files (below);
- 37 first `intros` of a proof gain the name, where the binder went
  into the leading quantifier of the statement;
- 140 explicit applications of a lemma that gained the binder gain
  `_` at its position;
- the three constructors, the field, four comparisons of two exits,
  two patterns that take a state apart, and one variable of a
  section.

After it every statement and every definition of the 283 files
compiles (checked with `rocq compile -vos`, which runs no proof
outside a section). The `Spec` files whose statements gain a binder,
with the number of binders: `FlambdaSemanticsSpec.v` 8,
`FlambdaContextWhereSpec.v` 9, `FlambdaPartialApplicationSpec.v` 9,
`FlambdaWellKindedSpec.v` 6, `FlambdaClosuresSpec.v` 5,
`FlambdaTrapSpec.v` 5, `FlambdaControlFlowSpec.v` 3,
`FlambdaLiftSpec.v` 3, `FlambdaApplySpec.v` 2,
`FlambdaInlineFreshSpec.v` 2, `FlambdaAlphaSpec.v`,
`FlambdaCanonicalFreeNamesSpec.v`, `FlambdaEquivarianceSpec.v`,
`FlambdaRangeSpec.v` and `FlambdaUnusedStaticsSpec.v` 1 each; in the
types library `FlambdaSimplifySwitchSpec.v`, `FlambdaTypesSpec.v` and
`FlambdaTypingEnvRefinementSpec.v` 2 each and
`FlambdaEnvAliasesFollowSpec.v` 1. No statement changes meaning: each
says of one more component, which nothing reads, what it said.

The script and the rules leave 102 lines longer than 80 columns; they
do not wrap, and the lines are wrapped again by hand.

### The proofs

There are 7,244 proofs in the 283 files. After the script 265 of
them fail, in 52 files. Each proof is checked on its own
(`rocq compile -vok`, with the proofs that fail admitted in a copy),
so that one that fails hides none; a proof of a section that is not
run is admitted with the variables that Rocq says it uses on the tree
before the sweep, so that the lemma is the same lemma after the
section. Rules driven by the error message then edit a proof that
fails and check it again, keeping an edit when the proof passes or
its first error moves forward. They repair 200 proofs, with
353 edits. What the rules are:

- the name of the heap after the name of a static environment, or of
  the values of an exit, in an `intros` or in a pattern that takes a
  relation on states apart (235 edits);
- the heap, or `_`, as an argument that an explicit application of a
  lemma or of a hypothesis is short of (90);
- `hp` for a `_` that cannot be inferred, and `_` for an `hp` that is
  not in scope (17);
- a third part in a pattern that takes the comparison of two exits
  apart (11).

65 proofs are left, in 27 files. The tree has not been
built whole: `make all` waits for them.

By file, for the files with a proof that fails after the script, and
by owner, for all the files that the script edits:

| File | Owner | Edits by the script | Proofs broken after it | Repaired by the rules | Left |
|------|-------|--------------------:|-----------------------:|----------------------:|-----:|
| `rocq/FlambdaContextProofs.v` | C0 | 166 | 16 | 9 | 7 |
| `rocq/FlambdaSemanticsProofs.v` | C0 | 164 | 11 | 11 | 0 |
| `rocq/FlambdaWellFormedProofs.v` | C0 | 28 | 1 | 1 | 0 |
| `rocq/FlambdaControlFlowProofs.v` | C0 (S3) | 8 | 3 | 3 | 0 |
| `rocq/FlambdaApplyProofs.v` | C0 (S4) | 26 | 6 | 6 | 0 |
| `rocq/FlambdaStaticProofs.v` | C0 (S5) | 0 | 2 | 2 | 0 |
| `rocq/FlambdaWellKindedProofs.v` | C2 | 49 | 6 | 2 | 4 |
| `rocq/FlambdaClosuresProofs.v` | C3 | 42 | 6 | 5 | 1 |
| `rocq/FlambdaPartialApplicationProofs.v` | C3 | 55 | 5 | 3 | 2 |
| `rocq/FlambdaHeapProofs.v` | C4 | 9 | 2 | 0 | 2 |
| `rocq/FlambdaTrapProofs.v` | C5 | 69 | 7 | 3 | 4 |
| `rocq/FlambdaAlphaProofs.v` | N1 | 1 | 1 | 1 | 0 |
| `rocq/FlambdaEquivarianceProofs.v` | N1 | 19 | 7 | 6 | 1 |
| `rocq/FlambdaHeapEquivarianceProofs.v` | N1 | 2 | 4 | 0 | 4 |
| `rocq/FlambdaNominalProofs.v` | N1 | 7 | 3 | 3 | 0 |
| `rocq/FlambdaScopeProofs.v` | N1 | 20 | 1 | 1 | 0 |
| `rocq/FlambdaStateSupportProofs.v` | N1 | 2 | 1 | 0 | 1 |
| `rocq/FlambdaContextWhereProofs.v` | N2 | 18 | 12 | 9 | 3 |
| `rocq/FlambdaInlineFreshProofs.v` | N2 | 9 | 1 | 1 | 0 |
| `rocq/FlambdaIdentitiesProofs.v` | P1 | 7 | 1 | 0 | 1 |
| `types/rocq/FlambdaTypesProofs.v` | T1 | 0 | 17 | 16 | 1 |
| `types/rocq/FlambdaSimplifySwitchProofs.v` | T1 (S2) | 0 | 10 | 10 | 0 |
| `types/rocq/FlambdaTypingEnvRefinementProofs.v` | T2 | 0 | 16 | 16 | 0 |
| `types/rocq/FlambdaSimplifyPassProofs.v` | T2 (S1) | 5 | 5 | 3 | 2 |
| `types/rocq/FlambdaSimplifyPrimitivesProofs.v` | T2 (S1) | 0 | 3 | 3 | 0 |
| `types/rocq/FlambdaSimplifyProjectionsProofs.v` | T2 (S1) | 0 | 1 | 1 | 0 |
| `types/rocq/FlambdaAliasesProofs.v` | T3 | 6 | 6 | 6 | 0 |
| `types/rocq/FlambdaEnvAliasesFollowProofs.v` | T3 | 10 | 7 | 7 | 0 |
| `types/rocq/FlambdaSimplifyStaticsProofs.v` | T3 | 2 | 1 | 0 | 1 |
| `types/rocq/FlambdaSimplifyApplyProofs.v` | T4 (S4) | 3 | 5 | 5 | 0 |
| `rocq/FlambdaCompareProofs.v` | V1 (C0) | 21 | 2 | 2 | 0 |
| `rocq/FlambdaNormaliseProofs.v` | V1 (C0) | 42 | 31 | 25 | 6 |
| `rocq/FlambdaUnusedStaticsProofs.v` | V1 (C0) | 15 | 3 | 3 | 0 |
| `rocq/FlambdaValidateProofs.v` | V1 (C0) | 0 | 2 | 2 | 0 |
| `rocq/FlambdaBlockLoadProofs.v` | V2 | 7 | 2 | 1 | 1 |
| `rocq/FlambdaCseProofs.v` | V2 | 7 | 2 | 1 | 1 |
| `rocq/FlambdaRenameApartProofs.v` | V2 | 0 | 1 | 1 | 0 |
| `rocq/FlambdaStaticsOrderProofs.v` | V2 | 9 | 2 | 2 | 0 |
| `rocq/FlambdaUnboxProofs.v` | V2 | 7 | 2 | 1 | 1 |
| `rocq/FlambdaUnusedContsProofs.v` | V2 | 0 | 1 | 1 | 0 |
| `rocq/FlambdaKnownSymbolsProofs.v` | V3 (S5) | 31 | 4 | 2 | 2 |
| `rocq/FlambdaLiftProofs.v` | V3 (S5) | 79 | 11 | 4 | 7 |
| `rocq/FlambdaMyClosureProofs.v` | V3 (S5) | 14 | 1 | 0 | 1 |
| `rocq/FlambdaSimulationProofs.v` | V3 (S5) | 12 | 3 | 0 | 3 |
| `rocq/FlambdaUnusedSlotsProofs.v` | V3 (S5) | 29 | 4 | 2 | 2 |
| `rocq/FlambdaContAlikeProofs.v` | V4 | 46 | 6 | 2 | 4 |
| `rocq/FlambdaLoopAliasesProofs.v` | V4 | 0 | 5 | 4 | 1 |
| `rocq/FlambdaLoopifyProofs.v` | V4 | 58 | 3 | 2 | 1 |
| `rocq/FlambdaRecHandlersProofs.v` | V4 | 0 | 3 | 3 | 0 |
| `rocq/FlambdaShortcutProofs.v` | V4 | 5 | 2 | 1 | 1 |
| `rocq/FlambdaSinkContsProofs.v` | V4 | 3 | 5 | 5 | 0 |
| `rocq/FlambdaUnusedParamsProofs.v` | V4 | 19 | 3 | 3 | 0 |

| Owner | Files | Edits by the script | Proofs broken after it | Repaired by the rules | Left |
|-------|------:|--------------------:|-----------------------:|----------------------:|-----:|
| C0 | 5 | 406 | 28 | 21 | 7 |
| C0 (S3) | 2 | 16 | 3 | 3 | 0 |
| C0 (S4) | 2 | 32 | 6 | 6 | 0 |
| C0 (S5) | 1 | 0 | 2 | 2 | 0 |
| C1 | 2 | 23 | 0 | 0 | 0 |
| C2 | 2 | 66 | 6 | 2 | 4 |
| C3 | 4 | 157 | 11 | 8 | 3 |
| C4 | 2 | 11 | 2 | 0 | 2 |
| C5 | 2 | 115 | 7 | 3 | 4 |
| N1 | 11 | 69 | 17 | 11 | 6 |
| N2 | 4 | 79 | 13 | 10 | 3 |
| P1 | 1 | 7 | 1 | 0 | 1 |
| T1 | 2 | 6 | 17 | 16 | 1 |
| T1 (S2) | 2 | 6 | 10 | 10 | 0 |
| T2 | 2 | 6 | 16 | 16 | 0 |
| T2 (S1) | 3 | 5 | 9 | 7 | 2 |
| T3 | 4 | 21 | 14 | 13 | 1 |
| T4 (S4) | 1 | 3 | 5 | 5 | 0 |
| V1 (C0) | 5 | 83 | 38 | 32 | 6 |
| V2 | 6 | 30 | 10 | 7 | 3 |
| V3 (S5) | 7 | 179 | 23 | 8 | 15 |
| V4 | 7 | 131 | 27 | 20 | 7 |
| all | 77 | 1451 | 265 | 200 | 65 |

### What is left, and whose it is

What is left is of four kinds, by the first error of each proof.

- An explicit application, by position, of a lemma, of an induction
  hypothesis or of a hypothesis of a section that takes the
  environments: the heap is missing at more than one place, or the
  proof names what it introduces after a tactic that the rules do not
  follow. Most of what is left is this, and all of C0's, N2's, V1's
  and V2's. It is mechanical, for a hand.
- A statement of a proofs file that names an exit and needs its heap
  (`stuttering_ends` and `stuttering_refines` of
  `FlambdaSimulationProofs.v`, `late_ends` and `late_refines` of
  `FlambdaPartialApplicationProofs.v`, which say `∃ k vs`), or a
  pattern that takes an exit apart one name short
  (`run_renamed_exit`, `stack_behaves_equivariant`, `enter_related`,
  the three of `FlambdaWellKindedProofs.v` about an exit).
- A proof that writes out a state where no heap is in sight
  (`lifted_step`, `simplify_expr_sound`, `let_static_body_refines_under`,
  `let_static_typed`).
- Five where the owner chooses. N1: `forget_with_heap` is no longer
  true as stated, since `forget_heap` keeps the heap (N1 restates
  `with_heap`), and `state_finitely_supported` gives a combinator of
  four arguments a constructor of five (N1 gives it a function). C5:
  `step_related` needs the invariant between the two machines to say
  that their states have the same heap. C4: `heap_call_code_agrees`
  and `heap_apply_cont_value_agrees` must say that the heap of the
  state is the heap of the heap's own machine.

N1 has said it does its six itself, as one commit on the branch of the
sweep. By owner and file:

- C0, 7:
  - `rocq/FlambdaContextProofs.v`: `carried_of_result`, `apply_cont_value_transfer`, `call_function_transfer`, `transfer`, `related_states_refines_from`, `related_states_refines`, `let_static_code_refines_where`
- C2, 4:
  - `rocq/FlambdaWellKindedProofs.v`: `step_well_kinded_here`, `exit_well_kinded_here`, `well_kinded_exit`, `run_exit`
- C3, 3:
  - `rocq/FlambdaClosuresProofs.v`: `let_closures_runs`
  - `rocq/FlambdaPartialApplicationProofs.v`: `late_ends`, `late_refines`
- C4, 2:
  - `rocq/FlambdaHeapProofs.v`: `heap_call_code_agrees`, `heap_apply_cont_value_agrees`
- C5, 4:
  - `rocq/FlambdaTrapProofs.v`: `enter_related`, `step_related`, `unwind_equivariant`, `stack_behaves_equivariant`
- N1, 6:
  - `rocq/FlambdaEquivarianceProofs.v`: `run_renamed_exit`
  - `rocq/FlambdaHeapEquivarianceProofs.v`: `forget_with_heap`, `rename_static_env_inverse_l`, `rename_static_env_inverse_r`, `heap_state_of_renamed_expr`
  - `rocq/FlambdaStateSupportProofs.v`: `state_finitely_supported`
- N2, 3:
  - `rocq/FlambdaContextWhereProofs.v`: `let_cont_recursive_handler_refines_from`, `let_static_code_refines_where`, `let_cont_handler_refines_in_range`
- P1, 1:
  - `rocq/FlambdaIdentitiesProofs.v`: `apply_identities_refines_at`
- T1, 1:
  - `types/rocq/FlambdaTypesProofs.v`: `inline_identity`
- T2 (S1), 2:
  - `types/rocq/FlambdaSimplifyPassProofs.v`: `let_static_body_refines_under`, `simplify_expr_sound`
- T3, 1:
  - `types/rocq/FlambdaSimplifyStaticsProofs.v`: `let_static_typed`
- V1 (C0), 6:
  - `rocq/FlambdaNormaliseProofs.v`: `inline_calls_refines_knowing`, `remove_unused_defined_lets_equivalent_bound`, `inline_known_calls_equivalent_knowing`, `rewrite_code_refines_aux`, `rewrite_code_refined_aux`, `thread_switch_equivalent`
- V2, 3:
  - `rocq/FlambdaBlockLoadProofs.v`: `load_blocks_knowing_refines`
  - `rocq/FlambdaCseProofs.v`: `share_primitives_knowing_refines`
  - `rocq/FlambdaUnboxProofs.v`: `unbox_numbers_knowing_refines`
- V3 (S5), 15:
  - `rocq/FlambdaKnownSymbolsProofs.v`: `fold_step_components`, `folded_related_step`
  - `rocq/FlambdaLiftProofs.v`: `call_code_lifted`, `lifted_step`, `lift_simulates`, `closed_stays_plain`, `call_code_plain`, `apply_cont_value_plain`, `plain_step_components`
  - `rocq/FlambdaMyClosureProofs.v`: `apply_cont_value_ok`
  - `rocq/FlambdaSimulationProofs.v`: `stuttering_exit`, `stuttering_ends`, `stuttering_refines`
  - `rocq/FlambdaUnusedSlotsProofs.v`: `drop_step_components`, `drop_step`
- V4, 7:
  - `rocq/FlambdaContAlikeProofs.v`: `apply_alike_carries`, `alike_carries`, `applies_alike_sym`, `applies_alike_carries`
  - `rocq/FlambdaLoopAliasesProofs.v`: `follow_aliases_in_loops_equivalent_in`
  - `rocq/FlambdaLoopifyProofs.v`: `loops_step`
  - `rocq/FlambdaShortcutProofs.v`: `shortcut_switch_equivalent`

### The test tool and the extracted files

`tests/tools/flsemantics.ml` changes in two places: the pattern of an
exit has a third component, and the record of the initial state has
`state_heap = Values.empty_heap`. The extracted files are generated
again. No expected output changes: the heap of every run is empty.
