# Record order: the 23 records with a call in more than one field

This folder says, for each of the 23 places that the port marks
`PORT-GAP(record-order)`, whether the order in which the fields of the record
are evaluated can change anything. Each verdict is from a reading of the
compiler's code of the functions called. This file has the question, the sense,
the table of the places, the facts that hold for many places and what was not
read. The detail is in four parts: `part-1.md` (places 1, 2, 3, 4, 17 and 18),
`part-2.md` (places 5 to 10), `part-3.md` (places 11 to 16, 20 and 21),
`part-4.md` (places 19, 22 and 23, and the tables of identifiers).

## 1. What a place is, and the question

The compiler builds a record (or an inline record) with a call in more than one
field. OCaml leaves the order in which the fields of a record are evaluated
unspecified. The port takes the fields in the order of the type, the last field
first, binds each call before the record is built, and marks the place
`PORT-GAP(record-order)` (`GUIDE.md`, section 2). There are 23 such places, in
12 files of the port. The question of each place: can the order of those calls
change anything?

The human's ruling. No order is assumed, and the compiler is not changed. Each
place is judged by a reading of the compiler's code of the functions called. His
words: "it should become evident that e.g. many Map-manipulating functions are
sufficiently pure, in some sense."

## 2. The sense

There is one sense of "pure enough", the same for every function and every
place.

For each function that is called in a field, and for each function called in its
arguments, four things are said. They are said from a reading of its body in the
compiler, and of the body of everything that it calls, down to leaves.

- W (writes). A call assigns to state that outlives the call. State is: a
  reference or a mutable field that something else can reach; a global table (a
  table that interns or hash-conses values, and a table that memoises, are
  tables); a counter (of fresh names, of stamps, of identifiers); a channel or a
  file; a flag. Each such state is named by where it is defined (file and line).
- R (reads). The state of those kinds that a call reads: flags of the command
  line, the current compilation unit, a table, a counter. Each is named by where
  it is defined.
- F (fails). A call can raise an exception or stop with a fatal error: where
  (file and line), and on what condition. "None" rests on the reading of the
  whole body.
- A (allocates a thing with an identity). A call returns a value that is
  mutable, or that could be told apart by physical equality (a fresh reference,
  a fresh table): what.

A LEAF is: a function whose body was read and that calls nothing more; or a
primitive of OCaml; or a function of OCaml's standard library, for which W, R, F
and A are stated from its documented behaviour, with its module and its name,
and with the statement that its body was not read; or a field projection.

TWO CALLS COMMUTE if neither writes what the other reads or writes. Then the
order of the two cannot change a result or a state.

- Where either can fail: the order chooses only which failure is seen, and
  whether the other call's writes happen before the failure. The entry of the
  place says which failures. That is not a refusal.
- A table that interns: a call that may add an entry writes the table. Two calls
  that both may add to the same table do not commute by the rule above, unless
  the reading shows that what each returns, and what the table then answers for
  every key, do not depend on which entry was added first. That is shown from
  the code: how an identifier is chosen for a new entry (from the data alone, or
  from a counter, or from what the table already holds). If it depends on the
  order in any way, the verdict is REPORT.
- A call that makes a fresh name (a variable, a symbol, a continuation, a code
  identifier, a stamp of any kind): the verdict of its place is REPORT, with
  what is made and where. It is not waved through.
- An effect that is only an allocation of a fresh mutable thing (A) is not a
  write for this purpose: two allocations commute.

THE VERDICT OF A PLACE is one of:

- COMMUTE: every pair of the calls of the place commutes, and none can fail.
- COMMUTE, FAILURES ORDERED: every pair commutes, but some can fail. The entry
  lists which, and what the order then chooses.
- REPORT: a fresh name is made, or the order can change a result or a state, or
  the code did not decide. The entry says exactly what and where. This goes to
  the human.

WHAT IS ASSUMED, AND WHAT NOT.

- Nothing about a function from its name or its type. Its body is read. A
  function that looks like a projection may go through a table.
- The functors of the compiler's containers (maps, sets, tables of identifiers)
  are code of the compiler, and are read:
  `middle_end/flambda2/algorithms/container_types.ml`,
  `middle_end/flambda2/algorithms/patricia_tree.ml` and what they apply. So are
  the comparison and hash functions that a map or a set is given: a comparison
  that reads a table reads that table.
- Labels and optional arguments: an optional argument with a default evaluates
  its default at the call.

## 3. What was read

The compiler's files as they are at commit
ecc5c0d968c892b4312065caef0f19ffffa042a9, the donor commit of the port
(`PROVENANCE.md` names it). They were read in a tree of commit
4fe46bb689903ead25d346ac9efd3c883821f171. Between those two commits `git diff
--name-only` names `.gitignore` and files under `rocq/`,
`middle_end/flambda2/rocq/` and `middle_end/flambda2/tests/`, and nothing else:
every file of the compiler that this folder cites has the same bytes at both.

By reading only. Nothing was built and nothing was run. All numbers of lines are
of those files. Part 2 says of itself that the files of the port were not read:
it is about the compiler only.

THE FORM OF THE FOUR PARTS. The four parts are four readings, each of its own
places. Under FUNCTIONS a part has one entry for each function that was read:
`defined` (where; for a field of the result of a functor, or for an alias, the
chain to the body), `calls` (the functions that its body calls, or LEAF and
why), `W`, `R`, `F` and `A` (section 2), and `read` (the lines that were read to
say this). Under PLACES it has one entry for each place: the fields and their
calls in the order of the type, the pairs of calls and why they commute, and the
verdict. Then what was not read, and doubts. A part names a place by P and its
number: P7 is place 7. The line `place:` under the heading of a place has the
compiler's file and lines. A heading that would be longer than 80 columns is cut
and ends with `..`; the line `heading:` under it has the heading whole. A
function that several places reach can have an entry in more than one part; the
entries of two parts are not merged.

WHERE TWO PARTS SAY DIFFERENT THINGS OF ONE FUNCTION. The entries of the parts
were laid side by side for every function that has more than one. They agree on
what is written and read. They differ in these points, and no verdict rests on
one of them.

- `Table_by_int_id.Make(E).add`, when no identifier is left
  (`middle_end/flambda2/algorithms/table_by_int_id.ml` 75-107). Parts 1, 2 and 3
  name the fatal error of line 99; part 4 says that the assertion of line 91
  fails before it. Part 4 is right: the walk adds one to the identifier (line
  35), and the assertion on its flags fails as soon as the walk leaves the
  identifiers of the table, which is before it can come round to where it
  began. Line 99 can be reached only where assertions are compiled out.
- The fatal error of `Simple.with_coercion`
  (`middle_end/flambda2/identifiers/int_ids.ml` 822-825), on the path of a
  waiting renaming: "not reachable" in part 2, listed as possible in part 3. Not
  settled.
- The lookup of a simple with a coercion
  (`middle_end/flambda2/algorithms/table_by_int_id.ml` 110-111): "not reachable
  for a simple made through the interface" in part 2; `Not_found` is possible in
  parts 3 and 4 if the table was replaced after the simple was made. Part 2's
  words hold where no table is replaced while Simplify runs (section 8).
- The failures of the comparison of compilation units
  (`utils/compilation_unit.ml` 91 and 286): counted in parts 1 and 3, called
  invariants in part 4, not named in part 2 (section 8).
- `Misc.fatal_errorf`: under R, part 1 says none, and parts 2 and 4 name the
  state of the formatter, which part 1 has under W.
- Under A, part 3 also writes a fresh immutable value; parts 1, 2 and 4 write
  "none" for it. Such a value has no identity that a call of these places tests.
- Four numbers of lines: the end of `Tree_operations`, of `Container_types.Make`
  and of `Make_map` is given with or without the line of the attribute that
  follows the module; `Int_ids.initialise` is given with or without `reset`,
  which follows it.

## 4. The table of the 23 places

The files of the port are named from the folder of the port; the files of the
compiler from the root of the repository. The calls are in the order of the
fields in the type; a field without a call is left out. `f` on `g`: `f` is
applied to the result of `g`.

| Place | The port: definition, file | The compiler: file, lines | Calls, field by field, in the order of the type | Verdict | Reason | Detail |
|---|---|---|---|---|---|---|
| 1 | `remove` in `env/Continuation_uses_env.v` | `middle_end/flambda2/simplify/env/continuation_uses_env.ml` 145-148 | `continuation_uses`: `Continuation.Map.remove`; `continuation_arities`: `Continuation.Map.remove` | COMMUTE | Both calls are `Continuation.Map.remove`, on two maps: no write, no read of state, no failure. | `part-1.md` |
| 2 | `create` in `env/Downwards_acc.v` | `middle_end/flambda2/simplify/env/downwards_acc.ml` 94-112 | `flow_acc`: `Flow.Acc.empty`; `are_lifting_conts`: `Are_lifting_conts.no_lifting`; `continuation_lifting_budget`: `Flambda_features.Expert.cont_lifting_budget` | REPORT | `Flow.Acc.empty` makes a fresh continuation: it writes a counter and a table. It is the only call of the three that writes or that can fail; the two others read flags or nothing. Nothing was found that the order can change. Reported to the human, as the rule for a fresh name asks. | `part-1.md` |
| 3 | `create` in `env/Downwards_env.v` | `middle_end/flambda2/simplify/env/downwards_env.ml` 245-276 | `inlining_state`: `Inlining_state.default`; `inlining_history_tracker`: `Inlining_history.Tracker.empty` on `Current_unit.get_cu_exn`; `specialization_cost`: `Specialization_cost.cannot_specialize` | COMMUTE, FAILURES ORDERED | No call writes when it succeeds. One call alone can fail (`Current_unit.get_cu_exn`, when no unit is set; it prints its message before it fails), so the order chooses nothing. | `part-1.md` |
| 4 | `enter_set_of_closures` in `env/Downwards_env.v` | `middle_end/flambda2/simplify/env/downwards_env.ml` 372-402 | `typing_env`: `Flambda2_types.Typing_env.closure_env`; `specialization_cost`: `Specialization_cost.cannot_specialize` | COMMUTE | `TE.closure_env` and `Specialization_cost.cannot_specialize`: no write, no read of state, no failure. | `part-1.md` |
| 5 | `apply_prim` in `flow/Mutable_unboxing.v` | `middle_end/flambda2/simplify/flow/mutable_unboxing.ml` 450-452 | `bindings`: `Simple.Map.add`; `rewrites`: `Named_rewrite_id.Map.add` | COMMUTE | Two additions to two immutable maps: no write, no read of state, no failure. | `part-2.md` |
| 6 | `apply_prim` in `flow/Mutable_unboxing.v` | `middle_end/flambda2/simplify/flow/mutable_unboxing.ml` 463-465 | `bindings`: `Simple.Map.add` on `Simple.var`; `rewrites`: `Named_rewrite_id.Map.add` | COMMUTE | As place 5; `Simple.var` returns its argument. | `part-2.md` |
| 7 | `create_block_like` in `lifting/Lifted_constant.v` | `middle_end/flambda2/simplify/lifting/lifted_constant.ml` 180-185 | `bound_static`: `compute_bound_static`; `defining_exprs`: `compute_defining_exprs`; `symbol_projections`: `Definition.symbol_projections`; `is_fully_static`: `Rebuilt_static_const.is_fully_static` | COMMUTE | No call writes state (one allocates). The constant is a block here, so its free names are stored, and no call can fail. | `part-2.md` |
| 8 | `create_set_of_closures` in `lifting/Lifted_constant.v` | `middle_end/flambda2/simplify/lifting/lifted_constant.ml` 198-203 | as place 7 | COMMUTE, FAILURES ORDERED | No call writes state when it succeeds (one allocates). One call alone can fail (`compute_bound_static`: the heavy checks on, and one symbol given to two function slots; it prints its message before it fails), so the order chooses nothing. | `part-2.md` |
| 9 | `create_code` in `lifting/Lifted_constant.v` | `middle_end/flambda2/simplify/lifting/lifted_constant.ml` 212-217 | as place 7 | COMMUTE, FAILURES ORDERED | `is_fully_static` alone writes (for code that is not rebuilt: caches of free names in its result types, a waiting renaming, entries of tables that intern) and alone can fail. The other calls read none of that. The order chooses nothing. | `part-2.md` |
| 10 | `create_definition` in `lifting/Lifted_constant.v` | `middle_end/flambda2/simplify/lifting/lifted_constant.ml` 221-227 | as place 7, with `Rebuilt_static_const.is_fully_static` on `Definition.defining_expr` | COMMUTE, FAILURES ORDERED | As place 9, but `compute_bound_static` can fail too. The order chooses which of the two failures is seen (here `is_fully_static` runs first), and whether the writes of `is_fully_static` come before a failure of `compute_bound_static`. | `part-2.md` |
| 11 | `create` in `Rebuilt_expr.v` | `middle_end/flambda2/simplify/rebuilt_expr.ml` 432 | `params1`: `create_mapping`; `params2`: `create_mapping` | COMMUTE | Each call of `create_mapping` fills a table that it has just made: two allocations. | `part-3.md` |
| 12 | `create_normal_non_code` in `Rebuilt_static_const.v` | `middle_end/flambda2/simplify/rebuilt_static_const.ml` 70-71 | `const`: `Static_const_or_code.create_static_const`; `free_names`: `Static_const.free_names` | COMMUTE, FAILURES ORDERED | No call writes. `Static_const.free_names` alone can fail, so the order chooses nothing. | `part-3.md` |
| 13 | `create_code` in `Rebuilt_static_const.v` | `middle_end/flambda2/simplify/rebuilt_static_const.ml` 94-95 | `const`: `Static_const_or_code.create_code`; `free_names`: `Code.free_names` | COMMUTE, FAILURES ORDERED | `Code.free_names` computes: it writes caches (and may force a waiting renaming and add to tables that intern), and it alone can fail. `create_code` applies a constructor and reads none of that. The order chooses nothing. | `part-3.md` |
| 14 | `create_code'` in `Rebuilt_static_const.v` | `middle_end/flambda2/simplify/rebuilt_static_const.ml` 102-103 | as place 13 | COMMUTE, FAILURES ORDERED | As place 13. | `part-3.md` |
| 15 | `find_code_characteristics` in `Rebuilt_static_const.v` | `middle_end/flambda2/simplify/rebuilt_static_const.ml` 110-111 | `cost_metrics`: `Code_metadata.cost_metrics`; `function_slot_size`: `Code_metadata.function_slot_size` | COMMUTE | Two readings of fields of one immutable record. | `part-3.md` |
| 16 | `map_set_of_closures` in `Rebuilt_static_const.v` | `middle_end/flambda2/simplify/rebuilt_static_const.ml` 341-344 | `const`: `Static_const_or_code.create_static_const` on `Static_const.set_of_closures`; `free_names`: `Set_of_closures.free_names` | COMMUTE, FAILURES ORDERED | No call writes. `Set_of_closures.free_names` alone can fail, so the order chooses nothing. | `part-3.md` |
| 17 | `arg_types_by_use_id_for_lifting` in `Simplify_let_cont_expr.v` | `middle_end/flambda2/simplify/simplify_let_cont_expr.ml` 211-217 | `arg_type`: `Flambda2_types.alias_type_of` on `Flambda_kind.With_subkind.kind` on `Bound_parameter.kind`; `typing_env`: `Downwards_env.typing_env` | COMMUTE | `alias_type_of` and the projections: no write, no read of state, no failure. | `part-1.md` |
| 18 | `compute_specialized_continuation` in `Simplify_let_cont_expr.v` | `middle_end/flambda2/simplify/simplify_let_cont_expr.ml` 1165-1176 | `cont_uses_env`: `Continuation_uses_env.add_continuation_use` on `One_continuation_use.use_kind`, `id`, `env_at_use` and `arg_types`; `handlers`: `Continuation.Map.add` | REPORT | `CUE.add_continuation_use` calls the meet of types, which can make a fresh variable and was not read to its leaves. Every write and every failure of the place is in that one field; `Continuation.Map.add` is pure. Nothing was found that the order can change. Reported to the human. | `part-1.md` |
| 19 | `create_have_lifted_set_of_closures` in `Simplify_named_result.v` | `middle_end/flambda2/simplify/simplify_named_result.ml` 45-48 | `let_bound`: `Bound_pattern.singleton`; `simplified_defining_expr`: `Simplified_named.create` on `Named.create_simple` on `Simple.symbol` | COMMUTE | For a symbol no call reads or writes a table, a counter or a flag, and none can fail. | `part-4.md` |
| 20 | `simplify_non_lifted_set_of_closures0` in `Simplify_set_of_closures.v` | `middle_end/flambda2/simplify/simplify_set_of_closures.ml` 935-939 | `function_slot_size`: `Code_metadata.function_slot_size`; `dbg`: `Code_metadata.dbg` | COMMUTE | Two readings of fields of one immutable record. | `part-3.md` |
| 21 | `simplify_non_lifted_set_of_closures0` in `Simplify_set_of_closures.v` | `middle_end/flambda2/simplify/simplify_set_of_closures.ml` 961-964 | `cost_metrics`: `Code_metadata.cost_metrics`; `function_slot_size`: `Code_metadata.function_slot_size` | COMMUTE | Two readings of fields of one immutable record. | `part-3.md` |
| 22 | `let_op_dollar` in `Simplify_switch_expr.v` | `middle_end/flambda2/simplify/simplify_switch_expr.ml` 381-386 | `let_bound`: `Bound_pattern.singleton` on `Bound_var.create`; `simplified_defining_expr`: `Simplified_named.create` | COMMUTE, FAILURES ORDERED | No call writes. `Simplified_named.create` alone can fail, and only on a broken invariant, so the order chooses nothing. The fresh variable is made before the record. | `part-4.md` |
| 23 | `unboxer` in `unboxing/Unboxers.v` | `middle_end/flambda2/simplify/unboxing/unboxers.ml` 249-253 | `var_kind`: `Value_slot.kind`; `poison_const`: `Const.const_poison` on `Value_slot.kind` | COMMUTE, FAILURES ORDERED | `Const.const_poison` alone may add to the table of constants and alone can fail (no identifier left). `Value_slot.kind` reads a field. The order chooses nothing. | `part-4.md` |

THE COUNT. 11 COMMUTE (places 1, 4, 5, 6, 7, 11, 15, 17, 19, 20, 21). 10
COMMUTE, FAILURES ORDERED (places 3, 8, 9, 10, 12, 13, 14, 16, 22, 23). 2 REPORT
(places 2 and 18).

THE TEN "FAILURES ORDERED". In nine of them one call alone can fail (places 3,
8, 9, 12, 13, 14, 16, 22 and 23). The other calls of the place cannot fail, so
the order does not choose which failure is seen; and they write no state, so the
state at the failure is the same in any order. (At places 9, 13, 14 and 23 the
call that can fail is also the only call that writes state.) The order chooses
nothing. Part 3 adds for places 12 and 16: the order chooses only whether the
blocks of the other calls were allocated before the failure, and nothing can see
that. In place 10 two calls can fail, `compute_bound_static` and
`Rebuilt_static_const.is_fully_static`. There the order chooses which of the two
failures is seen (in the order that the port takes, `is_fully_static` runs first
and its failure is the one seen); and, when only `compute_bound_static` fails,
whether the writes of `is_fully_static` (the caches of free names, the fields of
the name abstraction, the possible entries of tables) have happened before that
failure.

WHERE THE LINE BETWEEN THE FIRST TWO VERDICTS LIES. A point of failure in the
code that a place calls counts as "can fail" unless the code that was read and
the types exclude it. Part 2 gives place 7 COMMUTE, because the two points of
failure in the code that it calls cannot be reached there: one needs a symbol
that is defined twice, and the place has one pattern that defines one symbol;
the other needs an identifier whose flags the private types of the identifiers
exclude. (It says: if a guarded site is counted as "can fail", place 7 is
COMMUTE, FAILURES ORDERED, with nothing chosen by the order.) Part 4 gives
places 22 and 23 COMMUTE, FAILURES ORDERED: what is left there is excluded only
by things that hold outside the code that was read (at place 22, that no table
is replaced while Simplify runs; at place 23, that the identifiers of a table do
not run out). It says of each: if those points are counted as not reachable, the
verdict is COMMUTE.

## 5. The two places reported (2 and 18)

PLACE 2: `create`, `middle_end/flambda2/simplify/env/downwards_acc.ml` 94-112.

- What is made, and where. `Flow.Acc.empty`
  (`middle_end/flambda2/simplify/flow/flow_acc.ml` 29-41) makes a fresh
  continuation: its lines 30-32 call `Continuation.create`
  (`middle_end/flambda2/identifiers/continuation.ml` 109-122). The counter of
  stamps of continuations (the reference at line 22 of that file) goes up by
  one, and the table of continuations (held by the reference at line 103) gets
  an entry.
- Why the verdict is REPORT. By the rule of section 2 for a call that makes a
  fresh name, and for that reason only.
- What the reading found. `Flow.Acc.empty` is the only call of the place that
  writes state, and the only one that can fail: when no compilation unit is set
  (`typing/current_unit.ml` 33); by the failures of the table
  (`middle_end/flambda2/algorithms/table_by_int_id.ml` 99, and the assertions);
  by the failures of `Compilation_unit.hash` and `Compilation_unit.equal`.
  `Are_lifting_conts.no_lifting` writes nothing, reads no state and cannot fail.
  `Flambda_features.Expert.cont_lifting_budget` writes nothing, cannot fail, and
  reads two references of flags (`driver/oxcaml_flags.ml` 419 and 173);
  `Flow.Acc.empty` does not write a flag. So the two other calls neither read
  nor write what it reads or writes. Nothing was found that the order of the
  three fields can change.
- Detail: `part-1.md`, group B and P2.

PLACE 18: `compute_specialized_continuation`,
`middle_end/flambda2/simplify/simplify_let_cont_expr.ml` 1165-1176.

- What can be made, and where. `Continuation_uses_env.add_continuation_use`
  (`middle_end/flambda2/simplify/env/continuation_uses_env.ml` 65-104) calls
  `Flambda2_types.meet` (line 83). With the N-way algorithm that meet can reach
  `Variable.create` at `middle_end/flambda2/types/env/join_env.ml` 729: a fresh
  variable. The chain of calls is item 1 of the entry `Flambda2_types.meet` of
  `part-1.md`. The N-way algorithm is the one in force at this place, if the
  flags do not change during the pass: the place is reached only for a
  continuation that `Downwards_acc.add_continuation_to_specialize` recorded
  (`middle_end/flambda2/simplify/simplify_let_cont_expr.ml` 1193; its one caller
  is `middle_end/flambda2/simplify/simplify_switch_expr.ml` 1087), and that
  needs the flag of match-in-match
  (`middle_end/flambda2/simplify/simplify_switch_expr.ml` 935-939), which makes
  `Flambda_features.join_algorithm` answer the N-way algorithm
  (`middle_end/flambda2/ui/flambda_features.ml` 66-74).
- Why the verdict is REPORT. For two reasons. First, a fresh name can be made:
  it was not decided from the code whether this meet (the type of an argument
  against the type that is unknown but for the subkind) can meet the condition
  of line 729; the condition is on the types. Second, `Flambda2_types.meet` is
  not read to its leaves, and it can call the resolver of `.cmx` files.
- What the reading found. `Continuation.Map.add`, the call of the field
  `handlers`, writes nothing, reads no state and cannot fail. So neither call
  writes what the other reads or writes, whatever `add_continuation_use` does.
  Every write and every failure of the place is in the field `cont_uses_env`.
  What the order can change, as far as was read: nothing.
- What was not read. The meet of types to its leaves: the two algorithms and
  what they use are about twenty thousand lines. The entry `Flambda2_types.meet`
  of `part-1.md` gives the lines that were read; item 1 of the last section of
  that part gives what was not. For the binary algorithm, a search of the files
  named there finds no maker of names; that is a search, not a reading of every
  body. The resolver of `.cmx` files: `Flambda_cmx.load_cmx_file_contents` was
  read (`middle_end/flambda2/cmx/flambda_cmx.ml` 28-57); the bodies below it
  were not (item 2 of the same section names them). Not known: if an import can
  make fresh names.
- Detail: `part-1.md`, group F and P18.

## 6. Facts that hold for many places

Each fact is shown in the parts that are named with it.

THE MAPS AND SETS OF IDENTIFIERS ARE PATRICIA TREES ON THE INTEGER, AND TAKE NO
COMPARISON. For variables, symbols, names, constants, simples, code identifiers,
`Code_id_or_symbol` and continuations, `Set` and `Map` are `Patricia_tree.Make`
(`middle_end/flambda2/algorithms/patricia_tree.ml` 2229-2293) applied to a
printer only. The key is the integer of the identifier. No comparison function,
no hash function and no table is used by `add`, `find`, `mem`, `remove`,
`update`, `union`, `fold` or `iter`; the printer is used only by `print`,
`to_string` and the message of `disjoint_union`. The operations are persistent:
they return new immutable trees and write nothing. Shown in `part-4.md` (T7),
`part-1.md` (group A), `part-2.md` (`Simple.Map.add`) and `part-3.md` (C1).

`middle_end/flambda2/algorithms/container_types.ml` is NOT what makes those
maps. It makes maps and sets from the `Map.Make` and `Set.Make` of the standard
library, with the comparison of its argument (`part-1.md`, last section, item
10). The maps and sets of function slots and of value slots are made so: a slot
is a record, not an integer. Their comparison
(`middle_end/flambda2/identifiers/slot.ml` 61-78) reads no table (`part-3.md`,
C2 and C3; `part-4.md`, T7). `Named_rewrite_id.Map` is made so too, with the
comparison of integers (`part-2.md`, `Named_rewrite_id.Map.add`).

THE TABLES THAT INTERN CHOOSE AN IDENTIFIER FROM THE HASH OF THE DATUM, AND THEN
WALK UPWARDS. Every table of identifiers (of constants, variables, symbols,
simples with a coercion, code identifiers, continuations) is an instance of
`Table_by_int_id.Make` (`middle_end/flambda2/algorithms/table_by_int_id.ml`
38-127). Its `add` (lines 75-107) starts at the identifier made from the hash of
the datum and the flags of the table. If that identifier is free, the datum is
stored there. If it holds an equal datum, it is returned and nothing is written.
If it holds a different datum, the following identifiers are tried in turn. No
counter is used, and no entry is ever removed or replaced. So two additions of
new, different data to one table can exchange identifiers: when the first free
identifier on the walk of each is the same, the datum added first gets it, and
the other gets the next free one. For constants the hash is of the payload
alone, without the constructor: a tagged and an untagged constant of one number
always start at the same identifier. What a changed identifier can change
afterwards: every comparison, and every set and map of these identifiers, is by
the integer; so the order in which a set or a map is walked, and anything that
follows that order. Shown in `part-4.md` (T1 to T4, and T7), and in `part-1.md`
(`Table_by_int_id.Make(E).add`), `part-2.md` (`Int_ids.Simple.with_coercion` and
the tables that intern) and `part-3.md` (B9).

NO PLACE OF THE 23 HAS TWO CALLS THAT MAY ADD TO THE SAME TABLE. Part 1: none of
its six places has two calls that add to the same table (last section, item 12).
Part 2: at places 5 to 8 no call writes state (at place 8: no call that
succeeds; `compute_bound_static` prints its message before it fails); at places
9 and 10 one call only can add an entry to a table. Part 3: in none of its eight
places can two calls of different fields both add to a table (last section, item
7). Part 4: of its three places only place 23 may add to a table that interns,
and with one call only; place 22 may read the table of simples with a coercion,
and adds to none. So the rule of section 2 for two additions to one table is
used at no place.

`Code.free_names` IS COMPUTED, AND WRITES CACHES. It is not a stored field. The
record of a piece of code stores the free names of the parameters and of the
body only; the function unions them with the free names of the metadata
(`middle_end/flambda2/terms/code0.ml` 86-90). On the way, and only when the
result types of the code are known, it writes: the cache of free names of each
type that it visits (the mutable field at
`middle_end/flambda2/types/grammar/with_cached_free_names.ml` 19, assigned at
line 32); the three mutable fields of the name abstraction that holds the result
types, when a delayed renaming is waiting
(`middle_end/flambda2/nominal/name_abstraction.ml` 71-73); and, in that same
case, possibly entries of tables that intern. The caches are memos: the value
stored is computed from the head of the type alone. No fresh name is made on
this path. Shown in `part-3.md` (F6 and Part D) and in `part-2.md` (its Part 3,
where the same function is reached as `Non_constructed_code.free_names`). Places
9, 10, 13 and 14.

THE COUNTS OF OCCURRENCES ARE GUARDED BY ASSERTIONS. In a set of free names, the
count of the occurrences of one name is packed in 20 bits for each name mode.
Three assertions (`middle_end/flambda2/nominal/name_occurrences.ml` 106, 111
and 115) fail when a count would pass 1 048 575. So a function that computes
free names can stop with `Assert_failure`. That is why the places of free names
are COMMUTE, FAILURES ORDERED and not COMMUTE. Shown in `part-3.md` (the third
fact before the entries; N2 to N4), `part-2.md` (the operations of
`Name_occurrences`) and `part-4.md` (the entries of `Name_occurrences`). Places
9, 10, 12, 13, 14 and 16. At places 19 and 22 the counts stay small: the count
is 1 at place 19, and the primitives of place 22 have one or two arguments
(`part-4.md`).

THE FUNCTIONS THAT MAKE A FRESH NAME. Each advances a counter:
`Variable.create`, `Variable.rename`; `Symbol.manufacture`; `Code_id.create`,
`Code_id.rename`; `Continuation.create`, `Continuation.rename`; the `create` and
`rename` of a slot (`Function_slot.create`, `Value_slot.create`);
`Apply_cont_rewrite_id.create`; `Named_rewrite_id.create`. This is the list of
T8 of `part-4.md`; T3 there names functions that call these (among them
`import_and_rename`, of variables and of continuations). A place that calls one
of them in a field is REPORT. T8 also lists: the calls that touch no table and
no counter and cannot fail (`Simple.var`, `Simple.symbol`, `Simple.const`,
`Simple.name`, `Name.var`, `Name.symbol`; the comparison, equality and hash of
every identifier that is an integer (not those of a slot, which call those of
its compilation unit: section 8); `Value_slot.kind` and the other projections of
a slot; `Bound_var.create`; `Bound_pattern.singleton`; `Named.create_simple`;
`Named.create_prim`); the calls that read a table and write none; and the calls
that may add to a table, with no counter (every maker of a constant;
`Symbol.create` and its kin; `Simple.with_coercion` and
`Simple.apply_coercion`).

## 7. What these facts are for

A proof about the port that exchanges two calls needs, for each of the two, what
it writes, what it reads, where it can fail and what it allocates. The entries
of the four parts are the first such contracts. They are readings, not proofs:
nothing was built or run, and section 8 has their limits.

## 8. What was not read, and doubts

The lists of the four parts, each item once, in groups. Each item says which
places it touches. Where a part says that a verdict does not rest on an item,
that is said here too.

THE STANDARD LIBRARY.

- The bodies of the functions of OCaml's standard library were not read, but for
  the lines named below; W, R, F and A are from the documented behaviour. Each
  part names the functions that it uses as leaves: `part-1.md` (last section,
  item 6), `part-2.md` (item 1), `part-3.md` (Part E, and item 5), `part-4.md`
  (item 1). Assumed in part 2: the functions of `List`, `ListLabels`, `Array`,
  `Map.Make`, `Set.Make` and `Hashtbl.Make` that are used have no effect of
  their own beyond calling the function that they are given, and, for `Hashtbl`,
  changing the table that they are given. Read: `stdlib/map.ml` 77-141 (part 2),
  and 16-150 and 236-470, the first of the two copies of the functor (part 3);
  of `stdlib/hashtbl.ml`, the lines that the entries B1 and B2 of part 3 give.
  Places: every place whose entries name such a leaf; the entries of part 1 name
  none for places 1, 4 and 17.
- The primitive that counts leading zeros (`int_clz`,
  `middle_end/flambda2/algorithms/patricia_tree.ml` 19-21) is in C, or a
  built-in. Its body was not read; its declaration says no allocation, no effect
  and no coeffect. Places: 5, 6 and 18, where a field calls the `add` of a
  Patricia tree; parts 2, 3 and 4 name it also for the trees inside the
  functions called.

CODE THAT RUNS ONLY ON A PATH THAT FAILS.

- Printers. Not read: `Continuation.print`, `Continuation_uses_env.print`,
  `Continuation_uses.print`, `Downwards_env.print`, `Flambda2_types.print` and
  `Typing_env.print` (place 18; they read the tables of identifiers and flags of
  colours). Not read: the printers on the failure path of `Bound_static.create`,
  which are `Misc.Sexp`, `Function_slot.Lmap.print`, `Flambda_colours` and
  `Format` (places 8 and 10; `Symbol.print` and `Code_id.print` were read: they
  read the tables of symbols and of code identifiers). Not read: `Named.print`
  and all that it calls, the `print` of the data of a table, `Flambda_colours`
  and `Flambda_features` (places 19, 22 and 23). They run only when the call is
  already failing.
- Handlers. `Misc.Fatal_error` is an exception, and handlers above the functions
  of a place were not looked for. If a handler catches it and the compilation
  goes on, the second thing that the order chooses at place 10 is the only thing
  that the order could leave behind: memos filled or not, table entries added or
  not (part 2, doubt D). Places: 10.

THE MEET OF TYPES, AND WHAT IT REACHES. Place 18. All in `part-1.md`, last
section.

- `Flambda2_types.meet` is not read to its leaves. Item 1 lists what was not
  read. The counts of places of failure in its entry are from a search, not from
  a reading; so is the statement that no maker of names is in the files of the
  binary algorithm.
- The resolver of `.cmx` files. `Flambda_cmx.load_cmx_file_contents` was read;
  what it calls was not (item 2). Not known: if an import can make fresh names.
- Not decided: whether the meet of `add_continuation_use` can reach
  `Variable.create` at `middle_end/flambda2/types/env/join_env.ml` 729. The
  chain of calls exists; the condition is on the types (item 3).
- That place 18 is reached only with the N-way algorithm rests on: the one
  caller of `Downwards_acc.add_continuation_to_specialize` that a search finds;
  the fatal error at `middle_end/flambda2/simplify/simplify_switch_expr.ml`
  935-939; and the flags not changing during the pass.
  `decide_continuation_specialization` was not read whole (item 4).
- `Flambda2_types.unknown_with_subkind`. Not read in part 1:
  `Reg_width_const.naked_immediate` below `Const.create`, and the modules
  `Target_ocaml_int` and `Tag` with their maps and sets (item 5). The hash and
  the equality of constants are in `part-4.md` (T3, T4).

THE PATH OF A WAITING RENAMING, IN THE FREE NAMES OF CODE. Places 9, 10, 13
and 14.

- Not decided: whether the result types of the code at these places can carry a
  renaming that is not the identity, or a renaming with an import map. It
  depends on the callers, which were not read (part 2, item 5 and doubt A; part
  3, item 3). Both parts give the writes and the failures of that path as
  possible. If neither can happen, `is_fully_static` writes only the caches of
  free names, and the failures of places 9 and 10 reduce to the three assertions
  on counts. The verdicts of places 13 and 14 do not depend on it, because the
  other call of those places is a constructor application.
- Leaves not read on that path. The equality of kinds and the projection of a
  kind with subkind, called by `Bound_parameter.create` (parts 2 and 3; part 1
  has the projection `Flambda_kind.With_subkind.kind`, and part 4 has
  `Flambda_kind.equal`). The functions of sets of value slots and of maps of
  tags, which are the `Set.Make` and `Map.Make` of the standard library through
  `middle_end/flambda2/algorithms/container_types.ml`, and the functions of
  `Hashtbl` (part 2, item 3). The comparison of integers used for tags and
  relations, which the map functions on these paths do not call (part 3, item
  4). Assumed in part 2: comparisons and traversals of immutable data. The
  verdicts of places 9 and 10 do not rest on these being pure. They rest on
  this: the three other calls of the place, all read in full, read one flag that
  only the driver assigns, and otherwise touch no state.
- The writes are memos and interning. They were judged by the rule of section 2:
  no other call of the place reads or writes them. No attempt was made to show
  that a memo can never be observed by later code; the reading says that each
  memo stores what a later reader would compute (part 2, doubt C).

CONDITIONS OF FAILURE THAT WERE NOT DECIDED.

- Whether one symbol can be given to two function slots: by
  `closure_symbols_with_types` (place 8), or by a definition given to
  `create_definition` (place 10). It was treated as possible. It is the only way
  `compute_bound_static` fails, and only with the heavy checks (part 2, doubt
  B). Places: 8 and 10.
- Whether an instance of a compilation unit can have an empty head name or an
  empty parameter name. That is the condition of an exception in the comparison
  of compilation units (`utils/compilation_unit.ml` 91). Part 3 found no check
  that excludes the empty string when such a name is made, and read
  `typing/global_module.ml` at lines 150-170 only (C3, and item 2); part 4 says
  that it is an invariant of how a compilation unit is built. In the comparison
  of slots it needs two different slots with the same stamp whose compilation
  units are not physically the same. It matters only for which failures are
  possible. Places: 12 and 16, and inside `Code.free_names` 13 and 14 (part 3);
  the same line is among the failures of `Compilation_unit.hash` and
  `Compilation_unit.equal`, which place 2 reaches (part 1).
- Whether the matches of `middle_end/flambda2/terms/code_size_v1.ml` are
  complete. Not every match was checked against the definition of its type. They
  are taken as complete because the root `dune` file turns the warnings on in
  its three profiles and makes them errors in two (part 4, item 3). If one were
  not complete, place 22 would have a `Match_failure` among its failures, still
  in one call only. Places: 22.

ASSERTIONS COMPILED IN OR OUT. Some points of failure are assertions. An
assertion is counted as a point of failure; it disappears if assertions are
compiled out (part 2). The build files of the tree were searched for the flag
that removes assertions, and none was found; the file `ocamlopt_flags.sexp` of
the root of the project, which the dune files include, is made at build time, is
not in the tree, and was not read (the file of that name that is in the tree,
`oxcaml/tests/backend/oxcaml_dwarf/ocamlopt_flags.sexp`, is another one). If
assertions were removed, the counts of occurrences would wrap
silently instead of failing; the verdicts would not get worse (part 3, item 1).
Places: 9, 10, 12, 13, 14, 16, 22 and 23.

THE REPLACEMENT OF THE TABLES AFTER A UNIT. `Int_ids.initialise`,
`Int_ids.reset`, `Continuation.initialise` and `Continuation.reset` put a new
empty table in each reference. They are called from
`Flambda2.reset_symbol_tables`, after a unit is compiled, unless
`keep_symbol_tables` is set. The counters are not reset (part 4, T6). An
identifier made before a replacement is not in the new table; a lookup of a
simple with a coercion that is older than the replacement raises `Not_found`
(part 3, B8; part 4, `Simple.pattern_match`). Read: where `reset_symbol_tables`
is called; not the whole of the two functions that call it, nor the drivers.
ASSUMED: no table is replaced while Simplify runs on a unit (part 4, item 8).
Places: 22, where this is the only failure on the path that is not excluded by a
type or by a count; and 12, 13, 14 and 16, through the same lookup. An
observation outside the 23 places: `Const.const_null` is interned once, when the
module is initialised, so after a replacement the Null datum is not in the new
table until something adds it again. Whether any path then looks it up was not
checked (part 4, item 13).

WHAT A BUILD OR A HOST CAN CHANGE.

- Exhaustion of memory or of the stack is counted as a failure nowhere (parts 1,
  2 and 4). Places: all.
- Coverage. The `dune` files of the libraries that part 2 reads allow an
  instrumentation for coverage. In such a build every function writes counters
  of coverage. Not counted (part 2, doubt E).
- The random seed. The integers that represent variables depend on a seed drawn
  once, with `Random.bits`, when the module `Int_ids` is initialised
  (`middle_end/flambda2/identifiers/int_ids.ml` 17-19). It is a constant after
  that, so it is no state for the order of two calls. But the shape of a map of
  simples is not a function of the names alone; and whether the seed is the same
  from one run of the compiler to the next depends on nothing seeding the
  default generator before (no call of `Random.self_init` was found in the
  compiler's own directories). No verdict rests on it (part 2, doubt F; part 4,
  item 5).
- Hosts of 32 bits. The layout of an identifier and the Patricia trees depend on
  the size of an integer. They were read for a host of 64 bits only (part 4,
  item 7).
- The range of `Hashtbl.hash` (below 2^30) is from knowledge of the runtime, not
  from this tree. That it gives the same number for one same 64-bit integer,
  whatever the type at which the integer is seen, is its documented behaviour.
  The collisions of T4 of part 4 rest on it (part 4, item 6). No verdict rests
  on it.

ORDERS THAT OCAML DOES NOT FIX INSIDE THE FUNCTIONS CALLED. They are not among
the 23 places, and were not surveyed completely. Part 3 (item 6) saw three
kinds: an application whose two arguments are both calls (the unions of two
calls of free names); a binding of two things at once, in the union of the map
of the standard library; and a record with two calls, in `Name_occurrences`
(`middle_end/flambda2/nominal/name_occurrences.ml` 453-471). In the functions of
free names the calls involved write nothing but memo cells, so the value
returned and the final state do not depend on these orders; what they can choose
is which of several assertion failures is seen. On the path of a waiting
renaming the calls that can add to a table are bound one after the other in
every function that was read, so the source fixes their order. Part 1 (item 11)
saw one more: `Inlining_arguments.Args.create`, which place 3 calls, builds a
record with a call in each of thirteen fields. Each of the thirteen only reads
one reference of a flag and cannot fail, so they commute.

OTHER THINGS NOT READ.

- Values of modules in the fields (the many `empty`, `none` and so on). Not
  every definition was read; each was checked to be a name that is not applied
  at the place (part 1, item 9). Places: 2, 3 and 4.
- The guards before the records of places 7, 8 and 9 call
  `Static_const_or_code.is_block`, `is_set_of_closures` and `is_code`. Not read,
  and not needed: the exclusion of `Code_not_rebuilt` at places 7 and 8 is in
  `middle_end/flambda2/simplify/rebuilt_static_const.ml` 42-52 itself (part 2,
  item 4).
- Not read for part 4 (item 9): `middle_end/flambda2/algorithms/lmap.ml` (part 2
  reads its lines 80-140); the Datalog column maps, from which the sets and maps
  of `Code_id_or_name` come; `middle_end/flambda2/identifiers/field.ml` 15-119;
  `Set_of_closures.free_names` (part 3 has it: F7) and
  `Static_const_group.free_names`, which `Simplified_named.create` cannot reach;
  `Unit_info.modname`, and `typing/current_unit.ml` beyond its lines 16-44 (used
  by `Variable.create` and `Continuation.create`, not by places 19, 22 and 23;
  part 1 reads lines 16-74, and `parsing/unit_info.ml` 16-36);
  `Compilation_unit.mangle_for_linkage_name` and `Structured_mangling` (used by
  makers of symbols and of code identifiers, not by places 19, 22 and 23);
  `Flambda_features` (part 1 reads the lines of it that its entries give).
- `utils/symbol.ml` was not read for part 3 (the hash and the equality of the
  data of symbols, reached only with an import map); part 4 read it whole.
- The shape of a Patricia tree as a function of its set of keys only: argued,
  not proved (part 4, T7 and item 4). Two maps with the same bindings that are
  made in two orders are equal in structure, but they are not the same blocks: a
  test of physical equality between them can differ.
- The interface files were not checked beyond the ones cited, since an interface
  cannot change a body (part 3, item 8).
- Two things about single places that the verdicts do not rest on. At place 22:
  that the term is always a primitive, and that the fresh variable is made
  before the record, was read from lines 356-388 of the file (part 4, item 11).
  At place 23: the other unboxers of the file intern their poison constants when
  the module is initialised; they are not part of the place (part 4, item 12).

## 9. How a new place is judged

By the same sense. The functions that the new record calls in its fields are
read in the compiler as section 2 says. The verdict is one of the three. The
mark `PORT-GAP(record-order)` of the place says the verdict, and a row is added
to the table of section 4, with the entries of the reading in a part. A place
whose call makes a fresh name, or where the order can change a result or a
state, is REPORT and goes to the human.
