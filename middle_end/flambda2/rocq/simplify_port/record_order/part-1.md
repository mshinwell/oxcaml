# Record order, part 1: places 1, 2, 3, 4, 17 and 18

The reading of the compiler's code for places 1, 2, 3, 4, 17 and 18. `README.md`
of this folder has the question, the sense and the table of places.

Commit read: `4fe46bb689903ead25d346ac9efd3c883821f171` (`git rev-parse HEAD` in
the tree that was read; `git status --porcelain` with optional locks off shows
no change under `middle_end`, `utils`, `driver`, `typing`, `parsing`).

Paths are from the root of the repository.

## Verdicts in short

| Place | Verdict |
|---|---|
| P1 `remove`, `middle_end/flambda2/simplify/env/continuation_uses_env.ml` 145-148 | COMMUTE |
| P2 `create`, `middle_end/flambda2/simplify/env/downwards_acc.ml` 94-112 | REPORT: a fresh continuation is made |
| P3 `create`, `middle_end/flambda2/simplify/env/downwards_env.ml` 245-276 | COMMUTE, FAILURES ORDERED: one call can fail; the order chooses nothing |
| P4 `enter_set_of_closures`, `middle_end/flambda2/simplify/env/downwards_env.ml` 372-402 | COMMUTE |
| P17 `arg_types_by_use_id_for_lifting`, `middle_end/flambda2/simplify/simplify_let_cont_expr.ml` 211-217 | COMMUTE |
| P18 `compute_specialized_continuation`, `middle_end/flambda2/simplify/simplify_let_cont_expr.ml` 1165-1176 | REPORT: a fresh variable can be made, and one function is not read to its leaves |

For P2 and P18 the verdict is REPORT because the rule for a fresh name says so
(`README.md`, section 2). In both places no way was found for the order of the
fields to change a result or a state: in each, all the writes and all the
failures are in ONE field, and the calls of the other fields write nothing and
cannot fail. The details are in the section PLACES.

## Words used below

- "stdlib leaf": a function of OCaml's standard library. Its body was not read.
  W, R, F, A are from its documented behaviour.
- "projection": the body is one field access.
- "value": a name that is not applied at the place. No call happens at the
  place.
- A function "is pure" here means: W none, R none, F none, A none.
- Failures by exhaustion of memory or of the stack are not counted anywhere.

## FUNCTIONS

### Group A: maps keyed by continuations

A fact for all of group A. `Continuation.Map` is the `Map` field of
`Patricia_tree.Make` applied to `Continuation.T`
(`middle_end/flambda2/identifiers/continuation.ml` 158-166).
`Patricia_tree.Make` (`middle_end/flambda2/algorithms/patricia_tree.ml`
2229-2293) takes ONE thing from its argument: a printer. It takes no comparison
function and no hash function. Its `Map` includes `Patricia_tree.Map`
(2186-2223), which includes `Map0` (360-465) and `Tree_operations` applied to
`Map0` (469-2101). A key is the integer of the continuation (`Continuation.t` is
`Table_by_int_id.Id.t`, an integer:
`middle_end/flambda2/identifiers/continuation.ml` 99,
`middle_end/flambda2/algorithms/table_by_int_id.ml` 19-36). The tree functions
compare keys with integer equality and bit operations only. The equality sign in
that file is the integer equality of `utils/int_replace_polymorphic_compare.ml`
1, opened by a flag in `middle_end/flambda2/algorithms/dune`. So no operation of
group A reads the table of continuations.

### F: Continuation.Map.remove
defined: chain above; body `middle_end/flambda2/algorithms/patricia_tree.ml`
794-798 (`remove`) and 778-792 (`remove_tree`)
calls: `Map0.is_value_of` (376), `Map0.descr` (410-414), `Map0.empty` (378),
`Map0.tree_descr` (401-404), `Map0.leaf_key` (385), `Map0.branch_prefix_and_bit`
(389-391), `Map0.branch0` (393), `Map0.branch1` (395), `Map0.of_tree` (372),
`Map0.branch` (382-383), `unpack` (45-49), `match_prefix` (66), `mask` (62),
`zero_bit` (53), `branch_right_nonempty` (627-631), `branch_left_nonempty`
(633-637). Each is a LEAF: body read; it is integer arithmetic on the key, a
match on a constructor, or the construction of one immutable block.
W: none
R: none
F: none. No raise and no assertion in the bodies read; the matches are complete;
the recursion goes down one level of the tree per call and the depth of a tree
is at most the number of bits of a key.
A: none. The result is an immutable tree that shares with the argument, or the
argument itself when the key is absent.
read: `middle_end/flambda2/algorithms/patricia_tree.ml` 17-95, 360-465, 603-646,
778-798, 2186-2293; `middle_end/flambda2/identifiers/continuation.ml` 17-181;
`middle_end/flambda2/algorithms/dune`;
`utils/int_replace_polymorphic_compare.ml` 1-8

### F: Continuation.Map.add
defined: chain above; body `middle_end/flambda2/algorithms/patricia_tree.ml`
703-707 (`add`) and 684-701 (`add_tree`)
calls: the leaves of `remove` above, and `Map0.leaf` (380), `branch_non_empty`
(639-641), `join_non_empty` (667-672), `branching_bit` (59), `highest_bit` (56),
`pack` (51), `int_clz` (external, 19-21). `int_clz` is a LEAF: a primitive in C,
declared without allocation, effects or coeffects; its body was not read.
W: none
R: none
F: none (same reasons as `remove`)
A: none (a new immutable tree)
read: `middle_end/flambda2/algorithms/patricia_tree.ml` 17-95, 360-465, 603-707

### F: Continuation.Map.find_opt
defined: chain above; body `middle_end/flambda2/algorithms/patricia_tree.ml`
1742-1745, with `find_tree` 1260-1270
calls: `Map0.descr`, `Map0.tree_descr`, `Map0.leaf_key`, `Map0.leaf_datum`
(387), `Map0.branch_prefix_and_bit`, `Map0.branch0`, `Map0.branch1`, `unpack`,
`match_prefix`, `zero_bit`, `Or_null.this` and `Or_null.null`
(`middle_end/flambda2/algorithms/or_null.ml` 47-49), `Or_null.to_option`
(`middle_end/flambda2/algorithms/or_null.ml` 55). All LEAF, bodies read.
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/algorithms/patricia_tree.ml` 1260-1277, 1737-1745;
`middle_end/flambda2/algorithms/or_null.ml` 29-57

### F: Continuation.Map.update
defined: chain above; body `middle_end/flambda2/algorithms/patricia_tree.ml`
769-776, with `update_tree` 737-767
calls: the leaves of `add` and `remove`; and the function that the caller gives,
once.
W: none of its own
R: none of its own
F: none of its own
A: none
read: `middle_end/flambda2/algorithms/patricia_tree.ml` 737-776

### Group B: the calls of P2

### F: Flow.Acc.empty
defined: `Flow.Acc` is `Flow_acc` (`middle_end/flambda2/simplify/flow/flow.ml`
15); body `middle_end/flambda2/simplify/flow/flow_acc.ml` 29-41
calls: `Continuation.create` (with a name given, 30-32). The fields of the
record that it returns are that continuation and values
(`Continuation.Map.empty`, `Lifted_constant_state.empty`, the empty list).
W: what `Continuation.create` writes, at each call
R: what `Continuation.create` reads
F: what `Continuation.create` can fail with
A: it makes a FRESH NAME, a continuation. The record that it returns is
immutable.
read: `middle_end/flambda2/simplify/flow/flow.ml` 1-16;
`middle_end/flambda2/simplify/flow/flow_acc.ml` 14-95

### F: Continuation.create
defined: `middle_end/flambda2/identifiers/continuation.ml` 109-122
calls: `Option.value` (stdlib leaf); `Current_unit.get_cu_exn`; `next_stamp`
(the closure of `middle_end/flambda2/identifiers/continuation.ml` 21-25, LEAF:
it adds one to a reference and returns the content);
`Flambda_features.debug_flambda2`; `Format.asprintf` (stdlib leaf; called only
when the debug flag is set; it formats to a new string);
`Continuation.Table.add`, which is
`Table_by_int_id.Make(Continuation.Data).add`.
W: (1) the counter of stamps of continuations: the reference at
`middle_end/flambda2/identifiers/continuation.ml` 22, plus one at each call
(line 24). (2) the table of continuations: the hash table held by the reference
`grand_table_of_continuations`
(`middle_end/flambda2/identifiers/continuation.ml` 103) gets one new entry at
each call (line 122).
R: the current compilation unit (`typing/current_unit.ml` 18); the counter of
stamps; the flag `Oxcaml_flags.Flambda2.debug` (`driver/oxcaml_flags.ml` 202);
the table of continuations.
F: `typing/current_unit.ml` 33, when no compilation unit is set; and the
failures of `Table_by_int_id.Make.add` below.
A: a FRESH NAME: a continuation. How its identifier is chosen: the hash of the
pair (hash of the compilation unit, stamp), with the flags of continuations in
the top bits; if another entry of the table has that identifier, the next free
identifier is taken. So the identifier depends on the counter and on what the
table holds.
read: `middle_end/flambda2/identifiers/continuation.ml` 17-181

### F: Current_unit.get_cu_exn
defined: `typing/current_unit.ml` 30-33
calls: `Current_unit.get_cu` (24-25), which calls `Current_unit.get` (21-22:
reads the reference), `Option.map` (stdlib leaf) and `Unit_info.modname`
(`parsing/unit_info.ml` 34, a projection); `Misc.fatal_error` on the failure
path.
W: none (on failure, a message on the standard error channel)
R: the reference `current_unit`, `typing/current_unit.ml` 18
F: `typing/current_unit.ml` 33, when the reference holds no unit
A: none
read: `typing/current_unit.ml` 16-74; `parsing/unit_info.ml` 16-36

### F: Misc.fatal_error and Misc.fatal_errorf
defined: `utils/misc.ml` 26 and 20-24
calls: `Format.kfprintf` on `Format.err_formatter` (stdlib leaf), then raises
the exception `Misc.Fatal_error` (line 18)
W: the standard error channel and the state of the standard error formatter
R: none
F: always
A: none
read: `utils/misc.ml` 16-31

### F: Flambda_features.debug_flambda2
defined: `middle_end/flambda2/ui/flambda_features.ml` 17
calls: LEAF (reads one reference)
W: none
R: the flag `Oxcaml_flags.Flambda2.debug`, `driver/oxcaml_flags.ml` 202
F: none
A: none
read: `middle_end/flambda2/ui/flambda_features.ml` 15-60

### F: Table_by_int_id.Make(E).add  (here `Continuation.Table.add`)
defined: `middle_end/flambda2/algorithms/table_by_int_id.ml` 75-107; the functor
is 38-127; the instance for continuations is
`middle_end/flambda2/identifiers/continuation.ml` 101
calls: `Table_by_int_id.Id.create` (28-31), `Table_by_int_id.Id.next` (35),
`Table_by_int_id.Id.flags` (33), `E.hash`, `E.equal`, and `find_opt`, `find`,
`add` of the module `HT`. `HT` is OCaml's `Hashtbl.Make` (stdlib leaf) applied
at 50-63 to integer keys, a mixing function of the integer (57-60) and physical
equality of integers (62). On the failure path: `E.print`, `Misc.fatal_errorf`.
W: the hash table given: one new entry, unless an equal element is already there
R: the hash table given
F: 29-30, flags out of range: cannot happen here, because the flags of each kind
of identifier are a constant in range
(`middle_end/flambda2/identifiers/continuation.ml` 19 and 63;
`middle_end/flambda2/identifiers/int_ids.ml` 31-39). 99, when no identifier is
free after a full round of the search. Assertions at 91, 103, 106 on the flags.
And the failures of `E.hash` and `E.equal`.
A: none (the result is an integer)
How the identifier of a new entry is chosen: from `E.hash` of the element, with
the flags in the top bits (line 76). If a DIFFERENT element already has that
identifier, the function tries the following identifiers one after the other
until one is free or holds an equal element (85-107). So the identifier is from
the data alone ONLY when no two different elements have the same hash; with such
a collision it depends on which element was added first. This is a fact for
every table of identifiers of Flambda 2 (constants, variables, symbols, simples
with a coercion, code identifiers, continuations): all are instances of this
functor.
read: `middle_end/flambda2/algorithms/table_by_int_id.ml` 17-127

### F: Continuation.Data.hash and Continuation.Data.equal
defined: `middle_end/flambda2/identifiers/continuation.ml` 74-75 and 77-96
calls: `Hashtbl.hash` (stdlib leaf, no seed), `Compilation_unit.hash`;
`Int.equal` (stdlib leaf), `Compilation_unit.equal`
W: none
R: none
F: those of `Compilation_unit.hash` and `Compilation_unit.equal`
A: none
read: `middle_end/flambda2/identifiers/continuation.ml` 55-97

### F: Compilation_unit.hash and Compilation_unit.equal
defined: `utils/compilation_unit.ml` 505-512 and 499; `equal` calls `compare`,
336-362
calls: `descr` (284-301), `Name.hash` (78) and `Prefix.hash` (161), both
`Hashtbl.hash` (stdlib leaf); `Name.compare` (74, `String.compare`),
`Prefix.compare` (159), `List.compare`, `ListLabels.map` (stdlib leaves);
`Name.of_string` (89-92); `convert_arguments` (278-282), which calls
`Name.of_parameter_name` (98-99) and `Global_module.Parameter_name.to_string`
(`typing/global_module.ml` 8, the identity).
W: none
R: none
F: `utils/compilation_unit.ml` 286, an assertion on the tag of the block that
represents the unit; 91, an exception of the module when the head name of a unit
is the empty string (reached from 299 and 275).
A: none
read: `utils/compilation_unit.ml` 33-122, 144-166, 202-432, 494-513;
`typing/global_module.ml` 3-27

### F: Are_lifting_conts.no_lifting
defined: `middle_end/flambda2/simplify/are_lifting_conts.ml` 32
calls: LEAF (applies one constructor)
W: none
R: none
F: none
A: none (one immutable block)
read: `middle_end/flambda2/simplify/are_lifting_conts.ml` 16-68

### F: Flambda_features.Expert.cont_lifting_budget
defined: `middle_end/flambda2/ui/flambda_features.ml` 362-364
calls: `Flambda_features.Expert.with_default` (316-323);
`Oxcaml_flags.Flambda2.Expert.default_for_opt_level` (`driver/oxcaml_flags.ml`
407-408); `Oxcaml_flags.flags_by_opt_level` (`driver/oxcaml_flags.ml` 183-189).
All bodies read: matches and field accesses on constant records
(`driver/oxcaml_flags.ml` 367-405).
W: none
R: the reference `Oxcaml_flags.Flambda2.Expert.cont_lifting_budget`
(`driver/oxcaml_flags.ml` 419); and, when that flag is not set, the reference
`Oxcaml_flags.opt_level` (`driver/oxcaml_flags.ml` 173)
F: none
A: none
read: `middle_end/flambda2/ui/flambda_features.ml` 315-369;
`driver/oxcaml_flags.ml` 160-205, 336-422

### Group C: the calls of P3

### F: Inlining_state.default
defined: `middle_end/flambda2/terms/inlining_state.ml` 29-30
calls: `Inlining_arguments.create`
W: none
R: what `Inlining_arguments.create` reads
F: none
A: none (immutable records)
read: `middle_end/flambda2/terms/inlining_state.ml` 17-65

### F: Inlining_arguments.create
defined: `middle_end/flambda2/terms/inlining_arguments.ml` 329, which calls
`Args.create`, 255-270
calls: the thirteen functions of `Flambda_features.Inlining` below, each with
the round
W: none
R: thirteen references of flags (next entry)
F: none
A: none
read: `middle_end/flambda2/terms/inlining_arguments.ml` 16-331

### F: Flambda_features.Inlining.max_depth, max_rec_depth, call_cost ..
heading: F: Flambda_features.Inlining.max_depth, max_rec_depth, call_cost,
alloc_cost, prim_cost, branch_cost, indirect_call_cost, poly_compare_cost,
small_function_size, large_function_size, small_functor_size,
large_functor_size, threshold
defined: `middle_end/flambda2/ui/flambda_features.ml` 228-237, 239-242, 244-247,
249-252, 254-257, 259-262, 264-267, 269-272, 274-277, 279-282, 284-287, 289-292,
294-297
calls: for a round, each calls `Clflags.Int_arg_helper.get` or
`Clflags.Float_arg_helper.get` on the content of one reference. `max_depth` then
does integer arithmetic.
W: none
R: the references `max_depth`, `max_rec_depth`, `call_cost`, `alloc_cost`,
`prim_cost`, `branch_cost`, `indirect_call_cost`, `poly_compare_cost`,
`small_function_size`, `large_function_size`, `small_functor_size`,
`large_functor_size`, `threshold` of `Oxcaml_flags.Flambda2.Inlining`,
`driver/oxcaml_flags.ml` 480-502
F: none
A: none
read: `middle_end/flambda2/ui/flambda_features.ml` 205-305;
`driver/oxcaml_flags.ml` 437-560

### F: Clflags.Int_arg_helper.get and Clflags.Float_arg_helper.get
defined: `utils/clflags.ml` 31-35 and 36-40 apply `Arg_helper.Make`; the body of
`get` is `utils/arg_helper.ml` 116-125. The keys are integers; the map of keys
is OCaml's `Map.Make` on OCaml's `Int` (`utils/clflags.ml` 19-29, a module named
`Numbers` that is local to that file; it is not `utils/numbers.ml`).
calls: `find` of that map (stdlib leaf). Its exception for an absent key is
caught at both places (119 and 125).
W: none
R: none (the caller reads the reference)
F: none
A: none
read: `utils/arg_helper.ml` 17-127; `utils/clflags.ml` 16-41

### F: Inlining_history.Tracker.empty
defined: `middle_end/flambda2/terms/inlining_history.ml` 221-222
calls: `Inlining_history.Absolute.empty` (39; LEAF, it builds a pair).
`Inlining_history.Relative.empty` is a value (137).
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/terms/inlining_history.ml` 13-42, 130-139, 213-255

### F: Specialization_cost.cannot_specialize
defined: `middle_end/flambda2/simplify/specialization_cost.ml` 63
calls: LEAF (applies one constructor to a record of one field)
W: none
R: none
F: none
A: none (one immutable block)
read: `middle_end/flambda2/simplify/specialization_cost.ml` 16-202

### Group D: the calls of P4

### F: Flambda2_types.Typing_env.closure_env ..
heading: F: Flambda2_types.Typing_env.closure_env (the `TE.closure_env` of
`middle_end/flambda2/simplify/env/downwards_env.ml`)
defined: `TE` is `Flambda2_types.Typing_env`
(`middle_end/flambda2/simplify/env/downwards_env.ml` 22).
`middle_end/flambda2/types/flambda2_types.ml` 17-18 includes `Typing_env`; lines
19-118 do not define `closure_env` again. Body:
`middle_end/flambda2/types/env/typing_env.ml` 1079-1080.
calls: `Typing_env.increment_scope` (364-371), which calls
`Typing_env.current_scope` (344), `One_level.scope` (77, projection),
`One_level.create` (72, builds a record), `One_level.just_after_level` (81,
projection), `Scope.next` (`middle_end/flambda2/term_basics/scope.ml` 21,
integer plus one). `Typing_env_level.empty` is a value
(`middle_end/flambda2/types/env/typing_env_level.ml` 89-94).
W: none
R: none
F: none
A: none (new immutable records)
read: `middle_end/flambda2/types/env/typing_env.ml` 17-135, 344-371, 1079-1080;
`middle_end/flambda2/types/flambda2_types.ml` 17-174;
`middle_end/flambda2/term_basics/scope.ml` 17-47;
`middle_end/flambda2/types/env/typing_env_level.ml` 89-100

### Group E: the calls of P17

### F: Downwards_env.typing_env ..
heading: F: Downwards_env.typing_env (the `DE.typing_env` of P17 and of
`add_continuation_use`)
defined: `middle_end/flambda2/simplify/env/downwards_env.ml` 284. `DE` is
`Downwards_env` (`middle_end/flambda2/simplify/simplify_import.ml` 43;
`middle_end/flambda2/simplify/env/continuation_uses_env.ml` 17).
calls: LEAF (projection)
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/simplify/env/downwards_env.ml` 17-130, 240-420

### F: Flambda2_types.alias_type_of
defined: `middle_end/flambda2/types/flambda2_types.ml` 140 includes
`Type_grammar`; no later include of that file defines the name again (a search
of `middle_end/flambda2/types` finds one definition at top level). Body:
`middle_end/flambda2/types/grammar/type_grammar.ml` 4314-4330.
calls: `Type_descr.create_equals`
(`middle_end/flambda2/types/grammar/type_descr.ml` 199; LEAF, it wraps the
simple in two constructors)
W: none
R: none
F: none (a complete match on the kind)
A: none. The type that it returns is immutable. An alias type has no head, so it
has no cache field (compare `Flambda2_types.unknown_with_subkind` below).
read: `middle_end/flambda2/types/grammar/type_grammar.ml` 4300-4345;
`middle_end/flambda2/types/grammar/type_descr.ml` 17-311

### F: Flambda_kind.With_subkind.kind  (the `KS.kind` of P17)
defined: `KS` is `Flambda_kind.With_subkind`
(`middle_end/flambda2/simplify/simplify_import.ml` 49); body
`middle_end/flambda2/kinds/flambda_kind.ml` 904
calls: LEAF (projection)
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/kinds/flambda_kind.ml` 855-912

### F: Bound_parameter.kind
defined: `middle_end/flambda2/bound_identifiers/bound_parameter.ml` 79
calls: LEAF (projection)
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/bound_identifiers/bound_parameter.ml` 17-101

### Group F: the calls of P18

### F: One_continuation_use.use_kind, id, env_at_use, arg_types
defined: `middle_end/flambda2/simplify/env/one_continuation_use.ml` 40, 38, 44,
42
calls: LEAF (projections)
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/simplify/env/one_continuation_use.ml` 17-49

### F: One_continuation_use.create
defined: `middle_end/flambda2/simplify/env/one_continuation_use.ml` 27
calls: LEAF (builds a record)
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/simplify/env/one_continuation_use.ml` 17-49

### F: Continuation_uses_env.add_continuation_use ..
heading: F: Continuation_uses_env.add_continuation_use (the
`CUE.add_continuation_use` of P18)
defined: `CUE` is `Continuation_uses_env`
(`middle_end/flambda2/simplify/simplify_import.ml` 41); body
`middle_end/flambda2/simplify/env/continuation_uses_env.ml` 65-104
calls, in the order of the body: `Continuation.Map.find_opt`; on failure
`Misc.fatal_errorf` with `Continuation.print` and `Continuation_uses_env.print`;
`Downwards_env.typing_env`; `Flambda2_types.Typing_env.machine_width`
(`middle_end/flambda2/types/env/typing_env.ml` 362, projection);
`Flambda_arity.unarized_components`; `Misc.Stdlib.List.fold_left_map2` with a
function that calls, for each argument, `Flambda2_types.unknown_with_subkind`
and `Flambda2_types.meet`; `Downwards_env.with_typing_env`
(`middle_end/flambda2/simplify/env/downwards_env.ml` 542, a copy of a record);
`One_continuation_use.create`; `Continuation.Map.update` with a function that
calls `Continuation_uses.create` and `Continuation_uses.add_use`.
W: none of its own. Through `Flambda2_types.meet` and
`Flambda2_types.unknown_with_subkind`: see their entries (a counter and a table
of variables, tables of simples and of constants, caches in types, the state of
the loader of `.cmx` files, the standard error channel on failure).
R: through the same two functions: flags, the current compilation unit, tables
of identifiers.
F: `middle_end/flambda2/simplify/env/continuation_uses_env.ml` 69-72, when no
arity is recorded for the continuation; `utils/misc.ml` 279, when the list of
types of arguments and the arity have different lengths; the failures of
`Flambda2_types.meet` and of `Flambda2_types.unknown_with_subkind`;
`middle_end/flambda2/simplify/env/continuation_uses.ml` 45-47, when the arity of
the use and the arity of the continuation differ.
A: it can make FRESH NAMES (variables), through `Flambda2_types.meet`.
read: `middle_end/flambda2/simplify/env/continuation_uses_env.ml` 17-167

### F: Misc.Stdlib.List.fold_left_map2
defined: `utils/misc.ml` 272-281
calls: the function given; `List.rev` (stdlib leaf)
W: none of its own
R: none of its own
F: 279, when the two lists have different lengths
A: none
read: `utils/misc.ml` 270-281

### F: Flambda_arity.unarized_components
defined: `middle_end/flambda2/kinds/flambda_arity.ml` 186; it maps
`Component.component` (62-63, a projection of a constructor)
calls: `List.map` (stdlib leaf)
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/kinds/flambda_arity.ml` 17-200

### F: Flambda2_types.unknown_with_subkind
defined: `middle_end/flambda2/types/flambda2_types.ml` 141 includes
`More_type_creators`; body
`middle_end/flambda2/types/grammar/more_type_creators.ml` 490-632. It has an
optional argument; the caller does not give it, so its default is computed at
each call: `Alloc_mode.For_types.unknown`
(`middle_end/flambda2/bound_identifiers/alloc_mode.ml` 45-48), which calls
`Flambda_features.stack_allocation_enabled`
(`middle_end/flambda2/ui/flambda_features.ml` 371), which reads
`Config.stack_allocation`, a constant of the build.
calls: `Flambda_kind.With_subkind.kind`, `non_null_value_subkind`, `nullable`
(projections, `middle_end/flambda2/kinds/flambda_kind.ml` 904-908);
`More_type_creators.these_naked_immediates` (64) and
`Type_grammar.these_naked_immediates`
(`middle_end/flambda2/types/grammar/type_grammar.ml` 4428-4434), which can call
`Type_grammar.this_naked_immediate` (4392-4393), which calls
`Reg_width_const.naked_immediate`; `More_type_creators.variant_non_null`
(295-308); `More_type_creators.immutable_block_non_null` (246-259);
`More_type_creators.mutable_array_non_null` (486-488);
`Type_grammar.Row_like_for_blocks.create_exactly_multiple` (4133-4149) and
`create` (4075-4116) with `check_field_tys` (4055-4073);
`Type_grammar.Head_of_kind_value_non_null.create_variant` (4961-4963) and
`create_array_with_contents` (5000-5001); `Type_grammar.create_from_head_value`
(4860), which calls `Type_descr.create`
(`middle_end/flambda2/types/grammar/type_descr.ml` 197) and
`With_cached_free_names.create`
(`middle_end/flambda2/types/grammar/with_cached_free_names.ml` 22); itself, for
the fields of a variant; `Tag.Scannable.Map.map`, `Tag.Scannable.Map.fold`,
`Tag.Map.add`, `Tag.Map.map`, `Tag.Scannable.to_tag`, `Target_ocaml_int.of_int`,
`Target_ocaml_int.of_int_option`, `Target_ocaml_int.Set.get_singleton`,
`Target_ocaml_int.Set.is_empty` (bodies NOT read).
W: it can add an entry to the table of constants
(`middle_end/flambda2/identifiers/int_ids.ml` 366; the add is at 374), when the
subkind is a variant with exactly one constant constructor. That table interns:
see `Table_by_int_id.Make(E).add`.
R: the flag `Clflags.flambda_invariant_checks`, through
`Flambda_features.check_invariants`
(`middle_end/flambda2/ui/flambda_features.ml` 161-164; used at
`middle_end/flambda2/types/grammar/type_grammar.ml` 4056); the table of
constants; `Config.stack_allocation`.
F: `middle_end/flambda2/types/grammar/more_type_creators.ml` 251, a block of
floats too long for the target;
`middle_end/flambda2/types/grammar/type_grammar.ml` 4070-4072, a field whose
kind does not match the shape (only with the heavy invariant checks on).
A: for a kind of values, the type that it returns has a head with a cache field
that is mutable (`middle_end/flambda2/types/grammar/with_cached_free_names.ml`
17-22). For the other kinds it returns a value of a module.
read: `middle_end/flambda2/types/grammar/more_type_creators.ml` 17-130, 196-320,
476-637; `middle_end/flambda2/types/grammar/type_grammar.ml` 3978-4160,
4390-4434, 4856-4862, 4956-5002;
`middle_end/flambda2/types/grammar/type_descr.ml` 17-311;
`middle_end/flambda2/types/grammar/with_cached_free_names.ml` 17-79;
`middle_end/flambda2/bound_identifiers/alloc_mode.ml` 15-55;
`middle_end/flambda2/identifiers/int_ids.ml` 361-431

### F: Flambda2_types.meet
defined: `middle_end/flambda2/types/flambda2_types.ml` 143 includes `Meet`; body
`middle_end/flambda2/types/meet.ml` 17-29. It chooses by
`Flambda_features.use_n_way_join` (`middle_end/flambda2/ui/flambda_features.ml`
79-84, which calls `join_algorithm`, 66-77, and `match_in_match`, 57-59):
- the N-way algorithm: `Meet_and_n_way_join.meet`,
  `middle_end/flambda2/types/meet_and_n_way_join.ml` 3148-3160;
- the binary algorithm: `Meet_and_join.meet`,
  `middle_end/flambda2/types/meet_and_join.ml` 2509-2521.
The default flag is the binary algorithm (`driver/oxcaml_flags.ml` 212). When
the flag of match-in-match is set, `join_algorithm` answers the N-way algorithm
(`middle_end/flambda2/ui/flambda_features.ml` 66-74).
calls: NOT READ TO ITS LEAVES. The two algorithms and what they use are about
twenty thousand lines (`middle_end/flambda2/types`). What was read, and what was
found, is this.
1. FRESH VARIABLE, N-way algorithm. The chain of calls, each step read. Write MN
   for `middle_end/flambda2/types/meet_and_n_way_join.ml`, ME for
   `middle_end/flambda2/types/env/meet_env.ml`, JE for
   `middle_end/flambda2/types/env/join_env.ml`.
   - `Meet_and_n_way_join.meet` (MN 3148-3160) calls the inner `meet` (MN 1057).
   - The inner `meet` calls `Meet_env.meet_type` (ME 529-531), which calls
     `Meet_env.meet` (ME 442-526).
   - `Meet_env.meet` reaches `meet_expanded_head` (MN 1076-1079): directly (ME
     480), or through `add_concrete_equation_on_canonical_name` (ME 111-139, the
     call at 126).
   - `meet_expanded_head` calls `meet_expanded_head0` (MN 1081-1132). For two
     types of values that calls `meet_head_of_kind_value` (MN 1134-1163), which
     ALWAYS calls `meet_disjunction` (MN 265-392; the call at MN 1161).
   - When neither side of the disjunction is bottom, `meet_disjunction` calls
     `Join_env.cut_and_n_way_join` (the call at MN 347; body JE 1932-1959).
   - Then `cut_and_n_way_join0` (JE 1788-1802 and 1715-1786),
     `join_aliases_into_bindings` (JE 1220-1229),
     `import_or_delay_n_way_join_type` (JE 1034-1047),
     `add_equals_in_joined_envs` (JE 1074-1091), `add_alias_of_existential` (JE
     968-982), `existential_for_these_canonicals` (JE 952-966),
     `Join_env.Bindings_in_target_env.existential_for_these_simples` (JE
     723-738).
   - The last one calls `Variable.create` at JE 729.
   The same join is also called from `meet_row_like` (MN 394 and after; the call
   at MN 449). The comments of `meet_disjunction` (MN 270, 353-356) say that new
   variables can come from the two sides.
   The condition for JE 729: a variable of the environment has, in every
   environment that is joined, a new alias equation; and
   `n_way_join_canonical_simples` (JE 1002-1032) finds no canonical simple that
   is shared by all; and no variable was already made for that set of simples.
   Not decided from the code: whether the meet of `add_continuation_use` can
   meet this condition. It depends on the types.
2. Binary algorithm: a search for the makers of names (`Variable.create`,
   `Variable.rename`, `Symbol.create`, `Continuation.create`,
   `Continuation.rename`, `Code_id.create`, `Code_id.rename`, any `rename`, any
   `import_and_rename`) finds NONE in `middle_end/flambda2/types/meet.ml`,
   `middle_end/flambda2/types/meet_and_join.ml`,
   `middle_end/flambda2/types/env/meet_env.ml`,
   `middle_end/flambda2/types/env/typing_env.ml`,
   `middle_end/flambda2/types/env/aliases.ml`,
   `middle_end/flambda2/types/env/typing_env_level.ml`,
   `middle_end/flambda2/types/env/typing_env_extension.ml`,
   `middle_end/flambda2/types/env/cached_level.ml`,
   `middle_end/flambda2/types/env/binding_time.ml`,
   `middle_end/flambda2/types/env/code_age_relation.ml`,
   `middle_end/flambda2/types/grammar/type_grammar.ml`,
   `middle_end/flambda2/types/grammar/more_type_creators.ml`,
   `middle_end/flambda2/types/grammar/type_descr.ml`. In
   `middle_end/flambda2/types/expand_head.ml` the one maker (`Variable.rename`,
   line 754) is in `make_suitable_for_environment` (593-804), which no file of
   the meet calls (its callers: `middle_end/flambda2/types/traversals.ml` 1421,
   `middle_end/flambda2/simplify/simplify_set_of_closures.ml` 364,
   `middle_end/flambda2/simplify/env/downwards_env.ml` 833, a test). This is a
   search, not a reading of every body. The binary meet does call the binary
   join (`middle_end/flambda2/types/meet_and_join.ml` 256-378, the call at 372;
   `join` 1723-1823; `join_env_extension` 2481-2506).
3. The resolver. `Typing_env.find_with_binding_time_and_mode'`
   (`middle_end/flambda2/types/env/typing_env.ml` 408-472) calls the function
   `resolver` of the environment (line 431) for a name of another compilation
   unit that the environment does not hold. Other calls of it: 324, 340, 391.
   The meet reaches it through `Typing_env.find`
   (`middle_end/flambda2/types/env/meet_env.ml` 123, 234) and through
   `Typing_env.get_alias_then_canonical_simple_exn`
   (`middle_end/flambda2/types/env/meet_env.ml` 454, 462;
   `middle_end/flambda2/types/env/typing_env.ml` 1001-1032). The resolver is a
   parameter. The one that Simplify gives
   (`middle_end/flambda2/simplify/simplify.ml` 32) is
   `Flambda_cmx.load_cmx_file_contents`
   (`middle_end/flambda2/cmx/flambda_cmx.ml` 28-57). At the first use of a unit
   it reads the `.cmx` file of the unit, writes the mutable fields of the loader
   (`middle_end/flambda2/cmx/flambda_cmx.ml` 24-25, written at 45, 51, 54),
   calls `Exported_offsets.import_offsets` (53) and `Profile.record_call` (39),
   and imports the identifiers of the file into the tables of identifiers
   (`Flambda_cmx_format.import_typing_env_and_code`,
   `middle_end/flambda2/cmx/flambda_cmx_format.ml` 79-129). The bodies below
   `load_cmx_file_contents` were NOT read.
W: (a) the counter of stamps of variables
(`middle_end/flambda2/identifiers/int_ids.ml` 490, plus one at 495) and the
table of variables (`middle_end/flambda2/identifiers/int_ids.ml` 474, the add at
506), by item 1. (b) the table of simples with a coercion
(`middle_end/flambda2/identifiers/int_ids.ml` 727, the add at 820 in
`Simple.with_coercion`, 814-825), for example through `Simple.apply_coercion`
(`middle_end/flambda2/term_basics/simple.ml` 82-87) from
`Typing_env.get_canonical_simple_ignoring_name_mode`
(`middle_end/flambda2/types/env/typing_env.ml` 992-999) and
`Aliases.get_canonical_ignoring_name_mode`
(`middle_end/flambda2/types/env/aliases.ml` 949-955); only when a coercion is
not the identity. (c) the table of constants
(`middle_end/flambda2/identifiers/int_ids.ml` 366, 374), where a type of one
constant is built. (d) the cache of free names of a head of a type: the mutable
field at `middle_end/flambda2/types/grammar/with_cached_free_names.ml` 19,
assigned at 32. The value cached is a function of the head alone: every caller
that can fill the cache gives the function that follows value slots
(`middle_end/flambda2/types/grammar/type_grammar.ml` 439-443, 729-735, 745-843,
2879-3173; a search finds no other caller in `middle_end/flambda2`); the variant
that does not follow value slots does not use the cache (443). (e) by the
resolver: item 3. (f) the standard error channel, on failure only
(`middle_end/flambda2/types/meet.ml` 24-28;
`middle_end/flambda2/types/env/typing_env.ml` 1023;
`middle_end/flambda2/types/env/join_env.ml` 1782).
R: flags: `Oxcaml_flags.Flambda2.join_algorithm` (`driver/oxcaml_flags.ml` 308),
`Oxcaml_flags.Flambda2.match_in_match` (319), `Oxcaml_flags.opt_level` (173),
`Oxcaml_flags.Flambda2.join_depth` (307), `Oxcaml_flags.Flambda2.join_sharing`
(309), `Clflags.flambda_invariant_checks`; the option of the strategy of meet
(`middle_end/flambda2/types/env/meet_env.ml` 29-31: a reference made by
`Oxcaml_args.Extra_options.symbol`, `driver/oxcaml_args.ml` 1914-1924,
1972-1973; the function returned reads the reference, with no memory of an
earlier answer); the current compilation unit
(`middle_end/flambda2/types/env/typing_env.ml` 388, 414); the tables of
identifiers (each match on a simple or a name reads a table).
F: yes, many. Counted by a search for fatal errors, assertions and raises: 61
places in `middle_end/flambda2/types/meet_and_n_way_join.ml`, 18 in
`middle_end/flambda2/types/meet_and_join.ml`, 10 in
`middle_end/flambda2/types/env/meet_env.ml`, 24 in
`middle_end/flambda2/types/env/typing_env.ml`, 33 in
`middle_end/flambda2/types/env/aliases.ml`, 21 in
`middle_end/flambda2/types/env/join_env.ml`, 49 in
`middle_end/flambda2/types/grammar/type_grammar.ml`, 5 in
`middle_end/flambda2/types/expand_head.ml`. Two that were read:
`middle_end/flambda2/types/env/meet_env.ml` 446-449, the two types have
different kinds; `middle_end/flambda2/types/env/typing_env.ml` 416-418, a
variable is not bound in the environment. `middle_end/flambda2/types/meet.ml`
22-29 catches the fatal error, prints the two types and the environment on the
standard error channel, and raises it again.
A: FRESH NAMES (variables) possible, item 1. The types that it returns can hold
cache fields.
read: `middle_end/flambda2/types/meet.ml` 16-40;
`middle_end/flambda2/types/env/meet_env.ml` 17-593;
`middle_end/flambda2/types/meet_and_n_way_join.ml` 245-470, 1057-1200,
3139-3160; `middle_end/flambda2/types/meet_and_join.ml` 17-420, 1723-1830,
2466-2521; `middle_end/flambda2/types/env/join_env.ml` 311-424, 464-518,
634-760, 916-1230, 1419-1465, 1715-1806, 1930-1962;
`middle_end/flambda2/types/env/typing_env.ml` 17-560, 992-1100;
`middle_end/flambda2/types/grammar/type_grammar.ml` 336-520, 726-760, 3845-3872;
`middle_end/flambda2/types/grammar/with_cached_free_names.ml` 17-79;
`middle_end/flambda2/identifiers/int_ids.ml` 14-40, 255-302, 361-431, 469-512,
692-826; `middle_end/flambda2/term_basics/simple.ml` 82-94;
`middle_end/flambda2/cmx/flambda_cmx.ml` 17-73;
`middle_end/flambda2/cmx/flambda_cmx_format.ml` 79-129;
`middle_end/flambda2/ui/flambda_features.ml` 57-93; `driver/oxcaml_args.ml`
1905-1973

### F: Variable.create
defined: `middle_end/flambda2/identifiers/variable.ml` 17 includes
`Int_ids.Variable`; body `middle_end/flambda2/identifiers/int_ids.ml` 508-511,
which calls `create_in_compilation_unit`, 492-506
calls: `Current_unit.get_cu_exn`; `Option.is_some` (stdlib leaf);
`Table_by_int_id.Make(Variable_data).add` (the instance at
`middle_end/flambda2/identifiers/int_ids.ml` 472), with `Variable_data.hash`
(276-278) and `Variable_data.equal` (280-301). `Variable_data.hash` calls
`hash2` (23-27), which uses `hash_seed` (17-19), a value made once, when the
module starts, from `Random.bits` (stdlib leaf).
W: the counter of stamps of variables, the reference at
`middle_end/flambda2/identifiers/int_ids.ml` 490, plus one at each call (495);
the table of variables, held by the reference at 474, one new entry at each call
(506)
R: the current compilation unit; the counter; the table; `hash_seed`
F: `typing/current_unit.ml` 33; the failures of `Table_by_int_id.Make(E).add`
A: a FRESH NAME: a variable
read: `middle_end/flambda2/identifiers/variable.ml` 17-32;
`middle_end/flambda2/identifiers/int_ids.ml` 14-40, 255-302, 469-512

### F: Continuation_uses.create
defined: `middle_end/flambda2/simplify/env/continuation_uses.ml` 27
calls: LEAF (builds a record)
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/simplify/env/continuation_uses.ml` 17-158

### F: Continuation_uses.add_use
defined: `middle_end/flambda2/simplify/env/continuation_uses.ml` 39-59
calls: `One_continuation_use.arg_types`; `Flambda2_types.arity_of_list`
(`middle_end/flambda2/types/grammar/more_type_creators.ml` 482-484), which calls
`Type_grammar.kind` (`middle_end/flambda2/types/grammar/type_grammar.ml`
3851-3867, a match), `Flambda_kind.With_subkind.anything`
(`middle_end/flambda2/kinds/flambda_kind.ml` 894-897, which calls `create`,
871-892; with the arguments that `anything` gives, `create` does not reach its
two fatal errors) and `Flambda_arity.create_singletons`
(`middle_end/flambda2/kinds/flambda_arity.ml` 151);
`Flambda_arity.equal_ignoring_subkinds`
(`middle_end/flambda2/kinds/flambda_arity.ml` 172-173), which calls
`Component.equal_ignoring_subkinds` (25-32), `Misc.Stdlib.List.equal`
(`utils/misc.ml` 138-142), `Flambda_kind.With_subkind.erase_subkind`
(`middle_end/flambda2/kinds/flambda_kind.ml` 1262-1265) and
`Flambda_kind.With_subkind.equal` (1236, by the comparison at 1224-1234, which
uses OCaml's structural comparison on kinds and on subkinds, 101 and 859, and
the comparison of 580-584); on the failure path `Misc.fatal_errorf`, then a
handler (49-59) that prints the continuation, the types, the uses and the
environment on the standard error channel and raises the error again.
W: none (on failure, the standard error channel)
R: none
F: 45-47, when the arity of the types of the use and the arity of the
continuation differ
A: none
read: `middle_end/flambda2/simplify/env/continuation_uses.ml` 17-158;
`middle_end/flambda2/types/grammar/more_type_creators.ml` 476-490;
`middle_end/flambda2/kinds/flambda_arity.ml` 17-200;
`middle_end/flambda2/kinds/flambda_kind.ml` 58-105, 566-640, 855-912, 1198-1267;
`utils/misc.ml` 136-142

## PLACES

### P1: remove
place: `middle_end/flambda2/simplify/env/continuation_uses_env.ml` 145-148
fields and calls (order of the type, lines 20-23): `continuation_uses`:
`Continuation.Map.remove`; `continuation_arities`: `Continuation.Map.remove`.
The arguments are a parameter and a field of a parameter.
pairs: the two calls of `Continuation.Map.remove`: each is pure, on two
different immutable maps. They commute. Neither can fail.
verdict: COMMUTE

### P2: create
place: `middle_end/flambda2/simplify/env/downwards_acc.ml` 94-112
fields and calls (order of the type, lines 22-43): `flow_acc`: `Flow.Acc.empty`;
`are_lifting_conts`: `Are_lifting_conts.no_lifting`;
`continuation_lifting_budget`: `Flambda_features.Expert.cont_lifting_budget`.
The other fields are parameters, the empty list, or values of modules
(`Static_const.Map.empty`, `Name_occurrences.empty`, `LCS.empty`,
`Continuation.Set.empty`, `Code_id.Set.empty`, `Simple.Map.empty`,
`Continuation.Map.empty`): none is applied, so none is a call at this place.
pairs:
- `Flow.Acc.empty` and `Are_lifting_conts.no_lifting`: the second is pure. They
  commute.
- `Flow.Acc.empty` and `Flambda_features.Expert.cont_lifting_budget`: the second
  writes nothing and reads two references of flags (`driver/oxcaml_flags.ml` 419
  and 173). The first writes the counter of stamps of continuations
  (`middle_end/flambda2/identifiers/continuation.ml` 22) and the table of
  continuations (`middle_end/flambda2/identifiers/continuation.ml` 103), and
  does not write a flag. They commute.
- `Are_lifting_conts.no_lifting` and
  `Flambda_features.Expert.cont_lifting_budget`: no write on either side. They
  commute.
- failures: only `Flow.Acc.empty` can fail (no compilation unit set,
  `typing/current_unit.ml` 33; the failures of the table,
  `middle_end/flambda2/algorithms/table_by_int_id.ml` 99 and the assertions; the
  failures of `Compilation_unit.hash` and `Compilation_unit.equal`). The two
  other calls cannot fail and write nothing, so the order chooses nothing.
verdict: REPORT: `Flow.Acc.empty` makes a FRESH NAME, a continuation
(`middle_end/flambda2/simplify/flow/flow_acc.ml` 30-32 calls
`Continuation.create`, `middle_end/flambda2/identifiers/continuation.ml`
109-122: the counter at line 22 goes up by one and the table at line 103 gets an
entry). It is the only call of the place that writes state, and the only one
that can fail; the two other calls neither read nor write what it reads or
writes. So nothing was found that the order of the three fields can change. The
verdict is REPORT only because the rule for a fresh name says so.

### P3: create
place: `middle_end/flambda2/simplify/env/downwards_env.ml` 245-276
fields and calls (order of the type, lines 53-112): `inlining_state`:
`Inlining_state.default` with the round; `inlining_history_tracker`:
`Inlining_history.Tracker.empty`, applied to the result of
`Current_unit.get_cu_exn`; `specialization_cost`:
`Specialization_cost.cannot_specialize`. The other fields are parameters, the
variable `typing_env` (bound before the record, line 244), constants, a list of
one value, or values of modules. None is a call at this place.
pairs:
- `Inlining_state.default` and `Current_unit.get_cu_exn` with
  `Inlining_history.Tracker.empty`: the first reads thirteen references of flags
  (`driver/oxcaml_flags.ml` 480-502) and writes nothing; the second reads the
  reference of the current unit (`typing/current_unit.ml` 18) and writes
  nothing. They commute.
- `Specialization_cost.cannot_specialize` and each of the others: it is pure.
  They commute.
verdict: COMMUTE, FAILURES ORDERED: one call can fail, `Current_unit.get_cu_exn`
(`typing/current_unit.ml` 33, when no compilation unit is set; it prints on the
standard error channel and raises the fatal error). `Inlining_state.default` and
`Specialization_cost.cannot_specialize` cannot fail and write nothing. So in
every order the same single failure is seen, with the same state. The order
chooses nothing.

### P4: enter_set_of_closures
place: `middle_end/flambda2/simplify/env/downwards_env.ml` 372-402
fields and calls (order of the type, lines 53-112): `typing_env`:
`Flambda2_types.Typing_env.closure_env`; `specialization_cost`:
`Specialization_cost.cannot_specialize`. The other fields are variables of the
pattern (lines 341-371), constants, a list of one value, or values of modules.
pairs: `Flambda2_types.Typing_env.closure_env` and
`Specialization_cost.cannot_specialize`: both pure. They commute. Neither can
fail.
verdict: COMMUTE

### P17: arg_types_by_use_id_for_lifting
place: `middle_end/flambda2/simplify/simplify_let_cont_expr.ml` 211-217
fields and calls (order of the type,
`middle_end/flambda2/simplify/env/continuation_uses.ml` 86-89): `arg_type`:
`Flambda2_types.alias_type_of`, applied to the result of
`Flambda_kind.With_subkind.kind` of the result of `Bound_parameter.kind`, and to
a variable; `typing_env`: `Downwards_env.typing_env`.
pairs: `Flambda2_types.alias_type_of` (with the two projections in its argument)
and `Downwards_env.typing_env`: all four are pure. They commute. None can fail.
verdict: COMMUTE

### P18: compute_specialized_continuation
place: `middle_end/flambda2/simplify/simplify_let_cont_expr.ml` 1165-1176 fields
and calls (order of the type, lines 77-99; the record is a copy of `data` with
three fields changed): `cont_uses_env`:
`Continuation_uses_env.add_continuation_use`, with, in its arguments,
`One_continuation_use.use_kind`, `One_continuation_use.id`,
`One_continuation_use.env_at_use`, `One_continuation_use.arg_types`;
`consts_lifted_after_fork`: a variable; `handlers`: `Continuation.Map.add`, on a
variable, a variable and a field of `data`.
pairs:
- `Continuation.Map.add` and `Continuation_uses_env.add_continuation_use`:
  `Continuation.Map.add` is pure: it writes nothing, reads no state, cannot
  fail. So neither call writes what the other reads or writes, whatever
  `add_continuation_use` does. They commute.
- `Continuation.Map.add` and the four projections of `One_continuation_use`: all
  pure.
- failures: only `Continuation_uses_env.add_continuation_use` can fail (its
  entry lists where). `Continuation.Map.add` writes nothing, so the order
  chooses nothing: the same failure, the same state.
verdict: REPORT, for two reasons.
1. A FRESH NAME can be made. `Continuation_uses_env.add_continuation_use` calls
   `Flambda2_types.meet`
   (`middle_end/flambda2/simplify/env/continuation_uses_env.ml` 83). With the
   N-way algorithm, that meet can reach `Variable.create` at
   `middle_end/flambda2/types/env/join_env.ml` 729 (the chain is item 1 of the
   entry `Flambda2_types.meet`). And the N-way algorithm is the one in force at
   this place, if the flags do not change during the pass: this place is reached
   only for a continuation that `Downwards_acc.add_continuation_to_specialize`
   recorded (`middle_end/flambda2/simplify/simplify_let_cont_expr.ml` 1193; the
   one caller is `middle_end/flambda2/simplify/simplify_switch_expr.ml` 1087),
   and that needs the flag of match-in-match
   (`middle_end/flambda2/simplify/simplify_switch_expr.ml` 935-939), which makes
   `Flambda_features.join_algorithm` answer the N-way algorithm
   (`middle_end/flambda2/ui/flambda_features.ml` 66-74). Not decided from the
   code: whether this meet (the type of an argument against the type that is
   unknown but for the subkind) can meet the condition of line 729.
2. `Flambda2_types.meet` is NOT read to its leaves, and it can call the resolver
   of `.cmx` files, whose body below `Flambda_cmx.load_cmx_file_contents` was
   not read.
What the order can change, as far as was read: nothing. Every write and every
failure of the place is in the field `cont_uses_env`; the call of the field
`handlers` is pure.

## WHAT WAS NOT READ, AND DOUBTS

1. `Flambda2_types.meet`: not read to its leaves. Read: the lines given in its
   entry. Not read: the rest of
   `middle_end/flambda2/types/meet_and_n_way_join.ml` and
   `middle_end/flambda2/types/meet_and_join.ml` (the meets and the joins of each
   kind of head), `middle_end/flambda2/types/expand_head.ml`,
   `middle_end/flambda2/types/env/aliases.ml` (but 949-971), the rest of
   `middle_end/flambda2/types/env/typing_env.ml` and of
   `middle_end/flambda2/types/env/join_env.ml`, most of
   `middle_end/flambda2/types/grammar/type_grammar.ml`,
   `middle_end/flambda2/algorithms/leapfrog.ml` and
   `middle_end/flambda2/algorithms/channel.ml` (iterators with mutable state,
   used by the N-way join), `Coercion`, `Rec_info_expr`, `Name_occurrences`,
   `Renaming`, `Code_age_relation`, `Binding_time`. The counts of places of
   failure in its entry are from a search, not from a reading. The statement "no
   maker of names in the files of the binary algorithm" is from a search of the
   files named there.
2. The resolver of `.cmx` files: `Flambda_cmx.load_cmx_file_contents` read
   (28-57). Not read: `Compilation_unit.which_cmx_file`, the function
   `get_module_info` of the loader (it reads a file),
   `Flambda_cmx_format.import_typing_env_and_code` below lines 79-129,
   `Renaming.create_import_map`, `Exported_offsets.import_offsets`,
   `Exported_code.merge`, `Profile.record_call`. Not known: if an import can
   make fresh names (for example `Continuation.import_and_rename`,
   `middle_end/flambda2/identifiers/continuation.ml` 177-181, exists).
3. Whether the meet of `add_continuation_use` can reach `Variable.create` at
   `middle_end/flambda2/types/env/join_env.ml` 729: not decided. The chain of
   calls exists; the condition is on the types.
4. "P18 is reached only with the N-way algorithm" rests on: the one caller of
   `Downwards_acc.add_continuation_to_specialize` that a search finds; the fatal
   error at `middle_end/flambda2/simplify/simplify_switch_expr.ml` 935-939; and
   the flags not changing during the pass. `decide_continuation_specialization`
   was not read whole (read 896-1012).
5. `Flambda2_types.unknown_with_subkind`: not read:
   `Reg_width_const.naked_immediate` below `Const.create` (the hash and the
   equality of constants, `middle_end/flambda2/identifiers/int_ids.ml` 41-253),
   the modules `Target_ocaml_int` and `Tag` and their maps and sets.
6. OCaml's standard library: bodies not read. Used as leaves: `Hashtbl.hash`,
   `Hashtbl.Make` (the table inside each table of identifiers), `Map.Make` on
   `Int` (`find`), `Option.value`, `Option.map`, `Option.is_some`, `List.map`,
   `List.rev`, `List.compare`, `ListLabels.map`, `String.compare`, `Int.equal`,
   `Format.asprintf`, `Format.kfprintf`, `Format.err_formatter`, `Random.bits`
   (once, when `Int_ids` starts), OCaml's structural comparison.
7. The primitive `int_clz` (`middle_end/flambda2/algorithms/patricia_tree.ml`
   19-21) is in C; not read. Its declaration says no allocation, no effect, no
   coeffect.
8. Printers are called only on paths of failure (`Continuation.print`,
   `Continuation_uses_env.print`, `Continuation_uses.print`,
   `Downwards_env.print`, `Flambda2_types.print`, `Typing_env.print`). Their
   bodies were not read. They read the tables of identifiers and flags of
   colours.
9. For the fields that are values of modules (the many `empty`, `none`, and so
   on) not every definition was read. Checked: each is a name that is not
   applied at the place. These definitions were read: `Typing_env_level.empty`,
   `Inlining_history.Relative.empty`, `Continuation_uses_env.empty`,
   `Lifted_cont_params.empty` (one line seen), `Loopify_state.do_not_loopify`
   (one line seen), `Replay_history.first_pass` (one line seen),
   `Inlined_debuginfo.none` (one line seen).
10. `middle_end/flambda2/algorithms/container_types.ml` (read, 17-333) makes
    maps and sets from OCaml's `Map.Make` and `Set.Make` with the comparison of
    the argument. It is NOT what makes the maps and sets of continuations,
    variables, symbols, names, simples, constants and code identifiers: those
    are from `Patricia_tree.Make`, which takes a printer only (see group A).
11. Seen on the way, not one of the places of this part:
    `Inlining_arguments.Args.create`
    (`middle_end/flambda2/terms/inlining_arguments.ml` 255-270), which P3 calls,
    itself builds a record with a call in each of thirteen fields. Each of the
    thirteen only reads one reference of a flag and cannot fail, so they
    commute.
12. Seen on the way, a fact for the rule on tables that intern:
    `Table_by_int_id.Make(E).add` chooses the identifier of a new element from
    the hash of the element, but takes the next free identifier when a different
    element has the same hash. So, between two different elements with the same
    hash, the identifiers depend on the order of the two adds. None of the six
    places of this part has two calls that add to the same table.
