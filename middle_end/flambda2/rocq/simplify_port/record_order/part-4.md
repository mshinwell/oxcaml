# Record order, part 4: places 19, 22 and 23, and the tables of identifiers

Places 19, 22 and 23, and (section T) the tables of identifiers for all 23.
`README.md` of this folder has the question, the sense and the table of places.

commit read: 4fe46bb689903ead25d346ac9efd3c883821f171 (git rev-parse HEAD; git
status --short shows no change)
method: reading only (rg, sed -n, cat -n). Nothing was built, nothing was run.
host assumed: 64 bits (an OCaml integer has 63 bits). The layout of an
identifier and the Patricia trees depend on it (see T1, T7).
paths: from the root of the repository.

## SUMMARY

- P19 (middle_end/flambda2/simplify/simplify_named_result.ml 45-48): COMMUTE.
- P22 (middle_end/flambda2/simplify/simplify_switch_expr.ml 381-386): COMMUTE,
  FAILURES ORDERED. Only one call of the place can fail, and only on a broken
  invariant. The order chooses nothing.
- P23 (middle_end/flambda2/simplify/unboxing/unboxers.ml 249-253): COMMUTE,
  FAILURES ORDERED. Only one call of the place can fail (the interning of the
  constant, when the identifiers of its flag run out). The order chooses
  nothing.

No field of the three places makes a fresh name. At place 22 a fresh variable is
made, but by a `let` at line 364, before the record.
Only place 23 touches a table that interns, and with one call only.

On the table of constants (details in section T):
the identifier of a new constant is NOT taken from a counter. It is the hash of
the datum (its 60 low bits, with the flag of constants above them). If a
DIFFERENT datum already holds that identifier, the new one takes the next free
identifier, going up by one. So the identifier is from the data alone when its
starting identifier is free, and from what the table already holds otherwise.
Two additions of different new data can therefore get different identifiers in
the two orders. This is not only a matter of rare accidents of a hash: the hash
of a constant does not include its constructor, so the naked immediate and the
tagged immediate of one same number always start at the same identifier (T3,
T4).

## FUNCTIONS

### F: Bound_pattern.singleton
defined: middle_end/flambda2/bound_identifiers/bound_pattern.ml:144 (BPt is
Bound_pattern: middle_end/flambda2/simplify/simplify_import.ml:37)
calls: LEAF: it applies the constructor Singleton of the type of lines 15-18 to
its argument. It calls nothing.
W: none
R: none
F: none
A: none (an immutable block)
read: middle_end/flambda2/bound_identifiers/bound_pattern.ml:15-233 (the whole
file)

### F: Bound_var.create
defined: middle_end/flambda2/bound_identifiers/bound_var.ml:30-33 (BV is
Bound_var: middle_end/flambda2/simplify/simplify_import.ml:38)
calls: LEAF: it builds the immutable record of lines 17-21 from its three
arguments. No check, no call. The variable is an argument; it is not made here.
W: none
R: none
F: none
A: none
read: middle_end/flambda2/bound_identifiers/bound_var.ml:17-70 (the whole file)

### F: Name_mode.normal
defined: middle_end/flambda2/nominal/name_mode.ml:44 (NM is Name_mode:
middle_end/flambda2/simplify/simplify_import.ml:52)
calls: LEAF: it is a constant (the constructor Normal of lines 19-22), not a
function.
W: none
R: none
F: none
A: none
read: middle_end/flambda2/nominal/name_mode.ml:15-150 (the whole file)

### F: Simple.symbol
defined: middle_end/flambda2/term_basics/simple.ml:18 includes Int_ids.Simple;
the body is middle_end/flambda2/identifiers/int_ids.ml:741
calls: LEAF: it returns its argument unchanged. The Simple of a symbol IS the
integer of the symbol. No table is read or written.
W: none
R: none
F: none
A: none
read: middle_end/flambda2/term_basics/simple.ml:17-240 (the whole file, to see
that symbol is not defined again);
middle_end/flambda2/identifiers/int_ids.ml:720-860
note: the same is true of Simple.var
(middle_end/flambda2/identifiers/int_ids.ml:737), Simple.vars (739), Simple.name
(735), Simple.const (743), Name.var (645), Name.symbol (651).

### F: Named.create_simple
defined: middle_end/flambda2/terms/flambda.ml:1398 (Named comes from the open of
Flambda.Import, middle_end/flambda2/terms/flambda.ml:1720; the type is
middle_end/flambda2/terms/flambda.ml:46-51)
calls: LEAF: it applies the constructor Simple of the type named.
W: none
R: none
F: none
A: none
read: middle_end/flambda2/terms/flambda.ml:21-52, 1395-1430

### F: Named.create_prim
defined: middle_end/flambda2/terms/flambda.ml:1402
calls: LEAF: it applies the constructor Prim to a pair. (At place 22 it is
called at line 363, before the record. It is here for information.)
W: none
R: none
F: none
A: none
read: middle_end/flambda2/terms/flambda.ml:1395-1430

### F: Simplified_named.create
defined: middle_end/flambda2/simplify/simplified_named.ml:38-61
calls: by the constructor of its argument (lines 40-56), then one record
(58-61):
- Simple: Code_size.simple, Cost_metrics.from_size; then Named.free_names
- Prim: Code_size.prim, Cost_metrics.from_size; then Named.free_names
- Set_of_closures: Misc.fatal_errorf with Named.print; it does not return
- Static_consts: Misc.fatal_errorf with Named.print; it does not return
- Rec_info: the constant Cost_metrics.zero; then Named.free_names
W: none on the paths that return. On the two paths that fail: the channel of
errors (through Misc.fatal_errorf).
R: Clflags.target (utils/clflags.ml:266), only for a Prim whose operation is one
of four unary ones (see Code_size.prim). The table of Simples
(middle_end/flambda2/identifiers/int_ids.ml:727), only when the Simple, or an
argument of the primitive, is a Simple with a coercion (see
Simple.pattern_match).
F: middle_end/flambda2/simplify/simplified_named.ml:47-50, the argument is a
Set_of_closures; 52-55, the argument is Static_consts; and the failures of
Named.free_names and of Code_size.simple (below).
A: none (an immutable record of three fields; the record at 58-61 has one call
only, so it is not a place)
read: middle_end/flambda2/simplify/simplified_named.ml:17-100 (the whole file);
middle_end/flambda2/simplify/simplified_named.mli:15-64

### F: Code_size.simple
defined: middle_end/flambda2/terms/code_size.ml:42 is Code_size_v1.simple; the
body is middle_end/flambda2/terms/code_size_v1.ml:533-535
calls: Simple.pattern_match, with two functions that return a constant integer
W: none
R: the table of Simples, only if the Simple has a coercion
F: those of Simple.pattern_match
A: none (an integer)
read: middle_end/flambda2/terms/code_size.ml:17-60 (the whole file);
middle_end/flambda2/terms/code_size_v1.ml:533-535

### F: Code_size.prim
defined: middle_end/flambda2/terms/code_size.ml:40 is Code_size_v1.prim; the
body is middle_end/flambda2/terms/code_size_v1.ml:524-531
calls: in the same file: nullary_prim_size (386-396), unary_prim_size (398-449),
binary_prim_size (451-474), ternary_prim_size (476-490), quaternary_prim_size
(492-509), variadic_prim_size (515-522); and under them unary_int_prim_size
(49-69), arith_conversion_size (71-134), unbox_number (136-147), box_number
(150-162), block_load (164-165), array_load (167-176), block_set (178-187),
array_set (189-199), string_or_bigstring_load (201-231), bytes_like_set
(235-238), divmod_bi_check (240-251), binary_int_arith_primitive (253-308),
binary_int_shift_primitive (310-335), binary_int_comp_primitive (337-371),
int_comparison_like_compare_functions (373-378), binary_float_arith_primitive
(380), binary_float_comp_primitive (382), block (511), array (513). All of these
are matches on constructors and additions of integers. Leaves outside the file:
Target_system.Machine_width.is_32_bit and is_64_bit; Clflags.target_is_jsir;
List.length (Stdlib: no state, no failure, body not read).
W: none
R: Clflags.target (utils/clflags.ml:266), read at
middle_end/flambda2/terms/code_size_v1.ml:138 (Unbox_number), 152 (Box_number),
433 (Untag_immediate), 438 (Tag_immediate). Nothing else.
F: none (this rests on the matches being complete; see DOUBTS 3)
A: none (an integer)
read: middle_end/flambda2/terms/code_size_v1.ml:17-567 (the whole file)

### F: Clflags.target_is_jsir
defined: utils/clflags.ml:275-278
calls: LEAF: it reads the reference Clflags.target (utils/clflags.ml:266) and
matches on it
W: none
R: Clflags.target, utils/clflags.ml:266 (a flag, set by Clflags.set_target
at 268)
F: none
A: none
read: utils/clflags.ml:259-278

### F: Target_system.Machine_width.is_32_bit ..
heading: F: Target_system.Machine_width.is_32_bit,
Target_system.Machine_width.is_64_bit
defined: utils/target_system.ml:147-149 and 151-153
calls: LEAF: a match on the argument
W: none
R: none
F: none
A: none
read: utils/target_system.ml:129-158

### F: Cost_metrics.from_size
defined: middle_end/flambda2/terms/cost_metrics.ml:42
calls: LEAF: a record of its argument and of the constant
Removed_operations.zero (middle_end/flambda2/terms/removed_operations.ml:33-42).
Cost_metrics.zero (middle_end/flambda2/terms/cost_metrics.ml:32) is a constant
too.
W: none
R: none
F: none
A: none
read: middle_end/flambda2/terms/cost_metrics.ml:22-107 (the whole file);
middle_end/flambda2/terms/removed_operations.ml:20-60

### F: Named.free_names
defined: middle_end/flambda2/terms/flambda.ml:1411-1420
calls: Simple: Simple.free_names. Prim: Flambda_primitive.free_names. Rec_info:
Rec_info_expr.free_names. Set_of_closures: Name_occurrences.union,
Set_of_closures.free_names, Alloc_mode.For_allocations.free_names.
Static_consts: Static_const_group.free_names. The last two branches cannot be
reached from Simplified_named.create, which fails before;
Set_of_closures.free_names and Static_const_group.free_names were not read for
this part.
W: none (branches Simple, Prim, Rec_info)
R: the table of Simples, only for a Simple with a coercion
F: those of Simple.free_names and Flambda_primitive.free_names
A: none
read: middle_end/flambda2/terms/flambda.ml:1395-1430

### F: Simple.free_names
defined: middle_end/flambda2/term_basics/simple.ml:129, which calls
free_names_with_mode (123-127) with the constant Name_mode.normal
calls: Simple.pattern_match; for a name: Coercion.free_names, then
Name_occurrences.add_name; for a constant: the constant Name_occurrences.empty
W: none
R: the table of Simples, only for a Simple with a coercion
F: those of Simple.pattern_match. The assertion on counters (see
Name_occurrences) cannot fail here: the counts that are built are 1, 2 or 3.
A: none
read: middle_end/flambda2/term_basics/simple.ml:17-240

### F: Simple.pattern_match
defined: middle_end/flambda2/identifiers/int_ids.ml:745-764 (reached through the
include at middle_end/flambda2/term_basics/simple.ml:18)
calls: Table_by_int_id.Id.flags
(middle_end/flambda2/algorithms/table_by_int_id.ml:33, a shift of the integer).
Then, by the flags: for a variable or a symbol, the caller's function for names,
with the identity coercion; for a constant, the caller's function for constants;
for the flags of a Simple with a coercion, Int_ids.Simple.find_data
(middle_end/flambda2/identifiers/int_ids.ml:731), which is Table.find
(middle_end/flambda2/algorithms/table_by_int_id.ml:109-111) on the table held by
the reference of middle_end/flambda2/identifiers/int_ids.ml:727, and then the
same choice on the flags of the Simple that is stored there.
W: none
R: none when the flags are those of a variable, a symbol or a constant. When
they are those of a Simple with a coercion: the reference
middle_end/flambda2/identifiers/int_ids.ml:727 and the hash table that it holds.
F: middle_end/flambda2/identifiers/int_ids.ml:763 and 764, the flags are none of
the four (not reachable: the type is private,
middle_end/flambda2/identifiers/int_ids.mli:200, and every maker of a Simple
gives one of the four flags).
middle_end/flambda2/algorithms/table_by_int_id.ml:110, an assertion on the flags
(same). middle_end/flambda2/algorithms/table_by_int_id.ml:111, Not_found from
Hashtbl: the identifier has the flags of a Simple with a coercion and is not in
the table that the reference holds now. That needs the table to be replaced
(middle_end/flambda2/identifiers/int_ids.ml:729) after the Simple was made; see
DOUBTS 8.
A: none
read: middle_end/flambda2/identifiers/int_ids.ml:695-860;
middle_end/flambda2/algorithms/table_by_int_id.ml:17-127 (the whole file)

### F: Coercion.free_names
defined: middle_end/flambda2/term_basics/coercion.ml:17-23
calls: for the identity: the constant Name_occurrences.empty. For a change of
depth: Rec_info_expr.free_names twice and Name_occurrences.union.
W: none
R: none
F: none (the counts are 1 or 2)
A: none
read: middle_end/flambda2/term_basics/coercion.ml:15-55 (the whole file);
middle_end/flambda2/identifiers/coercion0.ml:15-125

### F: Rec_info_expr.free_names
defined: middle_end/flambda2/term_basics/rec_info_expr.ml:38, which calls
free_names_in_mode (32-36)
calls: the constant Name_occurrences.empty, or
Name_occurrences.singleton_variable; it recurses on the term
W: none
R: none
F: none
A: none
read: middle_end/flambda2/term_basics/rec_info_expr.ml:15-45 (the whole file);
middle_end/flambda2/identifiers/rec_info_expr0.ml:15-218

### F: Flambda_primitive.free_names
defined: middle_end/flambda2/terms/flambda_primitive.ml:2819-2847
calls: free_names_nullary_primitive (1150-1154), free_names_unary_primitive
(1703-1729), free_names_binary_primitive (2150-2157),
free_names_ternary_primitive (2514-2518), free_names_quaternary_primitive
(2520-2523), free_names_variadic_primitive (2648-2654); Simple.free_names for
each argument; Simple.List.free_names for a variadic primitive;
Name_occurrences.union and union_list. The functions by arity return the
constant Name_occurrences.empty, except: unary Box_number and Int_as_pointer,
and variadic Make_block and Make_array (Alloc_mode.For_allocations.free_names);
unary Project_function_slot and Project_value_slot
(Name_occurrences.add_function_slot_in_projection,
add_value_slot_in_projection); unary Duplicate_array, Duplicate_block, Obj_dup,
Make_lazy (Name_occurrences.singleton_variable).
W: none
R: the table of Simples, only for an argument that is a Simple with a coercion
F: those of Simple.pattern_match; and the assertion on counters of
Name_occurrences (middle_end/flambda2/nominal/name_occurrences.ml:106), when one
name occurs more than 1 048 575 times in the arguments of one primitive. That
needs a variadic primitive with more than a million arguments.
A: none
read: middle_end/flambda2/terms/flambda_primitive.ml:1150-1154, 1703-1729,
2150-2157, 2514-2523, 2648-2654, 2678-2685, 2819-2847

### F: Simple.List.free_names
defined: middle_end/flambda2/term_basics/simple.ml:156-159
calls: List.fold_left (Stdlib: no state, body not read) with
Name_occurrences.union and Simple.free_names
W: none
R: as Simple.free_names
F: as Simple.free_names, and the assertion on counters
A: none
read: middle_end/flambda2/term_basics/simple.ml:140-172

### F: Alloc_mode.For_allocations.free_names
defined: middle_end/flambda2/bound_identifiers/alloc_mode.ml:312-319
calls: Name_occurrences.singleton_variable, Name_occurrences.add_variable
W: none
R: none
F: none (counts 1 or 2)
A: none
read: middle_end/flambda2/bound_identifiers/alloc_mode.ml:15-377 (the whole
file)

### F: Name_occurrences.empty, add_name, add_variable, singleton_variable ..
heading: F: Name_occurrences.empty, add_name, add_variable, singleton_variable,
add_function_slot_in_projection, add_value_slot_in_projection, union, union_list
defined: middle_end/flambda2/nominal/name_occurrences.ml: empty 372-383 (a
constant record of ten empty maps); singleton_variable 417-418; add_variable
420-421; add_name 426-427; add_function_slot_in_projection 429-433;
add_value_slot_in_projection 435-439; union 734-744, with the first is_empty
(645-666) and binary_op (582-643); union_list 788
calls: the functions of the functor of lines 17-313 (next entry), applied to
Name (334-338), Continuation (340-344), Function_slot (346-347), Value_slot
(348), Code_id (350-354); Name.var and Name.symbol (identities,
middle_end/flambda2/identifiers/int_ids.ml:645, 651); List.fold_left
W: none
R: none
F: middle_end/flambda2/nominal/name_occurrences.ml:106, 111, 115 (through the
next entry)
A: none (immutable records of maps)
read: middle_end/flambda2/nominal/name_occurrences.ml:15-760, 780-790

### F: Name_occurrences.For_one_variety_of_names_not_renamable(N).empty ..
heading: F: Name_occurrences.For_one_variety_of_names_not_renamable(N).empty,
is_empty, singleton, add, union; and For_one_name.one_occurrence, add, union
defined: middle_end/flambda2/nominal/name_occurrences.ml: the functor 17-313;
For_one_name 67-199 (a count for each of the three name modes, packed in one
integer, 20 bits each: 94-122); one_occurrence 142-146; add 148-158; union
183-189; empty 208; is_empty 210; singleton 212-213; add 215-220; union 224-228
calls: N.Map.empty, N.Map.is_empty, N.Map.singleton, N.Map.update,
N.Map.union_total. For N = Name, Continuation, Code_id these are the Patricia
trees (next entry). For N = Function_slot, Value_slot these are Stdlib's Map
with the comparison of slots (entry after).
W: none
R: none
F: middle_end/flambda2/nominal/name_occurrences.ml:106, 111, 115: an assertion
fails when a count is not between 0 and 1 048 575
A: none
read: middle_end/flambda2/nominal/name_occurrences.ml:17-313

### F: Patricia_tree.Make(_).Map.empty, is_empty, singleton, update ..
heading: F: Patricia_tree.Make(_).Map.empty, is_empty, singleton, update,
union_total (and add, find, mem, remove, read for the other parts)
defined: middle_end/flambda2/algorithms/patricia_tree.ml. The functor Make is
2229-2293; it takes a printer only. Map is 2186-2223 and includes the operations
of the functor Tree_operations (469-2102) on the trees of Map0 (360-465). empty
2191 (378); is_empty 643-644; singleton 2193 (646); update 769-776 with
update_tree 737-767; union_total 1136-1137 with union_total_tree 1126-1134,
pattern_match_pair_merge 883-1043, pattern_match_pair_merge_total 1045-1050,
toplevel_union 1056-1063, toplevel_union_total 1065-1067; add 703-707 with
add_tree 684-701 (it adds, or replaces the datum of a key that is there); find
1272-1277 with find_tree 1260-1270; mem 659-660; remove 794-798. Helpers on
bits: 45-95. One external primitive, int_clz (19-21).
calls: only functions of the same file, on the integer keys and on immutable
trees; and the function that the caller gives (for update and union_total)
W: none
R: none (a key is an integer; it is looked at bit by bit; no comparison function
is given by the user, and no table is read)
F: none for empty, is_empty, singleton, update, union_total, add, mem, remove
(apart from what the caller's function does). find raises Not_found for a key
that is absent (1273). Line 1047 is an assert false that cannot be reached: a
total union of two non-empty trees is never empty. Other functions of the file
that can fail, not used at the places of this part: choose, min_binding,
max_binding on an empty tree (1521, 1543, 1565); disjoint_union on a common key
(2269-2273); the mutable iterator (1935, 1946).
A: none. (Mutable_iterator.create, 1910-1915, returns a fresh mutable iterator;
it is not used at the places of this part.)
read: middle_end/flambda2/algorithms/patricia_tree.ml:15-2293 (the whole file);
middle_end/flambda2/algorithms/patricia_tree.mli:15-39

### F: Function_slot.Map and Value_slot.Map ..
heading: F: Function_slot.Map and Value_slot.Map (Stdlib's Map), the comparison
of slots, Compilation_unit.compare
defined: middle_end/flambda2/identifiers/slot.ml:58-95 applies
Container_types.Make
(middle_end/flambda2/algorithms/container_types.ml:316-321), whose Map is
Make_map (33-265), which includes Stdlib's Map.Make on the comparison of
middle_end/flambda2/identifiers/slot.ml:61-78. That comparison: physical
equality first; then the difference of the stamps; then Compilation_unit.compare
(utils/compilation_unit.ml:336-362, which compares names, prefixes and arguments
of instances; utils/compilation_unit.ml:74, 159).
calls: Stdlib Map.Make(_).empty, is_empty, update, union: LEAF, Stdlib;
documented as persistent maps with no state; they call the comparison; bodies
not read.
W: none
R: none
F: none in the comparison of slots. Compilation_unit.compare has an assertion on
the tag of the block (utils/compilation_unit.ml:286) and a check that a name is
not empty (utils/compilation_unit.ml:89-92, reached from 299); both are
invariants of how a compilation unit is built.
A: none
read: middle_end/flambda2/identifiers/slot.ml:17-131 (the whole file);
middle_end/flambda2/algorithms/container_types.ml:17-333 (the whole file);
utils/compilation_unit.ml:28-125, 124-200, 202-520

### F: Value_slot.kind
defined: middle_end/flambda2/identifiers/value_slot.ml:30-32
calls: payload (middle_end/flambda2/identifiers/slot.ml:128): LEAF, the
projection of the field payload of the immutable record of
middle_end/flambda2/identifiers/slot.ml:50-56. Then the first component of the
pair.
W: none
R: none (a value slot is a record, not an integer in a table)
F: none
A: none
read: middle_end/flambda2/identifiers/value_slot.ml:17-36 (the whole file);
middle_end/flambda2/identifiers/slot.ml:17-131

### F: Const.const_poison
defined: Const is Reg_width_const
(middle_end/flambda2/simplify/simplify_import.ml:22);
middle_end/flambda2/identifiers/reg_width_const.ml:17 includes Int_ids.Const;
the body is middle_end/flambda2/identifiers/int_ids.ml:431
calls: it builds the datum Poison of the kind and the string (constructor of
middle_end/flambda2/identifiers/int_ids.ml:57), then Int_ids.Const.create
W: the table of constants, when the datum is not yet in it (see
Int_ids.Const.create)
R: the table of constants
F: those of Table_by_int_id.Make(_).add
A: none (it returns an integer)
read: middle_end/flambda2/identifiers/reg_width_const.ml:17-224 (the whole
file); middle_end/flambda2/identifiers/int_ids.ml:41-253, 361-467;
middle_end/flambda2/identifiers/int_ids.mli:21-107

### F: Int_ids.Const.create
defined: middle_end/flambda2/identifiers/int_ids.ml:374
calls: it reads the reference grand_table_of_constants
(middle_end/flambda2/identifiers/int_ids.ml:366) and calls Table.add, where
Table is Table_by_int_id.Make applied to Const_data
(middle_end/flambda2/identifiers/int_ids.ml:364)
W: the hash table held by the reference
middle_end/flambda2/identifiers/int_ids.ml:366, when the datum is new
R: the reference middle_end/flambda2/identifiers/int_ids.ml:366 and its hash
table
F: those of Table_by_int_id.Make(_).add
A: none
read: middle_end/flambda2/identifiers/int_ids.ml:361-467

### F: Table_by_int_id.Make(E).add
defined: middle_end/flambda2/algorithms/table_by_int_id.ml:75-107
calls: E.hash, Id.create (28-31), E.equal, Id.next (35), Id.flags (33);
find_opt, find and add of a hash table from Stdlib's Hashtbl.Make (50-63), keyed
by the identifier itself; Misc.fatal_errorf with E.print (99). What it does is
in T2.
W: the hash table given as argument: one new binding, when no datum equal to the
argument is found
R: the same hash table
F: line 91, an assertion: the walk after a collision goes past the last
identifier of the flag (all identifiers from the start to the top of the 60 bits
are taken). Line 99, a fatal error: the walk came back to its start; line 91
fails before. Lines 103 and 106 repeat the check of line 91. Id.create, lines
29-30, a fatal error for flags below 0 or above 15: the flags are constants from
0 to 4, so this cannot happen. E.equal can fail for some data (for two
immediates of different target widths:
middle_end/flambda2/numbers/target_ocaml_int.ml:282-286); not for a Poison (see
Const_data.equal). Hashtbl can raise only for lack of memory.
A: none
read: middle_end/flambda2/algorithms/table_by_int_id.ml:17-127 (the whole file)

### F: Const_data.hash, Const_data.equal ..
heading: F: Const_data.hash, Const_data.equal (on a Poison), Flambda_kind.hash,
Flambda_kind.equal
defined: middle_end/flambda2/identifiers/int_ids.ml:234-251 (hash; Poison at
250-251) and 199-232 (equal; Poison at 225-226; any two different constructors
give false at 227-232). Const_data gets them through Container_types.Make, which
includes its argument
(middle_end/flambda2/algorithms/container_types.ml:316-318). Flambda_kind.hash
is Stdlib's Hashtbl.hash and Flambda_kind.equal is Stdlib's compare equal to 0
(middle_end/flambda2/kinds/flambda_kind.ml:101-105), on a type with constant
constructors and one constructor over constant constructors (19-62).
calls: for a Poison: Hashtbl.hash of the pair of Flambda_kind.hash of the kind
and String.hash of the string; Flambda_kind.equal and String.equal. LEAVES:
Stdlib Hashtbl.hash, String.hash, String.equal, compare: no state; on these data
they cannot fail; bodies not read.
W: none
R: none
F: none
A: none
read: middle_end/flambda2/identifiers/int_ids.ml:41-253;
middle_end/flambda2/kinds/flambda_kind.ml:17-170

### F: Misc.fatal_errorf
defined: utils/misc.ml:20-24
calls: LEAF: Format.kfprintf on Format.err_formatter (Stdlib; it writes the
error channel), then it raises Misc.Fatal_error (utils/misc.ml:18)
W: the error channel
R: the state of the formatter
F: always
A: none
read: utils/misc.ml:16-31

### F: Named.print
defined: middle_end/flambda2/terms/flambda.ml:1422 is print_named, 868-885
calls: printers of Simple, Flambda_primitive, Set_of_closures, static constants,
Rec_info_expr, Debuginfo, and Flambda_colours. NOT READ down to leaves. It is
called only on the two paths of Simplified_named.create that end with a fatal
error.
W: the formatter given (the error channel, there)
R: not read (tables of identifiers for names, flags for colours)
F: not read
A: none
read: middle_end/flambda2/terms/flambda.ml:866-890

## PLACES

### P19: create_have_lifted_set_of_closures
place: `middle_end/flambda2/simplify/simplify_named_result.ml` 45-48
The record is at lines 44-51, in the function given to List.mapi (42-52). Its
type is middle_end/flambda2/simplify/simplified_named.ml:95-99.
fields and calls (order of the type):
- let_bound: Bound_pattern.singleton (on a bound variable taken from the list)
- simplified_defining_expr: Simple.symbol, then Named.create_simple, then
  Simplified_named.create (nested, so their order is fixed; machine_width is
  bound by a let at line 39, before the record)
- original_defining_expr: no call (a test on the index and a constructor)

what the second field does here, step by step: Simple.symbol returns the integer
of the symbol; its flags are those of a symbol (the type of symbols is private,
middle_end/flambda2/identifiers/int_ids.mli:145, and every maker of a symbol
goes through the table of symbols with the flag of symbols).
Simplified_named.create takes the branch Simple
(middle_end/flambda2/simplify/simplified_named.ml:41-42). Code_size.simple calls
Simple.pattern_match, which sees the flags of a symbol and returns the constant
for names: no table is read. Cost_metrics.from_size builds a record.
Named.free_names calls Simple.free_names: Simple.pattern_match again (no table),
Coercion.free_names on the identity coercion (the constant empty),
Name_occurrences.add_name, which is one update of an empty Patricia tree with a
count of 1 (the assertion of middle_end/flambda2/nominal/name_occurrences.ml:106
is on the number 1 and holds).

pairs:
- Bound_pattern.singleton with each call of the other field:
  Bound_pattern.singleton is a constructor; it reads and writes nothing. They
  commute.
- no call of this place writes any state, and none reads a table, a counter or a
  flag.

fresh names: none. interning: none. failures: none on this path (no assertion or
fatal error is on the path taken for a symbol, except the assertion on the
number 1).
verdict: COMMUTE

### P22: let_op_dollar
place: `middle_end/flambda2/simplify/simplify_switch_expr.ml` 381-386
The operator is defined at lines 309-388; the record is in the branch Prim
(356-388). Its type is middle_end/flambda2/simplify/simplified_named.ml:95-99.
before the record, each fixed by a let: named, made by Named.create_prim (363);
the fresh variable, made by Variable.create (364); duid (378); machine_width
(379). So no fresh name is made in a field of the record.
fields and calls (order of the type):
- let_bound: Bound_var.create (on the variable of line 364, duid, and the
  constant Name_mode.normal), then Bound_pattern.singleton (nested)
- simplified_defining_expr: Simplified_named.create on named, which is always a
  Prim here
- original_defining_expr: no call

the primitives that reach this place: those given to bound_prim in the same file
(lines 497, 514, 525, 545, 559, 567, 575): Tag_immediate, Boolean_not (unary);
integer multiplication, addition, subtraction, and an array load (binary). The
entries for Code_size.prim and Flambda_primitive.free_names cover every
primitive, not only these.

pairs:
- Bound_var.create and Bound_pattern.singleton with Simplified_named.create: the
  first two read and write nothing. They commute with anything.
- Simplified_named.create writes nothing on the path of a Prim. It reads the
  flag Clflags.target (for Tag_immediate) and perhaps the table of Simples (for
  an argument with a coercion). Nothing in the place writes these.

fresh names: none in the fields. interning: none.
failures: Bound_var.create and Bound_pattern.singleton cannot fail.
Simplified_named.create on a Prim can fail only at:
middle_end/flambda2/algorithms/table_by_int_id.ml:111 (an argument is a Simple
with a coercion that is absent from the table of Simples held now: only if the
table was replaced after the Simple was made; DOUBTS 8);
middle_end/flambda2/algorithms/table_by_int_id.ml:110 and
middle_end/flambda2/identifiers/int_ids.ml:763-764 (flags that the private type
excludes); middle_end/flambda2/nominal/name_occurrences.ml:106 (more than
1 048 575 occurrences of one name: not possible with the one or two arguments of
the primitives of this place).
verdict: COMMUTE, FAILURES ORDERED: only Simplified_named.create can fail, at
the points above, each on a broken invariant. The two other calls cannot fail
and write nothing. So the order chooses nothing: not which failure is seen
(there is one call that can fail), and not which writes happen before it (there
are none). If these points are counted as not reachable, the verdict is COMMUTE.

### P23: unboxer
place: `middle_end/flambda2/simplify/unboxing/unboxers.ml` 249-253
The function is Closure_field.unboxer (247-259). The type of the record is lines
25-32: var_name, var_kind, poison_const, unboxing_prim, prove_simple.
fields and calls (order of the type):
- var_name: a string literal
- var_kind: Value_slot.kind (249)
- poison_const: Value_slot.kind (252), then Const.const_poison on its result and
  a string literal (251-253; nested)
- unboxing_prim, prove_simple: two functions that are built, not called

pairs:
- Value_slot.kind (field var_kind) with Const.const_poison: Value_slot.kind
  projects a field of an immutable record; it reads no table and writes nothing.
  Const.const_poison reads and may write the table of constants
  (middle_end/flambda2/identifiers/int_ids.ml:366). Neither writes what the
  other reads or writes. They commute.
- Value_slot.kind (field var_kind) with Value_slot.kind (argument of
  Const.const_poison): the same projection, twice. They commute.

interning: ONE call of the place may add to a table that interns (the table of
constants). No other call of the place reads or writes that table, or any table.
So the rule for two additions to one table does not apply. The identifier that
Const.const_poison returns depends on what the table held BEFORE the record (T2,
T4); it is the same in both orders of the fields.
fresh names: none (the identifier of the constant comes from a hash of its datum
and from the table, not from a counter).
failures: Value_slot.kind cannot fail. Const.const_poison can fail only in
Table_by_int_id.Make(_).add:
middle_end/flambda2/algorithms/table_by_int_id.ml:91 (and 99, 103, 106), when
the walk after a collision runs out of the identifiers of the flag; and for lack
of memory in Hashtbl.
verdict: COMMUTE, FAILURES ORDERED: only Const.const_poison can fail (points
above). The other call cannot fail and writes nothing. So the order chooses
nothing. If the exhaustion of 2^60 identifiers is counted as not reachable, the
verdict is COMMUTE.

## T. THE TABLES OF middle_end/flambda2/identifiers/ (for all 23 places)

Files read whole: middle_end/flambda2/algorithms/table_by_int_id.ml and .mli;
middle_end/flambda2/identifiers/int_ids.ml (1-1083),
middle_end/flambda2/identifiers/continuation.ml,
middle_end/flambda2/identifiers/variable.ml,
middle_end/flambda2/identifiers/symbol.ml,
middle_end/flambda2/identifiers/name.ml,
middle_end/flambda2/identifiers/code_id.ml,
middle_end/flambda2/identifiers/code_id_or_name.ml,
middle_end/flambda2/identifiers/code_id_or_symbol.ml,
middle_end/flambda2/identifiers/reg_width_const.ml,
middle_end/flambda2/identifiers/slot.ml,
middle_end/flambda2/identifiers/value_slot.ml,
middle_end/flambda2/identifiers/function_slot.ml,
middle_end/flambda2/identifiers/coercion0.ml,
middle_end/flambda2/identifiers/rec_info_expr0.ml,
middle_end/flambda2/identifiers/apply_cont_rewrite_id.ml,
middle_end/flambda2/identifiers/named_rewrite_id.ml,
middle_end/flambda2/identifiers/flambda_debug_uid.ml,
middle_end/flambda2/identifiers/continuation_callsite_map.ml;
middle_end/flambda2/identifiers/field.ml from line 120;
middle_end/flambda2/term_basics/simple.ml;
middle_end/flambda2/algorithms/patricia_tree.ml,
middle_end/flambda2/algorithms/container_types.ml; utils/numbers.ml 1-36;
utils/symbol.ml; utils/linkage_name.ml 15-30. Read in part:
middle_end/flambda2/identifiers/int_ids.mli (15-120, 300-326, and the line of
each type: 22, 110, 145, 176, 200, 247, 281, 302, all private).

### T1. An identifier ..
heading: T1. An identifier (Table_by_int_id.Id,
middle_end/flambda2/algorithms/table_by_int_id.ml:19-36)
- An identifier is an OCaml integer. The 3 highest bits are the FLAGS (which
  sort of thing it is). The 60 other bits come from a hash. Id.create (28-31)
  keeps the 60 low bits of a hash and puts the flags above. Id.flags (33) is a
  shift. Id.next (35) adds one.
- The flags (middle_end/flambda2/identifiers/int_ids.ml:31-39): variable 0,
  symbol 1, constant 2, Simple with a coercion 3, code identifier 4.
  Continuations have their own table with flags 0
  (middle_end/flambda2/identifiers/continuation.ml:19). Fields of the reaper
  have their own table with flags 0
  (middle_end/flambda2/identifiers/field.ml:147).
- With flags 4 the integer is negative (the highest bit is the sign).
- Comparison, equality and hash of identifiers (Id.compare, Id.equal, Id.hash)
  are those of utils/numbers.ml:17-25 (through utils/identifiable.ml:266-268 and
  middle_end/flambda2/algorithms/table_by_int_id.ml:19-20): the comparison of
  integers, the equality of integers, and the identity. They read no table.

### T2. A table ..
heading: T2. A table (Table_by_int_id.Make,
middle_end/flambda2/algorithms/table_by_int_id.ml:38-127)
- A table is a hash table of Stdlib (Hashtbl.Make, 50-63) from identifiers to
  data. Its own hash function (57-60) only places the buckets; it does not
  change any answer.
- create (69): a new empty table.
- find (109-111): an assertion on the flags of the identifier; then the datum,
  or Not_found.
- add (75-107), on a datum d. Let s be the starting identifier of d: Id.create
  of E.hash d and the flags of the table. (1) If s is free, d is stored at s and
  s is returned. (2) If s holds a datum E.equal to d, s is returned and nothing
  is written. (3) If s holds a different datum, the identifiers s+1, s+2, … are
  tried in turn: the first that is free takes d; the first that holds a datum
  equal to d is returned. The walk must stay in the flags of the table
  (assertion, 91).
- No entry is ever removed or replaced (add is reached only for an identifier
  that was just found free: 77-79, 92-93, 101-102). The only other change is
  that the whole table is replaced by a new empty one (T6).
- export (117-120) builds a new hash table with the data of chosen identifiers
  (it reads). import (122-126) reads a datum from such a table, or stops with a
  fatal error.

THE ORDER OF TWO ADDITIONS TO ONE TABLE, from the code above. Let M be the table
before, d1 and d2 two data.
- d1 and d2 E.equal: the first call stores (or finds), the second finds. Same
  identifier, same table, in both orders.
- d1 already in M (or d2): the call for it writes nothing and returns the same
  identifier in both orders. (Its walk stops at d1 before any free identifier;
  the other call can only take a free identifier.) Same table in both orders.
- d1 and d2 different and both new. Let f1 and f2 be the first free identifiers
  on the walks of d1 and d2 in M. If f1 and f2 differ: d1 gets f1 and d2 gets f2
  in both orders, and the table after is the same. If f1 = f2: the datum added
  FIRST gets f1 and the other gets the next free identifier. THE ORDER THEN
  CHANGES BOTH IDENTIFIERS and what the table answers at them.
- f1 = f2 when the two data have the same starting identifier (equal hashes on
  the 60 low bits), or when the start of one lies in a run of taken identifiers
  that ends where the walk of the other ends.

So: a call that may add to a table commutes with a call that does not touch that
table. Two calls that may each add a NEW, DIFFERENT datum to the SAME table do
not commute in general: it cannot be shown from the code that their walks never
meet, and for constants it can be shown that they often do (T4).

What a changed identifier can change afterwards: every comparison and every Set
or Map of these identifiers is by the integer (T7), so the order in which a set
or a map is walked, and anything that follows that order.

### T3. The tables, one by one

VARIABLES. Table: reference middle_end/flambda2/identifiers/int_ids.ml:474
(replaced at 476). Datum: Variable_data (255-302): compilation unit, name,
stamp, kind, user-visible. E.hash (276-278): hash2 (23-27) of the hash of the
unit and the hash of the stamp; hash2 uses hash_seed (17-19), one number drawn
with Random.bits when the module is initialised. E.equal (280-301): same stamp
and same unit.
- Makers: Variable.create (508-511) reads the current unit
  (typing/current_unit.ml:18, 30-33; a fatal error if none) and calls
  create_in_compilation_unit (492-506), which INCREMENTS THE COUNTER
  previous_name_stamp (middle_end/flambda2/identifiers/int_ids.ml:490) and adds
  to the table. Variable.rename
  (middle_end/flambda2/identifiers/variable.ml:22-24),
  create_with_same_name_as_ident (19-20), import_and_rename
  (middle_end/flambda2/identifiers/int_ids.ml:557-560) call create.
  Variable.import (554-555) adds an imported datum.
- Each creation is a FRESH NAME: a new stamp, so a datum equal to no other, so a
  new entry; the identifier is a function of the unit, the stamp and the seed
  (and of a walk, if a collision).
- Readers of the table: compilation_unit, name, name_stamp, kind, user_visible
  (480-488), print (520-530).

SYMBOLS. Table: reference middle_end/flambda2/identifiers/int_ids.ml:568
(replaced at 570). Datum: the symbol of utils/symbol.ml:21-25 (unit, linkage
name, and a stored hash of the linkage name). E.hash: that stored field
(utils/symbol.ml:42; it is Hashtbl.hash of the linkage name: 92, 98, 109, 116,
122). E.equal (utils/symbol.ml:30-40): physical equality, or equal stored hashes
and equal linkage names.
- Makers: Symbol.create (middle_end/flambda2/identifiers/int_ids.ml:583-593),
  unsafe_create (576-577), for_compilation_unit (597), import (638-639): they
  build the datum from their arguments and add it. No counter. The same unit and
  linkage name give the same symbol.
- Symbol.manufacture (middle_end/flambda2/identifiers/symbol.ml:22-34):
  INCREMENTS ITS OWN COUNTER (line 23), reads a flag
  (Flambda_features.Expert.shorten_symbol_names), then Symbol.create: a FRESH
  NAME.
- Readers: compilation_unit (595), linkage_name (599), print (610-615).

CONSTANTS. Table: reference middle_end/flambda2/identifiers/int_ids.ml:366
(replaced at 368). Datum: Const_data (41-58), fifteen constructors. E.hash
(234-251): the hash of the payload only; see T4. E.equal (199-232): same
constructor and equal payloads.
- Makers: Const.create (374) and all that call it: naked_immediate,
  tagged_immediate, naked_float32, naked_float, naked_int8, naked_int16,
  naked_int32, naked_int64, naked_nativeint, naked_vec128, naked_vec256,
  naked_vec512, naked_mask (376-400); const_true, const_false,
  untagged_const_true, untagged_const_false, untagged_const_zero,
  untagged_const_int, const_int, const_zero, const_one, const_unit (402-427);
  const_poison (431); Reg_width_const.of_descr and of_int_of_kind
  (middle_end/flambda2/identifiers/reg_width_const.ml:19-35, 182-224); the
  Simple versions of middle_end/flambda2/term_basics/simple.ml:20-53, 77;
  Const.import (465-466). No counter.
- const_null (429) is a VALUE: the Null constant is interned once, when the
  module is initialised, in the table of that time.
- Readers: descr (433, 370), print (442), and all of
  middle_end/flambda2/identifiers/reg_width_const.ml:37-180 (is_naked_immediate
  and the like, kind).

SIMPLES. A Simple is the integer of a variable, of a symbol or of a constant,
unchanged; or, for a name with a coercion that is not the identity, an integer
with flags 3 from the table of Simples.
- Simple.var, vars, symbol, const, name
  (middle_end/flambda2/identifiers/int_ids.ml:735-743): identities. No table.
- Table: reference middle_end/flambda2/identifiers/int_ids.ml:727 (replaced at
  729). Datum: Simple_data (695-718): the underlying identifier and the
  coercion. E.hash (708-709): Hashtbl.hash of the pair of the underlying
  identifier and Coercion.hash
  (middle_end/flambda2/identifiers/coercion0.ml:111-114;
  middle_end/flambda2/identifiers/rec_info_expr0.ml:185-193). E.equal (711-717):
  equal identifiers and Coercion.equal.
- Maker: Simple.with_coercion (814-825): returns its argument for the identity
  coercion or for a constant; adds to the table for a name without coercion; a
  fatal error (822-825) if the Simple already has a coercion.
  Simple.apply_coercion and apply_coercion_exn
  (middle_end/flambda2/term_basics/simple.ml:82-94) call it. Simple.import
  (839-859). No counter.
- Readers (only for an integer with flags 3): pattern_match (745-764), coercion
  (780-782), same (766-778), print (791-803), and everything built on
  pattern_match: is_var, is_symbol, is_const, pattern_match', must_be_var,
  must_be_symbol, must_be_name, must_be_const, free_names, kind,
  without_coercion (middle_end/flambda2/term_basics/simple.ml:55-138).
- Simple.compare, equal, hash are on the integer (784-789). A name and the same
  name with a coercion are different Simples.

CODE IDENTIFIERS. Table: reference
middle_end/flambda2/identifiers/int_ids.ml:867 (replaced at 869). Datum:
Code_id_data (324-359). E.hash (342-345): the hash of the linkage name
(utils/linkage_name.ml:22-27, Hashtbl.hash of a string). E.equal (347-358):
equal linkage names.
- Maker: Code_id.create (883-912): INCREMENTS THE COUNTER of
  middle_end/flambda2/identifiers/int_ids.ml:881 (a fatal error at 885-886 if it
  is at its maximum); reads the mangling scheme
  (utils/compilation_unit.ml:707-716) and a flag; puts the stamp in the linkage
  name; adds. Code_id.rename (914-915) calls it. A FRESH NAME. Code_id.import
  (960-961).
- Readers: get_compilation_unit, linkage_name, name, debug (873-879),
  is_imported (920), print (929-931).

CONTINUATIONS. Table: reference
middle_end/flambda2/identifiers/continuation.ml:103 (replaced at 105). Datum
(55-61): unit, name, stamp, sort. E.hash (74-75): Hashtbl.hash of the pair of
the hash of the unit and the stamp. E.equal (77-96): same stamp and same unit.
- Maker: Continuation.create (109-122): reads the current unit (a fatal error if
  none), INCREMENTS THE COUNTER of lines 21-25, reads a flag
  (Flambda_features.debug_flambda2), adds. rename (126-128) and
  import_and_rename (177-181) call it. A FRESH NAME. import (174-175).
- Readers: name, name_stamp, sort (135-139), is_renamed_version_of (130-133),
  print (148-153).
- compare and equal are on the integer (142, 144); hash is Hashtbl.hash of the
  integer (146).

NAMES, CODE_ID_OR_SYMBOL, CODE_ID_OR_NAME
(middle_end/flambda2/identifiers/int_ids.ml:642-690, 964-1017, 1019-1074): no
table of their own. Their makers are identities. Their pattern_match looks at
the flags only (a fatal error or an assertion for other flags: 659, 978, 1039).

FIELDS of the reaper (middle_end/flambda2/identifiers/field.ml:144-160): one
more table of the same functor, never replaced; Field.create adds. Not used by
Simplify as far as was seen; its lines 15-119 were not read.

### T4. The hash of a constant, and collisions that always happen
Const_data.hash (middle_end/flambda2/identifiers/int_ids.ml:234-251) gives, for
each constructor, the hash of the payload and nothing of the constructor:
- Naked_immediate and Tagged_immediate: both Target_ocaml_int.hash of the number
  (236, 237), which is Hashtbl.hash of the 64-bit (or 32-bit) integer inside
  (middle_end/flambda2/numbers/target_ocaml_int.ml:290-293, 25-32, 145-152;
  middle_end/flambda2/numbers/one_bit_fewer.ml:129).
- Naked_int64: Hashtbl.hash of the 64-bit integer (243). Naked_nativeint: the
  same on its integer (middle_end/flambda2/numbers/targetint_32_64.ml:348-349).
  Naked_int32: Hashtbl.hash of the 32-bit integer (242). Naked_int8,
  Naked_int16: Hashtbl.hash of the integer
  (middle_end/flambda2/numbers/numeric_types.ml:91, 100-106).
- Naked_float: Hashtbl.hash of the bit pattern, which is a 64-bit integer
  (middle_end/flambda2/numbers/numeric_types.ml:283, 289, 330-331).
  Naked_float32: the same on a 32-bit integer
  (middle_end/flambda2/numbers/numeric_types.ml:366-367). Vectors and masks:
  Hashtbl.hash of an array of 64-bit integers
  (middle_end/flambda2/numbers/vector_types.ml:30, 43).
- Null: Hashtbl.hash of zero (249). Poison: Hashtbl.hash of the pair of the hash
  of the kind and the hash of the string (250-251).

So, shown from the code: for one same number n, the constants Naked_immediate n
and Tagged_immediate n have the SAME starting identifier. On a 64-bit target, so
have Naked_int64 n, Naked_nativeint n, and the Naked_float whose bit pattern is
n (the same function on the same 64-bit integer; for example the float zero and
the integer zeros). Whichever of them is added first in a run takes the starting
identifier; the next takes the one after; and so on. The same holds for
Naked_int8 n and Naked_int16 n, and for Naked_int32 n and the Naked_float32 of
bit pattern n.

Consequence for a record: if two fields each may intern a constant, and the two
constants can be such a pair (for example the tagged and the untagged zero, or
the tagged and the untagged true) and neither is in the table yet, their
identifiers depend on the order of the fields. That is a REPORT by the rule of
README.md, section 2.

For a Poison constant the hash mixes the kind and the string, so a collision
with another datum is an accident of the hash, not a rule. Hashtbl.hash gives a
number below 2^30 (knowledge of OCaml's runtime, not read), so such accidents
are rare but not impossible in a large table.

### T5. Counters and stamps outside the tables
- Value slots and function slots are RECORDS, not integers in a table
  (middle_end/flambda2/identifiers/slot.ml:50-56). Slot.Make(_).create (112-113)
  and rename (130) INCREMENT a counter (105-110); there is one counter for
  function slots and one for value slots (one per application of the functor:
  middle_end/flambda2/identifiers/function_slot.ml:17,
  middle_end/flambda2/identifiers/value_slot.ml:17). FRESH NAMES. The
  projections (payload, name, get_compilation_unit, Value_slot.kind,
  Value_slot.is_always_immediate, Function_slot.size) read fields only.
  Comparison: middle_end/flambda2/identifiers/slot.ml:61-78. hash: 82-83.
- Apply_cont_rewrite_id.create
  (middle_end/flambda2/identifiers/apply_cont_rewrite_id.ml:19-24) and
  Named_rewrite_id.create
  (middle_end/flambda2/identifiers/named_rewrite_id.ml:19-24): each INCREMENTS
  its own counter. FRESH. Both types are integers with the sets and maps of
  Stdlib (middle_end/flambda2/numbers/numeric_types.ml:17-38 through
  Container_types.Make).
- Flambda_debug_uid
  (middle_end/flambda2/identifiers/flambda_debug_uid.ml:21-82): plain data, no
  table, no counter. Flambda_debug_uid.none (33) is a constant.

### T6. When a table is replaced
Int_ids.initialise (middle_end/flambda2/identifiers/int_ids.ml:1076-1081),
Int_ids.reset (1083), Continuation.initialise and reset
(middle_end/flambda2/identifiers/continuation.ml:105, 107) put a new empty table
in each reference. They are called from Flambda2.reset_symbol_tables
(middle_end/flambda2/flambda2.ml:330-333), itself called at
middle_end/flambda2/flambda2.ml:344 and 360, after a unit is compiled, unless
keep_symbol_tables is set. The counters are NOT reset by these functions. An
identifier made before a replacement is not in the new table.

### T7. Sets and maps of identifiers
- Variable, Symbol, Name, Const (Reg_width_const), Simple, Code_id,
  Code_id_or_symbol, Continuation: Set and Map are Patricia_tree.Make applied to
  a printer only (middle_end/flambda2/identifiers/int_ids.ml:453-458, 541-546,
  626-631, 684-689, 827-832, 942-947, 1006-1011;
  middle_end/flambda2/identifiers/continuation.ml:164-166). The key is the
  integer. No comparison function, no hash function and no table is used by add,
  find, mem, remove, update, union, fold or iter. The printer is used only by
  print, to_string and the message of disjoint_union.
- All these operations are persistent: they return new immutable trees and write
  nothing (whole file read: no reference, no mutable field, except the
  Mutable_iterator, which the caller makes).
- A fold or an iter walks the keys in increasing order of the integer
  (middle_end/flambda2/algorithms/patricia_tree.ml:1398-1446). So the order of a
  walk is the order of the identifiers: flags first, then hash bits.
- The shape of a tree depends on its set of keys only, not on the order of the
  additions (the usual property of these trees; Map.equal at
  middle_end/flambda2/algorithms/patricia_tree.ml:1573-1593 compares shapes and
  relies on it; no proof was written). Two maps with the same bindings made in
  two orders are equal in structure, but they are not the same blocks: a test of
  physical equality between them can differ.
- Map.add (middle_end/flambda2/algorithms/patricia_tree.ml:703-707) adds a
  binding or replaces the datum of a key that is there.
- Function_slot, Value_slot: Set and Map are Stdlib's, on the comparison of
  middle_end/flambda2/identifiers/slot.ml:61-78.
- Code_id_or_name: Set and Map come from Datalog.Column.Make
  (middle_end/flambda2/identifiers/int_ids.ml:1064-1071): NOT READ. Lmap
  (middle_end/flambda2/identifiers/int_ids.ml:547, 948, 1012;
  middle_end/flambda2/identifiers/continuation.ml:167;
  middle_end/flambda2/identifiers/slot.ml:99):
  middle_end/flambda2/algorithms/lmap.ml NOT READ.

### T8. What this gives for a call met at another place (facts, not verdicts)
- No table, no counter, cannot fail: Simple.var, Simple.symbol, Simple.const,
  Simple.name, Name.var, Name.symbol; compare, equal, hash of every identifier;
  Value_slot.kind and the other projections of a slot; Bound_var.create;
  Bound_pattern.singleton; Named.create_simple; Named.create_prim.
- No state at all, but the result depends on the integers of the keys: Map.add,
  Map.update, Map.remove, Map.singleton, Map.union and the like on Variable,
  Symbol, Name, Simple, Const, Code_id, Continuation. Two of them on two
  different maps commute. Map.find can raise Not_found.
- Reads a table, writes none: every function listed as a reader in T3 (for a
  Simple: only when the integer has flags 3).
- May add to a table, no counter (an interning; the rule of T2 applies): every
  maker of a constant; Symbol.create and its kin; Simple.with_coercion and
  Simple.apply_coercion.
- Makes a fresh name (a counter): Variable.create, Variable.rename;
  Symbol.manufacture; Code_id.create, Code_id.rename; Continuation.create,
  Continuation.rename; Slot create and rename (Function_slot.create,
  Value_slot.create); Apply_cont_rewrite_id.create; Named_rewrite_id.create.

## WHAT WAS NOT READ, AND DOUBTS

1. Stdlib. Not read: the bodies of Hashtbl (Make, create, find, find_opt, add,
   replace, hash), Map.Make, List (length, fold_left, mapi, map), String (hash,
   equal, compare), Int (compare, equal), Option, Format (kfprintf, fprintf),
   Random.bits, Obj.tag, and the polymorphic compare. Their documented behaviour
   was used: Hashtbl.hash and String.hash are functions of the value with no
   state; a functorial hash table is a mutable table whose find raises
   Not_found; Map.Make gives persistent maps.
2. Printers. Named.print and all that it calls
   (middle_end/flambda2/terms/flambda.ml:868-885 and below), E.print of the
   tables, Flambda_colours, Flambda_features: not read. They run at the places
   of this part only on paths that end in a fatal error.
3. Completeness of the matches of middle_end/flambda2/terms/code_size_v1.ml.
   Each match was not checked against the definition of its type
   (unary_int_arith_op and the comparison type only were checked). The file
   turns off the warning for fragile matches (line 17) but not the warning for
   incomplete ones; the root dune file turns the warnings on in its three
   profiles (dune:17-38) and makes them errors in the profiles main and dev
   (dune:26-27, 37-38). The matches are taken as complete on that ground. If one
   were not, the failure would be a Match_failure in Code_size.prim, and place
   22 would have it among its failures (still one call only).
4. The shape of a Patricia tree as a function of its keys only (T7): argued, not
   proved.
5. hash_seed (middle_end/flambda2/identifiers/int_ids.ml:17-19) is drawn once,
   with Random.bits, when the module is initialised. It is a constant after
   that, so it is not a state for the order of two calls. Whether it is the same
   from one run of the compiler to the next depends on nothing seeding the
   default generator before; no call of Random.self_init was found in the
   compiler's own directories (the search left out external/, stdlib/,
   otherlibs/, testsuite/). This matters for the identifiers of variables across
   runs, not for the three places.
6. The range of Hashtbl.hash (below 2^30) is from knowledge of the runtime, not
   from this tree. That Hashtbl.hash gives the same number for one same 64-bit
   integer whatever the OCaml type it is seen at is its documented behaviour (it
   depends on the value only); the collisions of T4 rest on it.
7. Hosts of 32 bits. The layout of an identifier uses Sys.int_size
   (middle_end/flambda2/algorithms/table_by_int_id.ml:24-26) and the Patricia
   trees assume 63-bit integers
   (middle_end/flambda2/algorithms/patricia_tree.ml:56). Read for a 64-bit host
   only.
8. Replacement of the tables (T6). Read: where reset_symbol_tables is called
   (middle_end/flambda2/flambda2.ml:344, 360) but not the whole of those two
   functions, nor the drivers. Assumed: no table is replaced while Simplify runs
   on a unit. If one were, a Simple with a coercion made before would make
   Simple.pattern_match raise Not_found (this is the only failure on the path of
   place 22 that is not excluded by a type or by a count).
9. Not read at all: middle_end/flambda2/algorithms/lmap.ml; the Datalog column
   maps; middle_end/flambda2/identifiers/field.ml:15-119;
   Set_of_closures.free_names and Static_const_group.free_names (not reachable
   from Simplified_named.create); Unit_info.modname and the rest of
   typing/current_unit.ml beyond lines 16-44 (used by Variable.create and
   Continuation.create, not by the places of this part);
   Compilation_unit.mangle_for_linkage_name and Structured_mangling (used by
   makers of symbols and code identifiers, not by the places of this part);
   Flambda_features.
10. Lack of memory and overflow of the stack are not counted as failures
    anywhere above.
11. Place 22: that named is always a Prim, and that the fresh variable is made
    before the record, was read from lines 356-388 of the file. The constructor
    Prim of the local type (line 293) is built at one point only, in bound_prim
    (line 304; search of the file), and bound_prim is called at the seven sites
    that are listed. The entries cover every primitive, so the verdict does not
    rest on this.
12. Place 23: the other unboxers of the file (lines 42-223) intern their poison
    constants when the module is initialised. They are not part of the place.
13. An observation, outside the three places: Const.const_null is interned once,
    at the initialisation of the module
    (middle_end/flambda2/identifiers/int_ids.ml:429). After a replacement of the
    table of constants (T6) the Null datum is not in the new table until
    something adds it again; Const.descr of it would then raise Not_found.
    Whether any path does that was not checked.
