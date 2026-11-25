# Record order, part 2: places 5 to 10

The reading of the compiler's code for places 5 to 10. `README.md` of this
folder has the question, the sense and the table of places.

Commit read: `4fe46bb689903ead25d346ac9efd3c883821f171` (`git rev-parse HEAD` in
the tree that was read).

Method: reading only (`rg`, `sed -n`, `cat -n`). Nothing was built and nothing
was run. The port (the `.v` files) was not read; this part is about the compiler
only.

Paths are from the root of the repository.

## VERDICTS, IN SHORT

| place | definition | verdict |
|---|---|---|
| P5 | `apply_prim`, `middle_end/flambda2/simplify/flow/mutable_unboxing.ml` 450-452 | COMMUTE |
| P6 | `apply_prim`, `middle_end/flambda2/simplify/flow/mutable_unboxing.ml` 463-465 | COMMUTE |
| P7 | `create_block_like`, `middle_end/flambda2/simplify/lifting/lifted_constant.ml` 180-185 | COMMUTE |
| P8 | `create_set_of_closures`, same file 198-203 | COMMUTE, FAILURES ORDERED (one call can fail) |
| P9 | `create_code`, same file 212-217 | COMMUTE, FAILURES ORDERED (one call can fail; that call also writes caches) |
| P10 | `create_definition`, same file 221-227 | COMMUTE, FAILURES ORDERED (two calls can fail; one of them also writes caches) |

No call of these six places makes a fresh name.

## CONVENTIONS OF THIS PART

- LEAF(read): the body was read and it calls nothing more (a constructor, a
  field projection, integer arithmetic).
- LEAF(stdlib): a function of OCaml's standard library; W, R, F, A are from its
  documented behaviour. Where the body in `stdlib/` of this tree was also read,
  the entry says so.
- Exhaustion of memory or of the stack is not counted as a failure.
- An assertion is counted as a failure site (it disappears if assertions are
  compiled out).

Facts on how the names resolve (read in the `dune` files and at the head of the
two files):

- `middle_end/flambda2/simplify/dune` opens, for every file of Simplify, the
  libraries of `middle_end/flambda2/algorithms`,
  `middle_end/flambda2/bound_identifiers`, `middle_end/flambda2/identifiers`,
  `middle_end/flambda2/kinds`, `middle_end/flambda2/nominal`,
  `middle_end/flambda2/numbers`, `middle_end/flambda2/term_basics`,
  `middle_end/flambda2/terms`, `middle_end/flambda2/types`,
  `middle_end/flambda2/ui` and others. The only files named `simple`,
  `named_rewrite_id`, `bound_static` and `rebuilt_static_const` in those
  libraries are `middle_end/flambda2/term_basics/simple.ml`,
  `middle_end/flambda2/identifiers/named_rewrite_id.ml`,
  `middle_end/flambda2/bound_identifiers/bound_static.ml` and
  `middle_end/flambda2/simplify/rebuilt_static_const.ml`.
- `middle_end/flambda2/simplify/flow/mutable_unboxing.ml` makes two
  abbreviations only (lines 15-16, `T` and `EPA`) and one inner module
  (`Fold_prims`, 355). `middle_end/flambda2/simplify/lifting/lifted_constant.ml`
  makes one abbreviation (line 17, `T`) and one inner module (`Definition`,
  19-137). None of the names used at the six places is rebound.
- The containers are not under `utils/`. They are
  `middle_end/flambda2/algorithms/container_types.ml`,
  `middle_end/flambda2/algorithms/container_types_intf.ml`,
  `middle_end/flambda2/algorithms/patricia_tree.ml`,
  `middle_end/flambda2/algorithms/lmap.ml`,
  `middle_end/flambda2/algorithms/table_by_int_id.ml`.
- In native builds each of these libraries opens
  `Int_replace_polymorphic_compare` (`utils/int_replace_polymorphic_compare.ml`
  1-8): the comparison operators written in these files are comparisons of
  integers.

## FUNCTIONS

### Part 1. Functions of P5 and P6

### F: Simple.Map.add
defined: `middle_end/flambda2/algorithms/patricia_tree.ml`:703-707. Chain to the
body: `middle_end/flambda2/term_basics/simple.ml`:18 (the module includes
`Int_ids.Simple`) -> `middle_end/flambda2/identifiers/int_ids.ml`:827-832
(`Tree` is `Patricia_tree.Make` applied to a module that holds a printer and
nothing else; `Map` is `Tree.Map`) ->
`middle_end/flambda2/algorithms/patricia_tree.ml`:2229-2245 (the functor `Make`;
its `Map` includes the top-level `Map`) -> 2186-2189 (the top-level `Map`
includes `Map0` and `Tree_operations` applied to `Map0`) -> 703-707.
calls: `Map0.is_value_of` (376), `Map0.descr` (410-414), `Map0.leaf` (380),
`Map0.of_tree` (372): each LEAF(read), a constructor or a match on a
constructor. `add_tree` (entry below).
W: none
R: none
F: none
A: none. The result is a new immutable tree that shares nodes with the argument.
read: `middle_end/flambda2/algorithms/patricia_tree.ml`:17-95, 360-467, 603-707,
2186-2293; `middle_end/flambda2/identifiers/int_ids.ml`:720-860;
`middle_end/flambda2/term_basics/simple.ml`:1-240.
note: this map takes NO comparison function. The key is the integer that
represents the `Simple`, and the tree compares its bits. The only thing the
functor is given is a printer (`Int_ids.Simple.print`,
`middle_end/flambda2/identifiers/int_ids.ml`:791-803); the printer reads the
tables of identifiers, but `add` does not call it (it is called by the printing
functions of the map and by the error path of `disjoint_union`,
`middle_end/flambda2/algorithms/patricia_tree.ml`:2264-2290).

### F: Patricia_tree.Tree_operations.add_tree ..
heading: F: Patricia_tree.Tree_operations.add_tree (not exported; the worker of
`add`)
defined: `middle_end/flambda2/algorithms/patricia_tree.ml`:684-701, recursive.
calls: `is_value_of_tree` (606), `tree_descr` (401-404), `leaf_key` (385),
`leaf` (380), `branch_prefix_and_bit` (389-391), `branch0` (393), `branch1`
(395), `branch_non_empty` (639-641, which calls `Map0.branch`, 382-383),
`join_non_empty` (667-672): each LEAF(read), constructors and matches. `unpack`
(45-49), `pack` (51), `zero_bit` (53), `highest_bit` (56), `branching_bit` (59),
`mask` (62), `match_prefix` (66): each LEAF(read), integer arithmetic. `int_clz`
(19-21): LEAF, a primitive (an external that counts leading zeros, declared
without allocation and without effects).
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/algorithms/patricia_tree.ml`:17-95, 360-467, 603-707.

### F: Named_rewrite_id.Map.add
defined: `stdlib/map.ml`:129-141 (the functor `Map.Make` of the standard
library). Chain to the body:
`middle_end/flambda2/identifiers/named_rewrite_id.ml`:17 (the module includes
`Numeric_types.Int`) -> `middle_end/flambda2/numbers/numeric_types.ml`:29-32
(`Int` includes `Int_base`) -> 17-27 (`Int_base` is `Container_types.Make`
applied to the integers, with the comparison of the standard library on
integers) -> `middle_end/flambda2/algorithms/container_types.ml`:316-321
(`Make`: `Map` is `Make_map`) -> 33-34 (`Make_map` includes `Map.Make` of the
standard library; `add` is not redefined in 35-265).
calls: LEAF(stdlib): `Map.Make(Ord).add`. Documented: returns a map, raises
nothing.
The comparison it is given: `Int.compare` of the standard library
(`middle_end/flambda2/numbers/numeric_types.ml`:20; `stdlib/int.ml`:44), a
comparison of two integers.
W: none
R: none
F: none
A: none. The result is immutable; it is the argument itself when the key is
already bound to the physically same datum.
read: `middle_end/flambda2/identifiers/named_rewrite_id.ml`:1-24;
`middle_end/flambda2/numbers/numeric_types.ml`:17-38;
`middle_end/flambda2/algorithms/container_types.ml`:1-333;
`stdlib/map.ml`:77-141 (read as a check: `add`, `bal`, `create`, `height`. `bal`
has four sites that raise `Invalid_argument`, lines 100, 106, 112, 118, each on
a tree whose heights are wrong, which this module cannot build).
note: the comparison reads no table. The counter of this module
(`middle_end/flambda2/identifiers/named_rewrite_id.ml`:19, used by `create`,
21-24) is not touched by `Map.add`.

### F: Simple.var
defined: `middle_end/flambda2/identifiers/int_ids.ml`:737 (through
`middle_end/flambda2/term_basics/simple.ml`:18;
`middle_end/flambda2/term_basics/simple.ml` does not redefine it; signature at
`middle_end/flambda2/identifiers/int_ids.mli`:208).
calls: nothing. LEAF(read): it returns its argument. A variable and the `Simple`
made from it are the same integer.
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/identifiers/int_ids.ml`:720-764;
`middle_end/flambda2/term_basics/simple.ml`:1-240.
note: no table is read or written. The functions of this module that DO go
through the table of simples (`middle_end/flambda2/identifiers/int_ids.ml`:727)
are `pattern_match` (745-764, reads it when the `Simple` carries a coercion),
`coercion` (780-782, reads) and `with_coercion` (814-825, may add an entry).
None of them is called at P5 or P6.

### Part 2. Functions of P7 to P10 that every call reaches

### F: Lifted_constant.compute_bound_static
defined: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:163-165
calls: `ListLabels.map`: LEAF(stdlib), applies the function to each element, no
effect of its own. `Definition.bound_static_pattern` (entry below).
`Bound_static.create` (entry below).
W: none on the path that returns. On the failure path of `Bound_static.create`:
the error formatter (see `Misc.fatal_errorf`).
R: `Clflags.flambda_invariant_checks`, `utils/clflags.ml`:313-315 (through
`Bound_static.create`).
F: `middle_end/flambda2/bound_identifiers/bound_static.ml`:131-134 (through
`Bound_static.create`): only when the heavy invariant checks are on AND the list
of patterns defines some symbol or code identifier twice.
A: none (a list of immutable patterns).
read: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:1-324.

### F: Lifted_constant.Definition.bound_static_pattern
defined: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:117-123
calls: `Bound_static.Pattern.code`
(`middle_end/flambda2/bound_identifiers/bound_static.ml`:23),
`Bound_static.Pattern.block_like` (27), `Bound_static.Pattern.set_of_closures`
(25): each LEAF(read), a constructor. `Function_slot.Lmap.map` (entry below),
given `fst`: LEAF, a primitive projection of a pair.
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:19-137;
`middle_end/flambda2/bound_identifiers/bound_static.ml`:17-111.

### F: Function_slot.Lmap.map
defined: `middle_end/flambda2/algorithms/lmap.ml`:138. Chain:
`middle_end/flambda2/identifiers/function_slot.ml`:17-23 (the module is
`Slot.Make` applied) -> `middle_end/flambda2/identifiers/slot.ml`:99-103 (`Lmap`
is `Lmap.Make`) -> `middle_end/flambda2/algorithms/lmap.ml`:80-138. The map is a
list of pairs.
calls: `List.map`: LEAF(stdlib).
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/algorithms/lmap.ml`:80-140;
`middle_end/flambda2/identifiers/slot.ml`:43-131;
`middle_end/flambda2/identifiers/function_slot.ml`:15-30.

### F: Bound_static.create
defined: `middle_end/flambda2/bound_identifiers/bound_static.ml`:140-143
calls: `Flambda_features.check_invariants` (entry below);
`check_pattern_list_invariant` (entry below), only when the first answers true.
It returns its argument.
W: none on the path that returns; the error formatter on the failure path.
R: `Clflags.flambda_invariant_checks`, `utils/clflags.ml`:313-315.
F: `middle_end/flambda2/bound_identifiers/bound_static.ml`:131-134, the
condition of `check_pattern_list_invariant`.
A: none
read: `middle_end/flambda2/bound_identifiers/bound_static.ml`:1-176.

### F: Flambda_features.check_invariants
defined: `middle_end/flambda2/ui/flambda_features.ml`:161-164
calls: nothing. LEAF(read): it reads one reference and answers true only for the
heavy checks.
W: none
R: `Clflags.flambda_invariant_checks`, `utils/clflags.ml`:313-315. In the whole
tree this reference is assigned only by the driver
(`driver/main_args.ml`:2372-2378, the three options of the command line;
`driver/compenv.ml`:481-482), by a search of every use of the name.
F: none
A: none
read: `middle_end/flambda2/ui/flambda_features.ml`:1-40, 159-170;
`utils/clflags.ml`:310-316.

### F: Bound_static.check_pattern_list_invariant
defined: `middle_end/flambda2/bound_identifiers/bound_static.ml`:117-134
calls: `List.map`, `List.concat`, `List.compare_length_with`: LEAF(stdlib).
`Pattern.everything_being_defined_as_list` (entry below).
`Code_id_or_symbol.Set.of_list`, `Code_id_or_symbol.Set.cardinal` (entries
below). On failure: `Misc.fatal_errorf` (entry below) with
`Format.pp_print_list` (LEAF(stdlib)) and `Pattern.print` (entry below).
W: none on the path that returns; the error formatter on the failure path.
R: none on the path that returns.
F: `middle_end/flambda2/bound_identifiers/bound_static.ml`:131-134: when the
number of things defined by the patterns differs from the number of distinct
things defined, that is when some symbol or code identifier is defined twice.
A: none
read: `middle_end/flambda2/bound_identifiers/bound_static.ml`:113-143.

### F: Bound_static.Pattern.everything_being_defined_as_list
defined: `middle_end/flambda2/bound_identifiers/bound_static.ml`:87-93
calls: `Code_id_or_symbol.create_code_id`
(`middle_end/flambda2/identifiers/int_ids.ml`:967),
`Code_id_or_symbol.create_symbol`
(`middle_end/flambda2/identifiers/int_ids.ml`:969), through
`middle_end/flambda2/identifiers/code_id_or_symbol.ml`:15: each LEAF(read),
returns its argument. `Function_slot.Lmap.data`
(`middle_end/flambda2/algorithms/lmap.ml`:121; LEAF over `List.map` and `snd`).
`List.map`: LEAF(stdlib).
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/bound_identifiers/bound_static.ml`:87-93;
`middle_end/flambda2/identifiers/int_ids.ml`:964-1017;
`middle_end/flambda2/algorithms/lmap.ml`:119-125.

### F: Code_id_or_symbol.Set.of_list
defined: `middle_end/flambda2/algorithms/patricia_tree.ml`:2181, which calls
2067-2070. Chain: `middle_end/flambda2/identifiers/int_ids.ml`:1006-1010 ->
`middle_end/flambda2/algorithms/patricia_tree.ml`:2233-2234 -> 2104-2184.
calls: `List.fold_left`: LEAF(stdlib). The `add` of `Tree_operations` (703-707,
684-701: the same code as `Simple.Map.add` above) over the constructors of sets
(230-356), with the two projections of a binding of a set (305, 307), each
LEAF(read).
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/algorithms/patricia_tree.ml`:230-356, 2067-2070,
2104-2184.

### F: Code_id_or_symbol.Set.cardinal
defined: `middle_end/flambda2/algorithms/patricia_tree.ml`:1395-1396 and
1390-1393
calls: constructors and matches only. LEAF(read).
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/algorithms/patricia_tree.ml`:1390-1396.

### F: Misc.fatal_errorf
defined: `utils/misc.ml`:20-24 (the exception is declared at line 18)
calls: `Format.kfprintf` on `Format.err_formatter`: LEAF(stdlib).
W: the standard error channel, through the error formatter of `Format`.
R: the state of that formatter.
F: always: it raises `Misc.Fatal_error` after it has printed.
A: none
read: `utils/misc.ml`:16-26.

### F: Bound_static.Pattern.print ..
heading: F: Bound_static.Pattern.print (reached only when
`check_pattern_list_invariant` fails)
defined: `middle_end/flambda2/bound_identifiers/bound_static.ml`:29-37
calls: the printers of `Misc.Sexp`, `Code_id.print`
(`middle_end/flambda2/identifiers/int_ids.ml`:929-931),
`Function_slot.Lmap.print`, `Symbol.print`
(`middle_end/flambda2/identifiers/int_ids.ml`:610-615). NOT read down to leaves.
W: the formatter it is given (here the error formatter).
R: the table of code identifiers
(`middle_end/flambda2/identifiers/int_ids.ml`:867) and the table of symbols
(`middle_end/flambda2/identifiers/int_ids.ml`:568), for the entries of the
identifiers that it prints; settings of colours.
F: not determined (the call that reaches it is already raising).
A: none
read: `middle_end/flambda2/bound_identifiers/bound_static.ml`:29-37;
`middle_end/flambda2/identifiers/int_ids.ml`:563-640, 862-962.

### F: Lifted_constant.compute_defining_exprs
defined: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:167-169
calls: `ListLabels.map`: LEAF(stdlib). `Definition.defining_expr` (entry below).
`Rebuilt_static_const.Group.create` (entry below).
W: none
R: none
F: none
A: the group that it returns is a fresh record with one mutable field (see
`Rebuilt_static_const.Group.create`).
read: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:163-169.

### F: Lifted_constant.Definition.defining_expr
defined: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:87
calls: nothing. LEAF(read): a projection of an immutable field (the type is at
35-38).
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:19-137.

### F: Rebuilt_static_const.Group.create
defined: `middle_end/flambda2/simplify/rebuilt_static_const.ml`:421 (the type is
at 414-417)
calls: nothing. LEAF(read): it builds a record.
W: none
R: none
F: none
A: yes: a fresh record whose field `free_names` is mutable. It is a cache: it
starts as "unknown" and is assigned later by `Group.free_names` (427-437, the
assignment is at 436). `Group.create` does not look inside the constants that it
is given.
read: `middle_end/flambda2/simplify/rebuilt_static_const.ml`:413-522.

### F: Rebuilt_static_const.is_fully_static
defined: `middle_end/flambda2/simplify/rebuilt_static_const.ml`:369
calls: `Rebuilt_static_const.free_names` (entry below), then
`Name_occurrences.no_variables` (entry below).
W, R, F, A: the union of the two entries below. In short:
- when the constant is `Normal`, `Block_not_rebuilt` or
  `Set_of_closures_not_rebuilt`: W none, R none, F none that can be reached (see
  `Name.is_var`), A none;
- when the constant is `Code_not_rebuilt`: it WRITES caches and may write a
  table that interns, it reads tables, and it can fail (Part 3).
read: `middle_end/flambda2/simplify/rebuilt_static_const.ml`:1-522.

### F: Rebuilt_static_const.free_names
defined: `middle_end/flambda2/simplify/rebuilt_static_const.ml`:361-367 (the
type is at 24-38, no mutable field)
calls: for `Normal`, `Block_not_rebuilt`, `Set_of_closures_not_rebuilt`:
nothing, a projection of the stored field. For `Code_not_rebuilt`:
`Non_constructed_code.free_names` (Part 3).
W: none for the three first constructors. For `Code_not_rebuilt`: see Part 3.
R: none for the three first constructors. For `Code_not_rebuilt`: see Part 3.
F: none for the three first constructors. For `Code_not_rebuilt`: see Part 3.
A: none
read: `middle_end/flambda2/simplify/rebuilt_static_const.ml`:24-58, 361-369.
note: this is the function that "looks like a projection". It is one for three
constructors out of four.

### F: Name_occurrences.no_variables
defined: `middle_end/flambda2/nominal/name_occurrences.ml`:755-756
calls: `For_names.for_all` (307; `For_names` is made at 334-338 from the
functors at 17-313 and 315-332), which calls `Name.Map.for_all`
(`middle_end/flambda2/algorithms/patricia_tree.ml`:1454-1462, with 1448-1452,
1398-1413 and the call of the callback at 429; `Name.Map` is a Patricia tree,
`middle_end/flambda2/identifiers/int_ids.ml`:684-689). The callback calls
`Name.is_var` (entry below).
W: none
R: none
F: none that can be reached (see `Name.is_var`).
A: none
read: `middle_end/flambda2/nominal/name_occurrences.ml`:17-383, 734-788;
`middle_end/flambda2/algorithms/patricia_tree.ml`:1395-1477.

### F: Name.is_var
defined: `middle_end/flambda2/identifiers/name.ml`:19
calls: `Int_ids.Name.pattern_match`
(`middle_end/flambda2/identifiers/int_ids.ml`:653-659), which calls
`Table_by_int_id.Id.flags`
(`middle_end/flambda2/algorithms/table_by_int_id.ml`:33, a shift of an integer).
W: none
R: none. The kind of name (variable or symbol) is in the top bits of the
integer; no table is read.
F: `middle_end/flambda2/identifiers/int_ids.ml`:659, an assertion, when the top
bits of the integer say neither "variable" nor "symbol". Not reachable for a
name made through the interface: the type is private
(`middle_end/flambda2/identifiers/int_ids.mli`:176), the only makers are
`Name.var` and `Name.symbol` (`middle_end/flambda2/identifiers/int_ids.ml`:645,
651, both the identity), and a variable or a symbol gets its bits from
`Table_by_int_id.Make.add`
(`middle_end/flambda2/algorithms/table_by_int_id.ml`:75-107), which asserts them
(91, 103, 106).
A: none
read: `middle_end/flambda2/identifiers/name.ml`:15-77;
`middle_end/flambda2/identifiers/int_ids.ml`:642-690;
`middle_end/flambda2/algorithms/table_by_int_id.ml`:15-127.

### F: Lifted_constant.Definition.symbol_projections
defined: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:89-94
calls: nothing. LEAF(read): a match; it returns a stored immutable field, or the
constant `Variable.Map.empty` (a value, not a call) for a definition of code.
W: none
R: none
F: none
A: none
read: `middle_end/flambda2/simplify/lifting/lifted_constant.ml`:19-137.

### Part 3. Functions that `is_fully_static` reaches only for a ..
heading: Part 3. Functions that `is_fully_static` reaches only for a
`Code_not_rebuilt` constant

This case can occur at P9 and P10. It cannot occur at P7 or P8 (see the places).
The chain is long. The entries below group the functions by file; each group
says what it writes, reads and where it can fail. The leaves that were not read
are listed at the end of the part.

### F: Non_constructed_code.free_names
defined: `middle_end/flambda2/simplify/non_constructed_code.ml`:38, an alias of
`Code0.free_names`, `middle_end/flambda2/terms/code0.ml`:86-90 (the type, 17-21,
has no mutable field).
calls: `Code_metadata.free_names`, `Name_occurrences.union` (entries below).
W, R, F: those of the two.
A: none
read: `middle_end/flambda2/simplify/non_constructed_code.ml`:15-41;
`middle_end/flambda2/terms/code0.ml`:15-135.

### F: Code_metadata.free_names
defined: `middle_end/flambda2/terms/code_metadata.ml`:407-450 (the type, 17-48,
has no mutable field)
calls: `Name_occurrences.add_newer_version_of_code_id`,
`Name_occurrences.union`,
`Name_occurrences.downgrade_occurrences_at_strictly_greater_name_mode` (entry
"operations of Name_occurrences" below); `Result_types.free_names` (entry
below), only when the result types are known.
W: those of `Result_types.free_names`.
R: those of `Result_types.free_names`.
F: those of the functions called.
A: none
read: `middle_end/flambda2/terms/code_metadata.ml`:17-50, 400-452.

### F: operations of Name_occurrences used on this path
defined: `middle_end/flambda2/nominal/name_occurrences.ml`: `union` 734-744
(with the first `is_empty`, 645-666, and `binary_op`, 582-643); `diff` 668-732;
`union_list` 788; `singleton_variable` 417-418; `add_variable` 420-421;
`add_name` 426-427; `add_function_slot_in_types` 453-461;
`add_value_slot_in_types` 463-471; `add_code_id` 473-474;
`add_newer_version_of_code_id` 478-482; `create_variables` 490-496;
`downgrade_occurrences_at_strictly_greater_name_mode` 925-988;
`affected_by_renaming` 1095-1112; `apply_renaming` 1041-1093. The functions for
one variety of names are at 201-311 and 323-331; the counter for one name is at
90-199.
calls: functions of maps and sets: Patricia trees for names, variables, code
identifiers and continuations
(`middle_end/flambda2/algorithms/patricia_tree.ml`, read: 643-798, 800-1233,
1356-1396, 1415-1477, 1573-1593, 1755-1785, 1844-1865), and maps of the standard
library for function slots and value slots
(`middle_end/flambda2/algorithms/container_types.ml`:33-265 over `Map.Make`; the
comparison is `middle_end/flambda2/identifiers/slot.ml`:61-78, which compares
two stamps and then two compilation units with `Compilation_unit.compare`,
`utils/compilation_unit.ml`:336-362, a structural comparison that reads no
table). For the renaming functions: `Renaming.apply_name`, `apply_continuation`,
`apply_code_id` (entry below).
W: none (local references inside
`middle_end/flambda2/algorithms/container_types.ml` do not outlive the call).
R: none, except through the functions of `Renaming`.
F: `middle_end/flambda2/nominal/name_occurrences.ml`:106, 111, 115: three
assertions; one fails when the count of the occurrences of one name in one mode
would go above 1,048,575. They are reached from `add` (148-158), `union`
(183-189), the downgrade (160-169).
A: none
read: `middle_end/flambda2/nominal/name_occurrences.ml`:17-788, 920-990,
1040-1113.

### F: Result_types.free_names
defined: `middle_end/flambda2/terms/result_types.ml`:152-156
calls: `Name_abstraction.free_names` (entry below), given the module `Bound`
(18-126) and the functions of `Typing_env_extension.With_extra_variables`.
W, R, F: those of `Name_abstraction.free_names`.
A: none
read: `middle_end/flambda2/terms/result_types.ml`:15-168.

### F: Name_abstraction.free_names
defined: `middle_end/flambda2/nominal/name_abstraction.ml`:122-127
calls: `With_delayed_renaming.descr` (entry below); the function for the free
names of the term (here `Typing_env_extension.With_extra_variables.free_names`);
`Bound.free_names` (`middle_end/flambda2/terms/result_types.ml`:25-34);
`Name_occurrences.diff`.
W: those of `descr` and of the free names of the term.
R: the same.
F: those of the functions called.
A: none
read: `middle_end/flambda2/nominal/name_abstraction.ml`:15-168.

### F: Name_abstraction.With_delayed_renaming.descr
defined: `middle_end/flambda2/nominal/name_abstraction.ml`:63-74 (the type is at
48-52: three MUTABLE fields)
calls: `Renaming.is_identity`
(`middle_end/flambda2/nominal/renaming.ml`:177-195, read: tests of emptiness, no
effect). When the pending renaming is not the identity: the `apply_renaming` of
the bound part (`middle_end/flambda2/terms/result_types.ml`:36-46, then
`middle_end/flambda2/bound_identifiers/bound_parameters.ml`:79-80 and
`middle_end/flambda2/bound_identifiers/bound_parameter.ml`:92-94, 58-69) and the
`apply_renaming` of the term
(`Typing_env_extension.With_extra_variables.apply_renaming`, entry below).
W: `middle_end/flambda2/nominal/name_abstraction.ml`:71-73: when the pending
renaming is not the identity, the three mutable fields of the abstraction are
assigned (the renamed bound part, the renamed term, an empty pending renaming).
The abstraction is the one stored in the result types of the code metadata,
which the constant holds: the state outlives the call.
R: those three fields.
F: those of the renaming functions (below);
`middle_end/flambda2/bound_identifiers/bound_parameter.ml`:65-68, when a renamed
parameter has a kind that differs from the kind of its variable (it reads the
table of variables, `middle_end/flambda2/identifiers/int_ids.ml`:474, through
`Variable.kind`, 486).
A: none
read: `middle_end/flambda2/nominal/name_abstraction.ml`:27-84;
`middle_end/flambda2/nominal/renaming.ml`:132-195;
`middle_end/flambda2/bound_identifiers/bound_parameters.ml`:15-112;
`middle_end/flambda2/bound_identifiers/bound_parameter.ml`:15-101;
`middle_end/flambda2/terms/result_types.ml`:18-126.
note: it does NOT open the abstraction with fresh names. The function that does
(`pattern_match`, 76-83, which calls `import_and_rename`) is not on this path.

### F: Typing_env_extension.With_extra_variables.free_names
defined: `middle_end/flambda2/types/env/typing_env_extension.ml`:111-122
calls: `Variable.Set.of_list`, `Name.Map.fold` (Patricia trees),
`Name_occurrences` operations, `Type_grammar.free_names` (entry below).
W, R, F: those of `Type_grammar.free_names` and of `Name_occurrences`.
A: none
read: `middle_end/flambda2/types/env/typing_env_extension.ml`:15-157.

### F: Type_grammar.free_names
defined: `middle_end/flambda2/types/grammar/type_grammar.ml`:729, which calls
`free_names0`, 439-724 (a group of mutually recursive functions over the grammar
of types, 148-337).
calls: `Type_descr.free_names` (entry below) for each node; `Name_occurrences`
operations; `Simple.free_names`
(`middle_end/flambda2/term_basics/simple.ml`:123-129, which calls
`Int_ids.Simple.pattern_match` and `Coercion.free_names`,
`middle_end/flambda2/term_basics/coercion.ml`:17-23);
`Rec_info_expr.free_names_in_types`
(`middle_end/flambda2/term_basics/rec_info_expr.ml`:32-40);
`Set_of_closures_contents.free_names`
(`middle_end/flambda2/types/grammar/set_of_closures_contents.ml`:74-78);
`Or_unknown.free_names` (`middle_end/flambda2/lattices/or_unknown.ml`:57-60);
folds over maps, sets and arrays.
W: through `Type_descr.free_names`: the cache of free names of every node of the
type that is visited and has no cached value yet.
R: those caches; the table of simples
(`middle_end/flambda2/identifiers/int_ids.ml`:727) for an alias that carries a
coercion (`middle_end/flambda2/identifiers/int_ids.ml`:745-764, 731).
F: the assertions of `Name_occurrences` (above);
`middle_end/flambda2/algorithms/table_by_int_id.ml`:110-111 (an assertion on the
bits of the identifier, and `Not_found` if the table has no entry), not
reachable for a `Simple` made through the interface.
A: none
read: `middle_end/flambda2/types/grammar/type_grammar.ml`:15-736;
`middle_end/flambda2/term_basics/simple.ml`:123-131;
`middle_end/flambda2/term_basics/coercion.ml`:15-55;
`middle_end/flambda2/term_basics/rec_info_expr.ml`:15-45;
`middle_end/flambda2/types/grammar/set_of_closures_contents.ml`:15-132.

### F: Type_descr.free_names
defined: `middle_end/flambda2/types/grammar/type_descr.ml`:230-236 (with
`Descr.free_names`, 126-131)
calls: `With_cached_free_names.free_names` (entry below) for a node that is not
an alias; `Simple.free_names` and a downgrade of `Name_occurrences` for an
alias.
W, R, F: those of the functions called.
A: none
read: `middle_end/flambda2/types/grammar/type_descr.ml`:15-311.

### F: With_cached_free_names.free_names
defined: `middle_end/flambda2/types/grammar/with_cached_free_names.ml`:26-33
(the type is at 17-20: one MUTABLE field, the cache)
calls: the function for the free names of the head, only when the cache is
empty.
W: `middle_end/flambda2/types/grammar/with_cached_free_names.ml`:32: when the
cache is empty, the mutable field is assigned the free names just computed. The
node is part of a type that other values can reach.
R: that field.
F: those of the function called.
A: none
read: `middle_end/flambda2/types/grammar/with_cached_free_names.ml`:15-79.
note: this is a memo. The value stored is a function of the node alone (the
description of the node is immutable), so a later reader gets what it would have
computed itself.

### F: Typing_env_extension.With_extra_variables.apply_renaming
defined: `middle_end/flambda2/types/env/typing_env_extension.ml`:124-139
(reached only from `descr`, when the pending renaming is not the identity)
calls: `Renaming.apply_variable`, `Renaming.apply_name` (entry below);
`Type_grammar.apply_renaming` (entry below); `Name.Map.fold`, `Name.Map.add`.
W, R, F: those of the functions called.
A: none
read: `middle_end/flambda2/types/env/typing_env_extension.ml`:124-139.

### F: Type_grammar.apply_renaming
defined: `middle_end/flambda2/types/grammar/type_grammar.ml`:737-1211 (a group
of mutually recursive functions)
calls: `Type_descr.apply_renaming`
(`middle_end/flambda2/types/grammar/type_descr.ml`:216-228, 114-124), which
calls `With_cached_free_names.apply_renaming`
(`middle_end/flambda2/types/grammar/with_cached_free_names.ml`:39-54; it calls
`With_cached_free_names.free_names`, so it writes the cache too, then
`Name_occurrences.affected_by_renaming` and `apply_renaming`) and, for an alias,
`Simple.apply_renaming` (`middle_end/flambda2/term_basics/simple.ml`:133, which
is `Renaming.apply_simple`); the functions of `Renaming` (entry below);
`Rec_info_expr.apply_renaming`
(`middle_end/flambda2/term_basics/rec_info_expr.ml`:19-30);
`Set_of_closures_contents.apply_renaming`
(`middle_end/flambda2/types/grammar/set_of_closures_contents.ml`:64-72); the
sharing maps of `Misc.Stdlib` (`utils/misc.ml`:256-262, 446-455) and of
`Or_unknown` (`middle_end/flambda2/lattices/or_unknown.ml`:50-55); maps and
sets.
W: the caches of free names (above); through `Renaming.apply_simple`, the table
of simples and, with an import map, the tables of the other identifiers (below).
R: those caches and tables.
F: `middle_end/flambda2/types/grammar/type_grammar.ml`:1118-1119 (a fatal error,
when the renaming of the closures of a type gives an "other" case; not reachable
by this reading, because the "other" case passed at 1114 is always bottom and
1074-1076 returns it unchanged); those of `Renaming` (below).
A: none
read: `middle_end/flambda2/types/grammar/type_grammar.ml`:737-1211.

### F: functions of Renaming used on this path
defined: `middle_end/flambda2/nominal/renaming.ml`: `is_identity` 177-195;
`apply_variable` 260-269; `apply_symbol` 288-291; `apply_name` 300-303;
`apply_continuation` 315-324; `apply_code_id` 338-341; `apply_const` 353-356;
`apply_simple` 358-378; `value_slot_is_used` 380-383; the import map 23-130.
calls: `Permutation.apply` (`middle_end/flambda2/nominal/permutation.ml`:59-60,
a lookup in a Patricia tree). With an import map (a renaming made to read the
file of another compilation unit): the `import` functions of `Int_ids`
(`middle_end/flambda2/identifiers/int_ids.ml`: constants 465-466, variables
554-555, symbols 638-639, simples 839-859, code identifiers 960-961) and of
`Continuation` (`middle_end/flambda2/identifiers/continuation.ml`:174-175). In
`apply_simple`, without an import map: `Int_ids.Simple.pattern_match` (745-764),
`Coercion.map_depth_variables`
(`middle_end/flambda2/identifiers/coercion0.ml`:116-124;
`middle_end/flambda2/identifiers/rec_info_expr0.ml`:195-206) and
`Int_ids.Simple.with_coercion` (entry below).
W: through `with_coercion` and through the `import` functions: tables that
intern (below).
R: the same tables.
F: `middle_end/flambda2/identifiers/int_ids.ml`:822-825 (through
`with_coercion`); `middle_end/flambda2/algorithms/table_by_int_id.ml`:99, 126
(below).
A: none
read: `middle_end/flambda2/nominal/renaming.ml`:15-383;
`middle_end/flambda2/nominal/permutation.ml`:15-118;
`middle_end/flambda2/identifiers/coercion0.ml`:15-125;
`middle_end/flambda2/identifiers/rec_info_expr0.ml`:75-218;
`middle_end/flambda2/identifiers/continuation.ml`:100-130, 160-181.
note: none of these makes a fresh name. The functions of this file that do
(`bind_variable`, 271-279, and `bind_continuation`, 326-336) are not on this
path.

### F: Int_ids.Simple.with_coercion and the tables that intern
defined: `middle_end/flambda2/identifiers/int_ids.ml`:814-825; the table of
simples is the reference at 727. The table functions are
`middle_end/flambda2/algorithms/table_by_int_id.ml`: `add` 75-107, `find`
109-111, `import` 122-126.
calls: `Table_by_int_id.Make.add`, which calls the functions of `Hashtbl.Make`
(LEAF(stdlib)).
W: the table of simples (`middle_end/flambda2/identifiers/int_ids.ml`:727):
`add` puts a new entry when the pair (name, coercion) is not in the table yet.
With an import map, the same `add` on the table of constants (366), of variables
(474), of symbols (568), of code identifiers (867), of continuations
(`middle_end/flambda2/identifiers/continuation.ml`:103).
R: the same tables.
F: `middle_end/flambda2/identifiers/int_ids.ml`:822-825 (a `Simple` that already
has a coercion; not reachable from `Renaming.apply_simple` or from
`Int_ids.Simple.import` by this reading, because both pass a bare name);
`middle_end/flambda2/algorithms/table_by_int_id.ml`:99 (no identifier left); 126
(an identifier that the other unit did not export); 29-30 (bits of the kind out
of range; not reachable, the kinds are the constants of
`middle_end/flambda2/identifiers/int_ids.ml`:31-39 and of
`middle_end/flambda2/identifiers/continuation.ml`:19); assertions at 91, 103,
106, 110, 123.
A: none
read: `middle_end/flambda2/identifiers/int_ids.ml`:17-40, 361-470, 469-561,
563-640, 695-860, 862-962;
`middle_end/flambda2/algorithms/table_by_int_id.ml`:15-127.
note on how an identifier is chosen
(`middle_end/flambda2/algorithms/table_by_int_id.ml`:75-107): from the hash of
the data and the bits of the kind; if that identifier is taken by different
data, the next integers are tried in turn. So the identifier of a NEW entry can
depend on what the table holds already. `add` never changes or removes the entry
of an identifier that is in the table. No counter is read or advanced: the
counters of fresh names (`middle_end/flambda2/identifiers/int_ids.ml`:490 for
variables, 881 for code identifiers;
`middle_end/flambda2/identifiers/continuation.ml`:21-25;
`middle_end/flambda2/identifiers/slot.ml`:105;
`middle_end/flambda2/identifiers/named_rewrite_id.ml`:19) are not touched on
this path.

## PLACES

### P5: apply_prim
place: `middle_end/flambda2/simplify/flow/mutable_unboxing.ml` 450-452
fields and calls (type `Fold_prims.env`, 356-360, two immutable fields):
- `bindings`: `Simple.Map.add` of `block`, `fields`, `env.bindings`
- `rewrites`: `Named_rewrite_id.Map.add` of `rewrite_id`, `rewrite`,
  `env.rewrites`
The arguments are variables bound before the record (437-449) and projections of
immutable fields of `env`.
pairs:
- `Simple.Map.add` / `Named_rewrite_id.Map.add`: neither writes or reads any
  state; neither can fail; they work on two different maps. They commute.
verdict: COMMUTE

### P6: apply_prim
place: `middle_end/flambda2/simplify/flow/mutable_unboxing.ml` 463-465
fields and calls (same type):
- `bindings`: `Simple.Map.add` of (`Simple.var` of `var`), `fields`,
  `env.bindings`
- `rewrites`: `Named_rewrite_id.Map.add` of `rewrite_id`, `rewrite`,
  `env.rewrites`
pairs:
- `Simple.var` / anything: it returns its argument; no table, no effect, no
  failure.
- `Simple.Map.add` / `Named_rewrite_id.Map.add`: as at P5. They commute.
verdict: COMMUTE

### P7: create_block_like
place: `middle_end/flambda2/simplify/lifting/lifted_constant.ml` 180-185
fields and calls, in the order of the TYPE (139-145: `definitions`,
`bound_static`, `defining_exprs`, `symbol_projections`, `is_fully_static`; the
record at 180-185 writes the last two in the other order):
- `definitions`: no call
- `bound_static`: `compute_bound_static` of `definitions`
- `defining_exprs`: `compute_defining_exprs` of `definitions`
- `symbol_projections`: `Definition.symbol_projections` of `definition`
- `is_fully_static`: `Rebuilt_static_const.is_fully_static` of `defining_expr`
facts of this place, from the lines before the record (172-179):
- `definitions` is a list of one definition, made by `Definition.block_like`
  (106-109).
- The guard at 172-175 stops with a fatal error unless
  `Rebuilt_static_const.is_block` holds; that function answers false for
  `Code_not_rebuilt` and `Set_of_closures_not_rebuilt`
  (`middle_end/flambda2/simplify/rebuilt_static_const.ml`:42-46). So here the
  constant is `Normal` or `Block_not_rebuilt`, and its free names are a stored
  field.
pairs:
- `compute_bound_static` / the three others: it reads one flag of the command
  line and writes nothing; none of the others writes any state. They commute.
- `compute_defining_exprs` / the three others: its only effect is to allocate a
  fresh record with a mutable field (A). An allocation is not a write; no other
  call can reach that record. They commute.
- `is_fully_static` / `Definition.symbol_projections`: here both only read
  immutable data.
failures: none can be reached here.
- `middle_end/flambda2/bound_identifiers/bound_static.ml`:131-134 needs a symbol
  defined twice; here the list of patterns is one `Block_like` pattern, which
  defines one symbol, so the two numbers compared are both 1.
- `middle_end/flambda2/identifiers/int_ids.ml`:659 (the assertion in
  `Name.is_var`) needs a name whose bits say neither "variable" nor "symbol";
  see the entry `Name.is_var`.
verdict: COMMUTE

### P8: create_set_of_closures
place: `middle_end/flambda2/simplify/lifting/lifted_constant.ml` 198-203
fields and calls: as at P7 (same type, same four calls).
facts of this place (189-197):
- `definitions` is a list of one definition, made by
  `Definition.set_of_closures` (98-104).
- The guard at 189-192 stops unless `Rebuilt_static_const.is_set_of_closures`
  holds; that function answers false for `Code_not_rebuilt` and
  `Block_not_rebuilt`
  (`middle_end/flambda2/simplify/rebuilt_static_const.ml`:48-52). So here the
  constant is `Normal` or `Set_of_closures_not_rebuilt`, and its free names are
  a stored field.
pairs: as at P7. Every pair commutes: one read of a flag, one allocation, no
write.
failures:
- `compute_bound_static` can fail, at
  `middle_end/flambda2/bound_identifiers/bound_static.ml`:131-134, when the
  heavy invariant checks are on and `closure_symbols_with_types` gives the same
  symbol to two function slots. The reading of this function cannot exclude that
  (the map comes from the caller).
- No other call of the place can fail (for
  `middle_end/flambda2/identifiers/int_ids.ml`:659 see P7).
verdict: COMMUTE, FAILURES ORDERED: one call only can fail
(`compute_bound_static`, on the condition above). The order chooses nothing that
can be seen: the same failure is raised in any order, and the three other calls
write no state (one allocates).

### P9: create_code
place: `middle_end/flambda2/simplify/lifting/lifted_constant.ml` 212-217
fields and calls: as at P7 (same type, same four calls).
facts of this place (206-211):
- `definitions` is a list of one definition, made by `Definition.code` (96).
- The guard at 206-209 stops unless `Rebuilt_static_const.is_code` holds
  (`middle_end/flambda2/simplify/rebuilt_static_const.ml`:54-58). So here the
  constant is `Normal` (free names: a stored field) or `Code_not_rebuilt` (free
  names: COMPUTED, Part 3).
- For a definition of code, `Definition.symbol_projections` returns the empty
  map.
pairs:
- `is_fully_static` / `compute_bound_static`: for `Code_not_rebuilt`,
  `is_fully_static` writes the caches of free names in the result types of the
  code (`middle_end/flambda2/types/grammar/with_cached_free_names.ml`:32), may
  assign the three fields of the abstraction of the result types
  (`middle_end/flambda2/nominal/name_abstraction.ml`:71-73) and may add entries
  to tables that intern (the table of simples,
  `middle_end/flambda2/identifiers/int_ids.ml`:727; with an import map, the
  tables of the other identifiers). `compute_bound_static` reads one flag of the
  command line (`utils/clflags.ml`:313-315), which nothing in the middle end
  assigns. It reads the tables of identifiers only on its failure path, and that
  path cannot be reached here (one pattern, one code identifier; see P7). So
  neither writes what the other reads or writes. They commute.
- `is_fully_static` / `compute_defining_exprs`: the second puts the constant in
  a fresh group and does not look inside it; its cache (the mutable field of the
  group) is a different field from the caches that `is_fully_static` writes, and
  `is_fully_static` is not given the group. They commute.
- `is_fully_static` / `Definition.symbol_projections`: the second reads
  immutable data only.
- The other pairs: as at P7.
- Interning: one call only of the place can add an entry to a table. The rule
  about two calls that add to the same table does not apply.
- Fresh names: none (see the notes in Part 3).
failures:
- `is_fully_static` can fail, only for a `Code_not_rebuilt` constant: the three
  assertions on the counts of occurrences
  (`middle_end/flambda2/nominal/name_occurrences.ml`:106, 111, 115); and, only
  when the result types carry a pending renaming,
  `middle_end/flambda2/bound_identifiers/bound_parameter.ml`:65-68 and
  `middle_end/flambda2/algorithms/table_by_int_id.ml`:99, and with an import map
  `middle_end/flambda2/algorithms/table_by_int_id.ml`:126. (The sites
  `middle_end/flambda2/types/grammar/type_grammar.ml`:1118-1119,
  `middle_end/flambda2/identifiers/int_ids.ml`:822-825 and
  `middle_end/flambda2/algorithms/table_by_int_id.ml`:29-30 are on the path but
  not reachable by this reading; see Part 3.)
- `compute_bound_static` cannot fail here (one pattern that defines one code
  identifier).
- The two others cannot fail.
verdict: COMMUTE, FAILURES ORDERED: one call only can fail (`is_fully_static`,
for a `Code_not_rebuilt` constant). The order chooses nothing that can be seen:
the three other calls write no state (one allocates), so the state at the
failure is the same in any order.

### P10: create_definition
place: `middle_end/flambda2/simplify/lifting/lifted_constant.ml` 221-227
fields and calls: as at P7, but the argument of `is_fully_static` is the call
`Definition.defining_expr` of `definition` (line 225), a projection of an
immutable field.
facts of this place (219-220):
- `definitions` is a list of one definition, which is the argument of the
  function. There is no guard: the definition can be of any of the three sorts
  and its constant can be any of the four constructors.
pairs:
- `Definition.defining_expr` / anything: a projection; no effect, no failure.
- `is_fully_static` / `compute_bound_static`: as at P9, with one more case. Here
  the failure path of `compute_bound_static` can be reached (a definition of a
  set of closures, heavy checks on, a symbol given twice). On that path it
  prints the patterns, and for that it reads the tables of symbols and of code
  identifiers; `is_fully_static` may add entries to those tables (only for a
  `Code_not_rebuilt` constant whose result types carry a pending renaming with
  an import map). The entries read are those of identifiers that exist already,
  and `add` never changes the entry of an identifier that is in the table
  (`middle_end/flambda2/algorithms/table_by_int_id.ml`:75-107). So what the
  failure path prints does not depend on the order. They commute.
- `is_fully_static` / `compute_defining_exprs`, `is_fully_static` /
  `Definition.symbol_projections`, and the other pairs: as at P9.
- Interning: one call only of the place can add an entry to a table.
- Fresh names: none.
failures:
- `compute_bound_static`:
  `middle_end/flambda2/bound_identifiers/bound_static.ml`:131-134, when the
  heavy invariant checks are on and the definition is a set of closures that
  gives one symbol to two function slots.
- `is_fully_static`: as at P9, only for a `Code_not_rebuilt` constant.
- The two others, and `Definition.defining_expr`, cannot fail.
verdict: COMMUTE, FAILURES ORDERED: two calls can fail (`compute_bound_static`
and `is_fully_static`, each on the condition above; both conditions in one call
need a definition of a set of closures whose constant is `Code_not_rebuilt`,
which nothing in this function forbids). The order then chooses: (1) which of
the two failures is seen; with the order of the type, the last field first,
`is_fully_static` runs first and its failure is the one seen; (2) when only
`compute_bound_static` fails, whether the writes of `is_fully_static` (the
caches of free names, the fields of the abstraction, the possible table entries)
have happened before the failure.

## WHAT WAS NOT READ, AND DOUBTS

Not read, with what was assumed:

1. The standard library, except `stdlib/map.ml` 77-141 and the definitions of
   `Int.compare` and of the list functions named above. Assumed from the
   documentation: the functions of `List`, `ListLabels`, `Array`, `Map.Make`,
   `Set.Make`, `Hashtbl.Make` used here have no effect of their own beyond
   calling the function that they are given (and, for `Hashtbl`, changing the
   table that they are given).
2. The printers reached on the failure path of `Bound_static.create`:
   `Misc.Sexp`, `Function_slot.Lmap.print`, `Flambda_colours`, `Format`. They
   run only when the call is about to raise. Read: `Symbol.print` and
   `Code_id.print` (`middle_end/flambda2/identifiers/int_ids.ml`:610-615,
   929-931): they read the tables of symbols and of code identifiers.
3. On the path of a `Code_not_rebuilt` constant (P9, P10), these leaves were
   not read: `Flambda_kind.equal` and `Flambda_kind.With_subkind.kind` (called
   by `Bound_parameter.create`); the functions of sets of value slots and of
   maps of tags (`Set.Make` and `Map.Make` of the standard library, through
   `middle_end/flambda2/algorithms/container_types.ml`); the functions of
   `Hashtbl`. Assumed: comparisons and traversals of immutable data. The
   verdicts of P9 and P10 do not rest on these being pure. They rest on this:
   the three OTHER calls of the place (all read in full) read one flag that only
   the driver assigns, and otherwise touch no state.
4. `Static_const_or_code.is_block`, `is_set_of_closures`, `is_code` (called by
   the guards before the records, not in a field). Not needed: the exclusion of
   `Code_not_rebuilt` at P7 and P8 is in
   `middle_end/flambda2/simplify/rebuilt_static_const.ml`:42-52 itself.
5. The callers of the four `create` functions, and the code that builds the
   result types of a `Code_not_rebuilt` constant.

Doubts:

A. Not decided from these files: whether, at P9 or P10, the result types of a
   `Code_not_rebuilt` constant can carry a pending renaming, or a renaming with
   an import map. Both were treated as possible. If neither can happen,
   `is_fully_static` writes only the caches of free names, and the failures of
   P9 and P10 reduce to the three assertions on counts.
B. Not decided: whether `closure_symbols_with_types` (P8) or a definition given
   to `create_definition` (P10) can give one symbol to two function slots. It
   was treated as possible; it is the only way `compute_bound_static` fails, and
   only with the heavy checks.
C. The writes of `is_fully_static` for `Code_not_rebuilt` are memos and
   interning. They were judged by the rule of `README.md`, section 2 (no other
   call of the place reads or writes them). No attempt was made to show that a
   memo can never be observed by later code; the reading says that each memo
   stores what a later reader would compute (the description of a type node is
   immutable; the abstraction is replaced by its renamed form with an empty
   pending renaming).
D. `Misc.Fatal_error` is an exception. Handlers above these functions were not
   looked for. If a handler catches it and the compilation goes on, point (2) of
   the verdict of P10 is the only thing that the order could leave behind (memos
   filled or not, table entries added or not).
E. The `dune` files of these libraries allow an instrumentation for coverage
   (`bisect_ppx`). In such a build every function writes counters of coverage.
   Not counted.
F. The integers that represent variables depend on a random seed drawn once when
   the compiler starts (`middle_end/flambda2/identifiers/int_ids.ml`:17-19).
   This does not concern the order of the calls of a place (the keys are already
   integers when `Simple.Map.add` is called), but it means that the shape of a
   map of simples is not a function of the names alone.
G. P7 is given COMMUTE and not "FAILURES ORDERED" because the two failure sites
   in the code that it calls cannot be reached there, by the arguments written
   at the place. If a guarded site is counted as "can fail", P7 becomes
   "COMMUTE, FAILURES ORDERED" with nothing chosen by the order (no call of P7
   writes any state).
