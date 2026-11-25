# Record order, part 3: places 11 to 16, 20 and 21

The reading of the compiler's code for places 11 to 16, 20 and 21. `README.md`
of this folder has the question, the sense and the table of places.

Commit read: `4fe46bb689903ead25d346ac9efd3c883821f171` (`git rev-parse HEAD` in
the tree that was read).

Method: a reading of the source only. Nothing was built and nothing was run. All
paths are from the root of the repository. No line of the compiler is copied.

Summary of the verdicts (the reasons are in the section PLACES):

| place | verdict |
|---|---|
| P11 | COMMUTE |
| P12 | COMMUTE, FAILURES ORDERED (one call only can fail) |
| P13 | COMMUTE, FAILURES ORDERED (one call only can fail; that call also writes caches) |
| P14 | COMMUTE, FAILURES ORDERED (as P13) |
| P15 | COMMUTE |
| P16 | COMMUTE, FAILURES ORDERED (one call only can fail) |
| P20 | COMMUTE |
| P21 | COMMUTE |

No place makes a fresh name. No place is REPORT.

Three facts that the reader should know before the entries:

1. `Code.free_names` is NOT a stored field. It is computed at each call (entry
   F6). On the way it WRITES memo cells (a cache of free names in each type that
   it visits, and the forcing of a delayed renaming). The other call of its
   places is a constructor application that reads nothing, so the places still
   commute.
2. The maps of free names are of two kinds. Names, code identifiers and
   continuations are integers, and their maps are Patricia trees that work on
   the integer: no comparison function is given and no table is consulted.
   Function slots and value slots are records, and their maps are the maps of
   OCaml's standard library with a comparison that was read (entry C3): it reads
   no table.
3. The counts of occurrences are packed in 20 bits each and are guarded by
   assertions. So a function of free names can stop with `Assert_failure` when
   one name occurs more than 1 048 575 times in one mode. That is why the places
   of free names are "FAILURES ORDERED" and not plain "COMMUTE".

How module names resolve in the two files of the places (each was checked):
`middle_end/flambda2/simplify/rebuilt_static_const.ml` opens `Flambda` (line 17)
and makes `SC` an abbreviation of `Static_const` (line 19).
`Static_const_or_code` is `Flambda.Static_const_or_code`
(`middle_end/flambda2/terms/flambda.ml:1291-1360`). `Set_of_closures` is
`Flambda.Set_of_closures`, an alias
(`middle_end/flambda2/terms/flambda.ml:1708`) of
`middle_end/flambda2/terms/set_of_closures.ml`. `Static_const`, `Code` and
`Code_metadata` are not defined at the top of `Flambda`, so they are the files
`middle_end/flambda2/terms/static_const.ml`, `middle_end/flambda2/terms/code.ml`
and `middle_end/flambda2/terms/code_metadata.ml`. In
`middle_end/flambda2/simplify/simplify_set_of_closures.ml` (which opens
`Simplify_import`, line 17) `Code_metadata` is the same file; `Cost_metrics`
defines no module `Code_metadata` that the local open of line 961 could put in
front of it.

## FUNCTIONS

### Part A: the functions called in the fields

### F1: create_mapping ..
heading: F1: create_mapping (local function of
Rebuilt_expr.Matching_for_unique_handler.Match_permutable_parameters.create)
defined: middle_end/flambda2/simplify/rebuilt_expr.ml:420-431 (inside `create`,
416-432; `HV` is `Hashtbl.Make` applied to `Variable`, line 390; the type of the
data, with one mutable field, is at 394-397)
calls: HV.create (B1); List.iter (E); Bound_parameters.to_list (B4); HV.replace
(B2); Bound_parameter.var and Bound_parameter.kind (B4)
W: none. The only assignments are to the table that this same call has just
made.
R: none
F: none
A: yes: a fresh hash table (mutable, with an identity), and for each parameter a
fresh record with a mutable field
read: middle_end/flambda2/simplify/rebuilt_expr.ml:342-432

### F2: Flambda.Static_const_or_code.create_static_const
defined: middle_end/flambda2/terms/flambda.ml:1331 (the type is at 103-106)
calls: LEAF: it applies one constructor to its argument and does not look inside
the argument
W: none
R: none
F: none
A: a fresh immutable block (not mutable; physical equality would tell two
results apart)
read: middle_end/flambda2/terms/flambda.ml:103-106, 1291-1360;
middle_end/flambda2/terms/flambda.mli:637-663

### F3: Flambda.Static_const_or_code.create_code
defined: middle_end/flambda2/terms/flambda.ml:1327
calls: LEAF: it applies one constructor to its argument and does not look inside
the argument
W: none
R: none
F: none
A: a fresh immutable block (not mutable)
read: as F2

### F4: Static_const.free_names
defined: middle_end/flambda2/terms/static_const.ml:511-546 (with the local
function for lists of numbers at 512-519, and free_names_of_fields at 505-509)
calls: Set_of_closures.free_names (F7); free_names_of_fields, which calls
List.fold_left (E), Name_occurrences.union (N3) and
Simple.With_debuginfo.free_names (B6); Or_variable.free_names (B5);
Name_occurrences.add_variable (N2); Name_occurrences.empty (N1);
Name_mode.normal (B10)
W: none
R: the table of the simples that carry a coercion
(middle_end/flambda2/identifiers/int_ids.ml:727), only for a field that is such
a simple (through B6, B7, B8)
F: (a) `Assert_failure` at middle_end/flambda2/nominal/name_occurrences.ml:106
(also 111 and 115 for the other modes) when a count of occurrences would pass
1 048 575: for example a block or an array with more than that number of fields
that are the same name. (b) The failures of Simple.pattern_match (B8), for a
field that is a simple with a coercion. (c) For a set of closures, the failures
of F7.
A: a fresh immutable record of maps (or the shared constant N1)
read: middle_end/flambda2/terms/static_const.ml:17-149, 500-548

### F5: Static_const.set_of_closures (SC.set_of_closures)
defined: middle_end/flambda2/terms/static_const.ml:58
calls: LEAF: it applies one constructor to its argument
W: none
R: none
F: none
A: a fresh immutable block
read: middle_end/flambda2/terms/static_const.ml:19-58

### F6: Code.free_names
defined: middle_end/flambda2/terms/code.ml:47, which is Code0.free_names,
middle_end/flambda2/terms/code0.ml:86-90. It is COMPUTED: the record of a piece
of code (middle_end/flambda2/terms/code0.ml:17-21) stores the free names of the
parameters and body only; this function unions them with the free names of the
metadata.
calls: Code_metadata.free_names (D1); Name_occurrences.union (N3)
W: yes, three kinds, all through D1 and only when the result types of the code
are known:
  (1) the cache of free names of each type that is visited: the mutable field at
      middle_end/flambda2/types/grammar/with_cached_free_names.ml:19, assigned
      at line 32, when the cache is empty (D6);
  (2) the three mutable fields of the name abstraction that holds the result
      types (middle_end/flambda2/nominal/name_abstraction.ml:49-51), assigned at
      71-73, when a delayed renaming is waiting (D3);
  (3) in that same case of a waiting renaming, entries may be added to tables
      that intern: the table of simples with a coercion
      (middle_end/flambda2/identifiers/int_ids.ml:727; D9 and B9), and, if the
      renaming carries an import map, the tables of variables
      (middle_end/flambda2/identifiers/int_ids.ml:474), symbols (568), constants
      (366), code identifiers (867) and continuations
      (middle_end/flambda2/identifiers/continuation.ml:103).
R: the same cells and tables
F: (a) `Assert_failure` on a count of occurrences, as F4(a) (also when counts
are added by the change of mode, D1). (b) In the case of a waiting renaming: the
fatal errors and assertions of D9, D10 and B9 (a parameter whose new variable
has another kind; an identifier absent from an import map; a simple that already
has a coercion; no identifier left in a table). (c) The failures of B8 for an
alias type whose simple has a coercion. (d) The failures of the comparison C3
for types of closures.
A: a fresh immutable record of maps
FRESH NAMES: none. Every function on the path was read for a call that makes a
variable, a symbol, a continuation, a code identifier or a stamp. The path uses
only the functions of `Renaming` that APPLY a renaming (D9). It does not use the
functions that BIND (`bind_variable`, `bind_continuation`,
middle_end/flambda2/nominal/renaming.ml:271-279 and 326-336), which are the ones
that make fresh names; and the name abstraction is read with its function
`descr` (middle_end/flambda2/nominal/name_abstraction.ml:63-74), not with
`pattern_match` (76-83), which is the one that renames the bound names freshly.
read: middle_end/flambda2/terms/code.ml:17-65;
middle_end/flambda2/terms/code0.ml:17-135; and all of Part D

### F7: Set_of_closures.free_names
defined: middle_end/flambda2/terms/set_of_closures.ml:89-100
calls: Value_slot.Map.fold (C2); Simple.free_names (B7);
Name_occurrences.add_value_slot_in_declaration (N2); Name_occurrences.union
(N3); Name_occurrences.empty (N1); Name_mode.normal (B10);
Function_declarations.free_names (B11)
W: none
R: the table of simples with a coercion
(middle_end/flambda2/identifiers/int_ids.ml:727), only for a value slot whose
simple has a coercion
F: (a) `Assert_failure` on a count of occurrences, as F4(a). (b) The failures of
B8. (c) The failures of the comparison of slots (C3), which is called when a
slot is added to a map or two maps of slots are united.
A: a fresh immutable record of maps
read: middle_end/flambda2/terms/set_of_closures.ml:17-134

### F8: Code_metadata.cost_metrics
defined: middle_end/flambda2/terms/code_metadata.ml:97, a field of the result of
the functor Code_metadata_accessors (58-120), applied at line 138 to a view
whose function `metadata` is the identity (132-136)
calls: LEAF: a field projection
W: none
R: none
F: none
A: none
read: middle_end/flambda2/terms/code_metadata.ml:17-138;
middle_end/flambda2/terms/code_metadata.mli:60-90

### F9: Code_metadata.function_slot_size
defined: middle_end/flambda2/terms/code_metadata.ml:115-119 (same functor and
same application as F8)
calls: Flambda_arity.num_params
(middle_end/flambda2/kinds/flambda_arity.ml:225), which is List.length (E) of a
list (the type is at middle_end/flambda2/kinds/flambda_arity.ml:114); two
integer comparisons
W: none
R: none
F: none
A: none (it returns the integer 2 or 3). It is a computation, not a projection:
it reads two fields of the metadata (whether the function is tupled, and the
arity of the parameters).
read: middle_end/flambda2/terms/code_metadata.ml:17-138;
middle_end/flambda2/kinds/flambda_arity.ml:114, 223-225

### F10: Code_metadata.dbg
defined: middle_end/flambda2/terms/code_metadata.ml:101 (same functor and same
application as F8)
calls: LEAF: a field projection
W: none
R: none
F: none
A: none
read: as F8

### Part B: what the functions of Part A call

### B1: HV.create (Hashtbl.Make(Variable).create)
defined: stdlib/hashtbl.ml:501 (in the functor Make, 494-506), which calls the
general create (85-92) with its optional argument GIVEN as false
calls: power_2_above (stdlib/hashtbl.ml:80-83); Array.make (E)
W: none
R: none. The default of the optional argument would read the flag `randomized`
(stdlib/hashtbl.ml:59); because the argument is given, the default is not
evaluated. The seed is then 0 and the random generator is not called.
F: none
A: a fresh table
read: stdlib/hashtbl.ml:22-92, 494-506

### B2: HV.replace
defined: stdlib/hashtbl.ml:455-462 (in MakeSeeded, 360-492); it uses key_index
(370-371), replace_bucket (447-453), resize (159-168), insert_all_buckets
(131-157), ongoing_traversal (44-46)
calls: the hash and the equality of the key, which here are Variable.hash and
Variable.equal (B3)
W: only the table that it is given (its size, its array of buckets, the cells of
the buckets). In F1 that table is the fresh one.
R: only that table
F: none
A: none
read: stdlib/hashtbl.ml:22-50, 125-168, 358-375, 444-506

### B3: Variable.hash, Variable.equal, Variable.compare
defined: by a chain. middle_end/flambda2/identifiers/variable.ml:17 includes
Int_ids.Variable. middle_end/flambda2/identifiers/int_ids.ml:513-518 and 533 set
them to the functions of `Id`. `Id`
(middle_end/flambda2/algorithms/table_by_int_id.ml:19-20) includes Numbers.Int.
utils/numbers.ml:17-25 and 27-30: the comparison is the integer comparison of
the standard library, the hash is the identity, the equality is the equality of
integers. utils/identifiable.ml:266-273: the functor passes them through
unchanged.
calls: LEAF: integer primitives
W: none
R: none. A variable IS an integer; these three functions work on the integer and
do not consult the table of variables
(middle_end/flambda2/identifiers/int_ids.ml:474).
F: none
A: none
read: middle_end/flambda2/identifiers/variable.ml:15-32;
middle_end/flambda2/identifiers/int_ids.ml:469-561;
middle_end/flambda2/algorithms/table_by_int_id.ml:15-36; utils/numbers.ml:17-36;
utils/identifiable.ml:255-273
note: the same chain gives the comparison, equality and hash of Name, Symbol,
Simple, Code_id (middle_end/flambda2/identifiers/int_ids.ml:661-666, 603-608,
784-789, 922-927) and of Continuation
(middle_end/flambda2/identifiers/continuation.ml:141-146, where the hash is the
generic hash of the standard library applied to the integer).

### B4: Bound_parameters.to_list, Bound_parameter.var, Bound_parameter.kind
defined: middle_end/flambda2/bound_identifiers/bound_parameters.ml:45 (the
identity: the type is a list, line 19);
middle_end/flambda2/bound_identifiers/bound_parameter.ml:71 and 79 (field
projections of the record at 19-23)
calls: LEAF
W: none
R: none
F: none
A: none
read: middle_end/flambda2/bound_identifiers/bound_parameters.ml:15-112;
middle_end/flambda2/bound_identifiers/bound_parameter.ml:15-101

### B5: Or_variable.free_names
defined: middle_end/flambda2/term_basics/or_variable.ml:33-36
calls: Name_occurrences.empty (N1); Name_occurrences.singleton_variable (N2);
Name_mode.normal (B10)
W: none
R: none
F: none (the count is 1, which passes the assertion)
A: a fresh immutable record, or the shared constant
read: middle_end/flambda2/term_basics/or_variable.ml:15-50

### B6: Simple.With_debuginfo.free_names
defined: middle_end/flambda2/term_basics/simple.ml:232; it drops the debug
information and calls B7
calls: Simple.free_names (B7)
W, R, F, A: as B7
read: middle_end/flambda2/term_basics/simple.ml:201-240

### B7: Simple.free_names
defined: middle_end/flambda2/term_basics/simple.ml:129, which is
free_names_with_mode (123-127) with the normal mode
calls: Simple.pattern_match (B8); Coercion.free_names (B12);
Name_occurrences.add_name (N2); Name_occurrences.empty (N1)
W: none
R: the table of simples with a coercion
(middle_end/flambda2/identifiers/int_ids.ml:727), only when the simple has a
coercion
F: the failures of B8, and no other: the count of a name here is at most 3 (one
for the name; at most one for each of the two expressions of the coercion,
because such an expression holds at most one variable,
middle_end/flambda2/identifiers/rec_info_expr0.ml:113-120), so the assertion on
counts holds
A: a fresh immutable record, or the shared constant
read: middle_end/flambda2/term_basics/simple.ml:15-240

### B8: Simple.pattern_match (and Name.pattern_match)
defined: middle_end/flambda2/identifiers/int_ids.ml:745-764 (Simple), 653-659
(Name). They decide by the flag bits of the integer. For a simple with a
coercion, they look its data up with find_data (731), which is the function
`find` of a table (middle_end/flambda2/algorithms/table_by_int_id.ml:109-111).
calls: Id.flags (middle_end/flambda2/algorithms/table_by_int_id.ml:33);
Table.find; the two functions that the caller gives
W: none
R: the table of simples with a coercion
(middle_end/flambda2/identifiers/int_ids.ml:727), only when the flag says "has a
coercion"
F: (a) `Assert_failure` at middle_end/flambda2/identifiers/int_ids.ml:763, 764
or 659, if the flag bits are not those of a variable, a symbol, a constant or a
simple with a coercion; the types are private and every constructor sets one of
these flags, so no way to reach it was found. (b) `Assert_failure` at
middle_end/flambda2/algorithms/table_by_int_id.ml:110 (wrong flag; same remark).
(c) `Not_found` from middle_end/flambda2/algorithms/table_by_int_id.ml:111, if
the simple has the flag but no entry in the table. An entry is added when the
simple is made (middle_end/flambda2/identifiers/int_ids.ml:820). The table is
replaced by an empty one by the function `initialise`
(middle_end/flambda2/identifiers/int_ids.ml:729, 1076-1083); so this needs a
simple that is older than the last such reset.
A: none of its own
read: middle_end/flambda2/identifiers/int_ids.ml:642-690, 695-860;
middle_end/flambda2/algorithms/table_by_int_id.ml:15-127

### B9: Simple.with_coercion and the tables that intern ..
heading: B9: Simple.with_coercion and the tables that intern
(Table_by_int_id.Make: add, find, import)
defined: middle_end/flambda2/identifiers/int_ids.ml:814-825;
middle_end/flambda2/algorithms/table_by_int_id.ml:75-107 (add), 109-111 (find),
122-126 (import). The import functions of the identifiers are
middle_end/flambda2/identifiers/int_ids.ml:465-466 (constants), 554-555
(variables), 638-639 (symbols), 839-859 (simples), 960-961 (code identifiers)
and middle_end/flambda2/identifiers/continuation.ml:174-175.
calls: the hash and the equality of the data (read: variables
middle_end/flambda2/identifiers/int_ids.ml:276-301, code identifiers 342-358,
simples 708-717, constants 199-252, continuations
middle_end/flambda2/identifiers/continuation.ml:74-96; NOT read: those of
symbols, which come from utils/symbol.ml:30-42); the functions of the hash table
of the standard library
W: `add` may add an entry to the table that it is given
R: that table
F: fatal error at middle_end/flambda2/algorithms/table_by_int_id.ml:99 (no free
identifier left); fatal error at middle_end/flambda2/identifiers/int_ids.ml:822
(the simple already has a coercion that is not the identity); fatal error at
middle_end/flambda2/algorithms/table_by_int_id.ml:126 (the identifier is absent
from the import map); assertions on the flag at 91, 103, 106, 110, 123
A: none
HOW AN IDENTIFIER IS CHOSEN for a new entry
(middle_end/flambda2/algorithms/table_by_int_id.ml:75-107): first from the data
alone (its hash, with the flag bits). If that identifier is taken by different
data, the next integers are tried until a free one is found. So, when two
different data have the same hash, the identifier of each DEPENDS ON WHICH WAS
ADDED FIRST. No counter is used. In the places of this part this is reached only
from F6 (case of a waiting renaming), and the other call of those places adds
nothing to any table.
read: middle_end/flambda2/algorithms/table_by_int_id.ml:15-127;
middle_end/flambda2/identifiers/int_ids.ml:17-40, 255-360, 361-467, 469-640,
695-962

### B10: Name_mode.normal (and in_types)
defined: middle_end/flambda2/nominal/name_mode.ml:44 and 46: constants
calls: LEAF: a constant
W: none
R: none
F: none
A: none
read: middle_end/flambda2/nominal/name_mode.ml:15-60

### B11: Function_declarations.free_names
defined: middle_end/flambda2/terms/function_declarations.ml:58-69
calls: Function_slot.Map.fold (C2);
Name_occurrences.add_function_slot_in_declaration and add_code_id (N2);
Name_occurrences.empty (N1); Name_mode.normal (B10)
W: none
R: none
F: the failures of the comparison of slots (C3), in the addition of a slot to a
map; `Assert_failure` on a count only if one code identifier is the code of more
than 1 048 575 function slots of the one set (each slot itself is a key of a
map, so it is added once)
A: a fresh immutable record of maps
read: middle_end/flambda2/terms/function_declarations.ml:15-128

### B12: Coercion.free_names and Rec_info_expr.free_names
defined: middle_end/flambda2/term_basics/coercion.ml:17-23;
middle_end/flambda2/term_basics/rec_info_expr.ml:32-40 (a recursion on the
expression; a variable gives a singleton)
calls: Name_occurrences.empty (N1), union (N3), singleton_variable (N2)
W: none
R: none
F: none (two singletons are united: the count is at most 2)
A: a fresh immutable record, or the shared constant
read: middle_end/flambda2/term_basics/coercion.ml:15-55;
middle_end/flambda2/term_basics/rec_info_expr.ml:15-45;
middle_end/flambda2/identifiers/coercion0.ml:15-125;
middle_end/flambda2/identifiers/rec_info_expr0.ml:15-218

### Part N: Name_occurrences

### N1: Name_occurrences.empty
defined: middle_end/flambda2/nominal/name_occurrences.ml:372-383: a constant
record of ten empty maps (the record type is at 356-370)
calls: LEAF: a constant
W: none
R: none
F: none
A: none (one shared value)
read: middle_end/flambda2/nominal/name_occurrences.ml:334-383

### N2: Name_occurrences.add_variable, add_name, add_code_id ..
heading: N2: Name_occurrences.add_variable, add_name, add_code_id,
add_newer_version_of_code_id, add_function_slot_in_declaration,
add_value_slot_in_declaration, add_function_slot_in_types,
add_value_slot_in_types, singleton_variable, create_variables
defined: middle_end/flambda2/nominal/name_occurrences.ml:420-421, 426-427,
473-474, 478-482, 441-445, 447-451, 453-461, 463-471, 417-418, 490-496. Each
copies the record with one map (two maps for the two "in_types" functions)
replaced by the result of the function `add` or `singleton` of one variety of
names (212-220), which calls the function `update` or `singleton` of the map
with the functions on one count (67-199: one_occurrence 142-146, add 148-158).
calls: the map functions of C1 (names and code identifiers) or C2 (slots);
Name.var, which is the identity (middle_end/flambda2/identifiers/int_ids.ml:645)
W: none
R: none
F: `Assert_failure` at middle_end/flambda2/nominal/name_occurrences.ml:106, 111
or 115 when the count for the mode would pass 1 048 575; for slots, the failures
of the comparison C3
A: a fresh immutable record
read: middle_end/flambda2/nominal/name_occurrences.ml:17-504
note (not one of the 23 places): add_function_slot_in_types and
add_value_slot_in_types (453-471) each build a record with a call in two fields.
The two calls are additions to two different immutable maps; they write nothing;
both can fail only by the assertion of line 111.

### N3: Name_occurrences.union (and union_list)
defined: middle_end/flambda2/nominal/name_occurrences.ml:734-744, with is_empty
(645-666: the earlier of the two definitions of that name) and binary_op
(582-643); union_list at 788. The union of one variety (224-228) calls the
function `union_total` of the map with the addition of two counts (183-189).
calls: the map functions is_empty and union_total of C1 and C2
W: none
R: none
F: `Assert_failure` at middle_end/flambda2/nominal/name_occurrences.ml:106, 111
or 115 when the sum of two counts for a mode passes 1 048 575; for slots, the
failures of C3
A: a fresh immutable record (or one of the two arguments, when the other is
empty)
read: middle_end/flambda2/nominal/name_occurrences.ml:17-313, 506-788

### N4: Name_occurrences.diff ..
heading: N4: Name_occurrences.diff,
downgrade_occurrences_at_strictly_greater_name_mode, apply_renaming,
affected_by_renaming
defined: middle_end/flambda2/nominal/name_occurrences.ml:668-732, 925-988,
1041-1093, 1095-1112; per variety at 222, 288-305, 323-331
calls: map functions of C1 and C2 (diff_domains, map_sharing, for_all, map_keys,
union); for the two renaming functions, Renaming.apply_name, apply_continuation,
apply_code_id and is_identity (D9)
W: none of their own; with a renaming that has an import map, the writes of D9
R: none of their own; the reads of D9
F: `Assert_failure` on a count (the change of mode adds two counts, lines
160-169); the failures of D9
A: a fresh immutable record
read: middle_end/flambda2/nominal/name_occurrences.ml:17-354, 668-732, 922-988,
1040-1112
used by: only the subtree of F6

### Part C: containers and comparisons

### C1: the Patricia tree maps and sets ..
heading: C1: the Patricia tree maps and sets (Name.Map, Code_id.Map,
Continuation.Map, Variable.Map, Variable.Set, Name.Set, and the maps of
relations in types)
defined: middle_end/flambda2/algorithms/patricia_tree.ml. The functor Make
(2229-2293) takes ONLY a printing function; keys are integers (line 17). Map is
at 2186-2223 and Set at 2104-2184, over Tree_operations (469-2101). Functions
used on the paths of this part: empty (2191), is_empty (643), singleton (646,
2193), add (684-707), update (737-776), remove (778-798), union_total
(1126-1137, over pattern_match_pair_merge 883-1050 and toplevel_union
1056-1067), find (1260-1277), find_or_null (1737-1740), diff_domains
(1356-1388), fold (1433-1446), for_all (1448-1462), map_sharing (1767-1785),
of_list (2067-2070), map_keys (2072-2074). Applied in
middle_end/flambda2/identifiers/int_ids.ml:541-546, 626-631, 684-689, 827-832,
942-947 and middle_end/flambda2/identifiers/continuation.ml:164-166.
calls: integer operations on the keys (15-95), one external primitive that
counts leading zeros (19-21), and the function that the caller gives
W: none (the only mutable things of the file are in the module Mutable_iterator,
1867-2046, which the paths of this part do not use)
R: none
F: none of their own. `find` raises `Not_found` for an absent key (1273); its
callers on the paths of this part catch it or use find_or_null. The assertion at
1047 is in a function given to the merge for the case "the result is empty"; in
union_total the three functions given always return a non-empty tree
(1129-1133), so it is not reached.
A: fresh immutable trees
read: middle_end/flambda2/algorithms/patricia_tree.ml:15-110, 110-300, 358-470,
600-1140, 1256-1280, 1354-1462, 1676-1702, 1735-1790, 2046-2293

### C2: the maps and sets of function slots and value slots ..
heading: C2: the maps and sets of function slots and value slots
(Function_slot.Map, Value_slot.Map and their Set), and of tags
defined: middle_end/flambda2/identifiers/function_slot.ml:17-23 and
middle_end/flambda2/identifiers/value_slot.ml:17-25 apply Slot.Make
(middle_end/flambda2/identifiers/slot.ml:43-131), which applies
Container_types.Make
(middle_end/flambda2/algorithms/container_types.ml:316-322). Make_map (33-266)
includes the functor Map.Make of the standard library applied to the comparison
C3, and adds union_total (39-40), diff_domains (77-88), map_sharing (235-245),
filter_map_sharing (247-261). The functions of the standard library, which were
read in the tree: stdlib/map.ml:77-551, with is_empty (127), add (129-141),
update (282-300), fold (329-333), map (311-318), filter_map (442-452), split
(391-400), join (364-372), merge (402-412), union (414-430), bal (95-123).
calls: the comparison C3 (in add, update, split and so in union and merge;
`fold`, `map` and `is_empty` do not compare); the function that the caller gives
W: none (the references in map_sharing and filter_map_sharing are local to one
call)
R: none
F: the failures of C3. `Invalid_argument` from stdlib/map.ml:100, 106, 112, 118
and 259, and the assertion at 412, only for a tree that is not balanced or is
empty where it must not be; no function of the module builds such a tree when
the comparison is a total order, and C3 is one.
A: fresh immutable trees
read: middle_end/flambda2/algorithms/container_types.ml:15-333;
stdlib/map.ml:16-150, 236-470; middle_end/flambda2/identifiers/slot.ml:15-131;
middle_end/flambda2/identifiers/function_slot.ml:15-30;
middle_end/flambda2/identifiers/value_slot.ml:15-36;
middle_end/flambda2/kinds/tag.ml:15-60

### C3: the comparison of slots, and Compilation_unit.compare
defined: middle_end/flambda2/identifiers/slot.ml:61-78: equal at once if the two
slots are physically the same; else by the difference of their stamps; else, for
equal stamps, by Compilation_unit.compare. utils/compilation_unit.ml:336-362
(compare; exported at 432 and 497): equal at once if physically the same; else
it takes both units apart with `descr` (284-301) and compares the names
(strings), the prefixes (lists of strings; the list comparison is
utils/misc.ml:128-136) and the arguments of instances, recursively.
calls: String.compare (E); the list comparison of Misc; `descr`, which for an
instance converts the head and the arguments with Name.of_string
(utils/compilation_unit.ml:89-92) and convert_arguments (278-282)
W: none
R: none. It reads no table, no flag, and not the current compilation unit: it
works on the two values only.
F: (a) `Assert_failure` at utils/compilation_unit.ml:286, if the value is
neither a string nor a block of tag 0 or 1; the two functions that build such
values (269-271) cannot make another. (b) The exception `Error` from
utils/compilation_unit.ml:91, if an instance has an empty head name or an empty
parameter name. No check was found that excludes the empty string when such a
name is made (the functions at typing/global_module.ml:157-167 store the head as
given; that file was not read further). Both need two DIFFERENT slots with the
SAME stamp whose compilation units are not physically the same.
A: none (it allocates small records that it drops)
read: middle_end/flambda2/identifiers/slot.ml:43-131;
utils/compilation_unit.ml:17-122, 124-200, 202-515; utils/misc.ml:120-142

### Part D: the subtree of Code.free_names

### D1: Code_metadata.free_names
defined: middle_end/flambda2/terms/code_metadata.ml:407-450
calls: Name_occurrences.empty (N1), add_newer_version_of_code_id (N2), union
(N3), downgrade_occurrences_at_strictly_greater_name_mode (N4);
Result_types.free_names (D2) when the result types are known; Name_mode.normal
and in_types (B10)
W: those of D2
R: those of D2
F: those of D2; `Assert_failure` on a count (N3, N4)
A: a fresh immutable record
read: middle_end/flambda2/terms/code_metadata.ml:17-256, 405-452

### D2: Result_types.free_names
defined: middle_end/flambda2/terms/result_types.ml:152-156; it calls
Name_abstraction.free_names (D3) with the module Bound (18-126) and the
functions of the environment extension with extra variables (D4)
calls: D3; Result_types.Bound.free_names (25-34) and Bound.apply_renaming
(36-46), which call Bound_parameters.free_names and apply_renaming (D10) and
Renaming.apply_variable (D9); D4
W: those of D3 and D4
R: those of D3 and D4
F: those of D3, D4, D9, D10
A: a fresh immutable record
read: middle_end/flambda2/terms/result_types.ml:15-168

### D3: Name_abstraction.free_names and With_delayed_renaming.descr
defined: middle_end/flambda2/nominal/name_abstraction.ml:122-127 and 63-74. The
abstraction is a record of three MUTABLE fields (48-52): the bound names, the
term, and a renaming that is waiting to be applied.
calls: Renaming.is_identity (D9); if the waiting renaming is not the identity:
the apply_renaming of the bound names and of the term (D2, D4); then the free
names of the term and of the bound names, and Name_occurrences.diff (N4)
W: if the waiting renaming is not the identity, `descr` applies it and ASSIGNS
the three fields (lines 71-73): the renamed bound names, the renamed term, and
the empty renaming. This is a memo: a later call finds the identity and assigns
nothing. The value outlives the call (it is inside the metadata of the code).
R: those three fields
F: those of the renaming functions (D4, D9, D10)
A: none of its own
FRESH NAMES: none. `descr` applies the waiting renaming; it does not open the
abstraction with fresh names. The function that does that is `pattern_match`
(76-83), which this path does not call.
read: middle_end/flambda2/nominal/name_abstraction.ml:15-168

### D4: Typing_env_extension.With_extra_variables.free_names and apply_renaming
defined: middle_end/flambda2/types/env/typing_env_extension.ml:111-122 and
124-139 (the type is at 76-79: a list of variables and a map from names to
types)
calls: Variable.Set.of_list and Name.Map.fold and add (C1);
Name_occurrences.create_variables and add_name (N2), union (N3);
Type_grammar.free_names (D5); Renaming.apply_variable and apply_name (D9);
Type_grammar.apply_renaming (D7); List.map (E)
W: those of D5 and D7
R: those of D5 and D7
F: those of D5, D7, D9; `Assert_failure` on a count
A: fresh immutable values; and, through D7, for a type that the renaming
changes, fresh records with a mutable cell for the cache of free names, and
fresh arrays. No fresh name.
read: middle_end/flambda2/types/env/typing_env_extension.ml:15-157

### D5: Type_grammar.free_names ..
heading: D5: Type_grammar.free_names (free_names0 and the functions free_names_*
that it calls)
defined: middle_end/flambda2/types/grammar/type_grammar.ml:439-724, entry at 729
(it follows value slots, so it uses the cached function of D6). The types are at
148-337.
calls: Type_descr.free_names (D6); Name_occurrences.empty, singleton_variable,
add_name, add_code_id, add_function_slot_in_types, add_value_slot_in_types (N1,
N2), union and union_list (N3); Rec_info_expr.free_names_in_types (B12);
Set_of_closures_contents.free_names
(middle_end/flambda2/types/grammar/set_of_closures_contents.ml:74-78);
Or_unknown.free_names (middle_end/flambda2/lattices/or_unknown.ml:57-60); the
`fold` of the maps of tags, function slots, value slots (C2), names and
relations (C1), and of the set of names (C1); Array.fold_left (E);
inverse_relations (middle_end/flambda2/types/grammar/type_grammar.ml:422-427)
W: the cache of D6, once for each type head that it visits and that has an empty
cache
R: that cache; the table of simples with a coercion (through B7, for an alias
type)
F: `Assert_failure` on a count; the failures of B8 and C3
A: fresh immutable records
read: middle_end/flambda2/types/grammar/type_grammar.ml:30-345, 400-737

### D6: Type_descr.free_names and With_cached_free_names.free_names
defined: middle_end/flambda2/types/grammar/type_descr.ml:230-236 and 126-131;
middle_end/flambda2/types/grammar/with_cached_free_names.ml:26-33. A type head
that is not an alias is held in a record with one MUTABLE field, the cache of
its free names
(middle_end/flambda2/types/grammar/with_cached_free_names.ml:17-20).
calls: the function of free names of the head, which the caller gives (D5); for
an alias, Simple.free_names (B7) and the change of mode (N4)
W: if the cache is empty, it computes the free names and ASSIGNS the cache
(middle_end/flambda2/types/grammar/with_cached_free_names.ml:32). This is a
memo. The value stored is computed from the head alone (D5 reads no flag and no
counter), so it does not depend on when it is stored.
R: the cache
F: those of the function given; those of B8
A: none of its own
read: middle_end/flambda2/types/grammar/type_descr.ml:15-311;
middle_end/flambda2/types/grammar/with_cached_free_names.ml:15-79

### D7: Type_grammar.apply_renaming ..
heading: D7: Type_grammar.apply_renaming (and the functions apply_renaming_*
that it calls)
defined: middle_end/flambda2/types/grammar/type_grammar.ml:737-1211. Reached
from F6 only when a renaming is waiting (D3).
calls: Renaming.is_identity, apply_variable, apply_name, apply_code_id,
value_slot_is_used (D9); Type_descr.apply_renaming and
With_cached_free_names.apply_renaming (D8); Rec_info_expr.apply_renaming
(middle_end/flambda2/term_basics/rec_info_expr.ml:19-30);
Set_of_closures_contents.apply_renaming
(middle_end/flambda2/types/grammar/set_of_closures_contents.ml:64-72); map
functions of C1 and C2; Misc.Stdlib.Array.map_sharing (utils/misc.ml:446-455);
Or_unknown.map_sharing (middle_end/flambda2/lattices/or_unknown.ml:50-55)
W: the caches of D6 (through D8); the tables of D9. The references named
`changed` (976-989, 1188-1199) are local to one call.
R: the same
F: fatal error at middle_end/flambda2/types/grammar/type_grammar.ml:1119, for a
case that its own call excludes (it passes "no other case" and so gets "no other
case" back); the failures of D8 and D9
A: the argument itself when nothing changes; else fresh values: immutable ones;
through D8 a fresh record with a mutable cell for the cache of free names,
already filled; fresh arrays (954-974, 1175-1178). No fresh name.
read: middle_end/flambda2/types/grammar/type_grammar.ml:400-437, 737-1212

### D8: Type_descr.apply_renaming and With_cached_free_names.apply_renaming
defined: middle_end/flambda2/types/grammar/type_descr.ml:216-228 and 114-124;
middle_end/flambda2/types/grammar/with_cached_free_names.ml:39-54
calls: D6 (it first takes the free names of the head, which fills the cache);
Renaming.has_import_map (D9); Name_occurrences.affected_by_renaming and
apply_renaming (N4); for an alias, Simple.apply_renaming, which is
Renaming.apply_simple (D9)
W: the cache of the OLD head (through D6); the tables of D9
R: the same
F: those of D6, D9, N4
A: a fresh record with its cache already filled, or the argument itself when the
renaming does not touch its free names
read: as D6

### D9: Renaming: is_identity, has_import_map, apply_variable, apply_symbol ..
heading: D9: Renaming: is_identity, has_import_map, apply_variable,
apply_symbol, apply_name, apply_continuation, apply_code_id, apply_const,
apply_simple, value_slot_is_used; Permutation.apply and is_empty
defined: middle_end/flambda2/nominal/renaming.ml:177-195, 161, 260-269, 288-291,
300-303, 315-324, 338-341, 353-356, 358-378, 380-383; the import map at 23-130;
middle_end/flambda2/nominal/permutation.ml:37 and 59-60
calls: map functions of C1; B8; Coercion.map_depth_variables
(middle_end/flambda2/identifiers/coercion0.ml:116-124) and the same of
Rec_info_expr (middle_end/flambda2/identifiers/rec_info_expr0.ml:195-206);
Simple.with_coercion (B9); with an import map, the import functions of B9;
Value_slot.in_compilation_unit
(middle_end/flambda2/identifiers/slot.ml:117-118), which calls the equality of
compilation units (C3)
W: apply_simple may add a simple with a coercion to the table of simples
(middle_end/flambda2/identifiers/int_ids.ml:727, through
middle_end/flambda2/identifiers/int_ids.ml:820), when the name or the coercion
changes. With an import map, each apply function may add the imported identifier
to its table (B9).
R: the table of simples; with an import map, the tables of B9
F: the fatal errors and assertions of B9; `Assert_failure` at
middle_end/flambda2/identifiers/int_ids.ml:659
A: none of their own
FRESH NAMES: none in these functions. An import copies the data of an identifier
of another unit into a table under the identifier that its data gives; it takes
nothing from a counter. The functions of this file that DO make fresh names are
bind_variable (271-279) and bind_continuation (326-336), and the two "fresh"
functions of the import map (105, 115-116); none is called by any function of
this part.
read: middle_end/flambda2/nominal/renaming.ml:15-383;
middle_end/flambda2/nominal/permutation.ml:15-118

### D10: Bound_parameters.free_names and apply_renaming ..
heading: D10: Bound_parameters.free_names and apply_renaming;
Bound_parameter.free_names, apply_renaming and create
defined: middle_end/flambda2/bound_identifiers/bound_parameters.ml:74-77 and
79-80; middle_end/flambda2/bound_identifiers/bound_parameter.ml:89-90, 92-94 and
58-69
calls: Name_occurrences.singleton_variable, union, empty;
Renaming.apply_variable (D9); Misc.Stdlib.List.map_sharing
(utils/misc.ml:256-262); in `create`: Variable.kind
(middle_end/flambda2/identifiers/int_ids.ml:486), which looks the variable up in
the table of variables, and the equality of kinds (not read)
W: none of their own
R: `create` reads the table of variables
(middle_end/flambda2/identifiers/int_ids.ml:474), only when a renaming changes
the variable of a parameter
F: fatal error at middle_end/flambda2/bound_identifiers/bound_parameter.ml:65 if
the new variable has not the kind of the parameter; `Not_found` or
`Assert_failure` from the table lookup
(middle_end/flambda2/algorithms/table_by_int_id.ml:110-111)
A: fresh immutable values
read: as B4

### Part E: leaves of the standard library whose bodies were not read

For each of these W, R, F, A are stated from the documented behaviour: none,
none, none (but for what the function given does), none.
- List.iter, List.fold_left, List.length, List.map (stdlib/list.ml)
- Array.fold_left, Array.map, Array.make (stdlib/array.ml); Array.make returns a
  fresh array
- Int.compare, String.compare
- Hashtbl.hash (the generic hash; used by the hash of continuations and of the
  data of tables, not by any comparison of the places of this part)
- the functions of Set.Make of the standard library (fold, filter, mem, add),
  used for the sets of function slots and value slots in
  Set_of_closures_contents (D5, D7)

The functions of the standard library whose bodies WERE read are in B1, B2
(stdlib/hashtbl.ml) and C2 (stdlib/map.ml).

## PLACES

### P11: create (Match_permutable_parameters)
place: `middle_end/flambda2/simplify/rebuilt_expr.ml` 432
fields and calls: params1: create_mapping (F1) on the first list of parameters;
params2: create_mapping (F1) on the second list (order of the type:
middle_end/flambda2/simplify/rebuilt_expr.ml:399-406)
pairs: (create_mapping, create_mapping): commute. Each call makes its own table
and assigns only to it; neither reads anything that the other writes. The keys
are variables, whose hash and equality are integer operations that consult no
table (B3). The creation of the table does not read the flag of randomisation
(B1). The effect of each call is only the allocation of fresh mutable things,
and two allocations commute.
verdict: COMMUTE

### P12: create_normal_non_code
place: `middle_end/flambda2/simplify/rebuilt_static_const.ml` 70-71
fields and calls: const: Static_const_or_code.create_static_const (F2);
free_names: Static_const.free_names (F4); cost_metrics: no call (a variable).
Order of the type: middle_end/flambda2/simplify/rebuilt_static_const.ml:25-29.
pairs: (F2, F4): commute. F2 writes nothing, reads nothing (it does not look
inside the constant) and cannot fail. F4 writes nothing.
verdict: COMMUTE, FAILURES ORDERED: only Static_const.free_names can fail: by
the assertion on a count of occurrences
(middle_end/flambda2/nominal/name_occurrences.ml:106, 111, 115); by the lookup
of a simple with a coercion (B8); and, for a set of closures, by the comparison
of slots (C3). The other call cannot fail, so the order does not choose WHICH
failure is seen. It chooses only whether the block of F2 was allocated before
the failure, and nothing can see that.

### P13: create_code
place: `middle_end/flambda2/simplify/rebuilt_static_const.ml` 94-95
fields and calls: const: Static_const_or_code.create_code (F3); free_names:
Code.free_names (F6); cost_metrics: no call (the constant at
middle_end/flambda2/terms/cost_metrics.ml:32). The code is bound by a `let`
before the record (lines 89-92).
pairs: (F3, F6): commute. F6 WRITES (caches of free names in the types of the
result types; the forcing of a delayed renaming; possibly entries of tables that
intern), but F3 reads none of that state and writes nothing: it only puts the
code under a constructor. In both orders the block of F3 points to the same
code, whose inner cells are filled once by F6.
verdict: COMMUTE, FAILURES ORDERED: only Code.free_names can fail (F6, F). The
other call cannot fail, so the order does not choose which failure is seen, and
the writes of F6 before its failure are the same in both orders. No fresh name
is made (F6, FRESH NAMES).

### P14: create_code'
place: `middle_end/flambda2/simplify/rebuilt_static_const.ml` 102-103
fields and calls: const: Static_const_or_code.create_code (F3); free_names:
Code.free_names (F6); cost_metrics: no call (a constant)
pairs: (F3, F6): commute, for the reason of P13
verdict: COMMUTE, FAILURES ORDERED: as P13. Here the code comes from the caller,
so it cannot be said from this function whether a renaming is waiting in its
result types; the verdict does not depend on it.

### P15: find_code_characteristics
place: `middle_end/flambda2/simplify/rebuilt_static_const.ml` 110-111
fields and calls: cost_metrics: Code_metadata.cost_metrics (F8);
function_slot_size: Code_metadata.function_slot_size (F9). Order of the type:
middle_end/flambda2/terms/cost_metrics.ml:27-30. The metadata is bound by a
`let` before the record (line 109).
pairs: (F8, F9): commute. F8 is a field projection. F9 reads two other fields of
the same immutable record and takes the length of a list. Neither writes,
neither reads any state, neither can fail.
verdict: COMMUTE

### P16: map_set_of_closures
place: `middle_end/flambda2/simplify/rebuilt_static_const.ml` 341-344
fields and calls: const: Static_const_or_code.create_static_const (F2) applied
to SC.set_of_closures (F5) of the set of closures; free_names:
Set_of_closures.free_names (F7); cost_metrics: no call (a variable). The set of
closures and the cost metrics are bound by `let` before the record (lines
333-339).
pairs: (F5, F7) and (F2, F7): commute. F5 and F2 each apply one constructor:
they write nothing, read nothing and cannot fail. F7 writes nothing.
verdict: COMMUTE, FAILURES ORDERED: only Set_of_closures.free_names can fail
(F7, F: the assertion on a count; the lookup of a simple with a coercion; the
comparison of slots). The other calls cannot fail, so the order does not choose
which failure is seen; it chooses only whether two blocks were allocated before
the failure.

### P20: simplify_non_lifted_set_of_closures0
place: `middle_end/flambda2/simplify/simplify_set_of_closures.ml` 935-939
fields and calls: function_slot_size: Code_metadata.function_slot_size (F9);
dbg: Code_metadata.dbg (F10). Order of the type:
middle_end/flambda2/terms/function_declarations.ml:18-21. The metadata is bound
by a `let` before the record (lines 928-934).
pairs: (F9, F10): commute. A computation on two fields of an immutable record,
and a projection of a third field. Neither writes, neither reads any state,
neither can fail.
verdict: COMMUTE

### P21: simplify_non_lifted_set_of_closures0
place: `middle_end/flambda2/simplify/simplify_set_of_closures.ml` 961-964
fields and calls: cost_metrics: Code_metadata.cost_metrics (F8);
function_slot_size: Code_metadata.function_slot_size (F9). Order of the type:
middle_end/flambda2/terms/cost_metrics.ml:27-30. The metadata is bound by a
`let` before the record (lines 955-960).
pairs: (F8, F9): commute, for the reason of P15
verdict: COMMUTE

## WHAT WAS NOT READ, AND DOUBTS

1. Whether assertions are compiled in. Every "FAILURES ORDERED" above rests in
   part on assertions. The build files of the tree (dune files, Makefiles,
   `.sexp`, `.mk`, `.ac`, `.in`, outside `external/` and the test suite) were
   searched for the flag that removes assertions, and none was found. The file
   `ocamlopt_flags.sexp` of the root of the project, which the dune files
   include, is made at build time and is not in the tree: it was not read.
   (`oxcaml/tests/backend/oxcaml_dwarf/ocamlopt_flags.sexp`, which is in the
   tree, is another file.) If assertions were removed, the
   counts of occurrences would wrap silently instead of failing; the verdicts
   would not get worse (the functions would then not fail at those lines).
2. `typing/global_module.ml`: read only lines 150-170 (the functions that make a
   name). `utils/symbol.ml`: not read (the hash and equality of the data of
   symbols, reached only with an import map, B9). Not established: whether an
   instance of a compilation unit can have an empty head name or an empty
   parameter name. That is the condition of failure (b) of C3. It matters only
   for which failures are possible, in P12 and P16 (and inside F6).
3. In the subtree of Code.free_names, the path of a WAITING RENAMING (D3, D7,
   D8, D9, D10, B9) is reached only if the result types of the code carry a
   renaming that is not the identity. Whether that can be the case at P13 and
   P14 depends on the callers, which were not read. The writes and failures of
   that path are reported as possible. The verdicts of P13 and P14 do not depend
   on it, because the other call of those places is a constructor application.
4. Not read in that same path: the equality of kinds and the projection of a
   kind with subkind (`middle_end/flambda2/kinds/`), called by
   Bound_parameter.create (D10); the comparison of integers used for tags and
   relations (`Numeric_types.Int`), which the map functions on the paths of this
   part do not call (they only fold and map).
5. The bodies of the standard-library functions of Part E were not read; and of
   `stdlib/map.ml` lines 16-150 and 236-470 were read (the first of the two
   copies of the functor), not the rest. The external primitive that counts
   leading zeros (middle_end/flambda2/algorithms/patricia_tree.ml:19-21) is a C
   stub or a built-in: not read.
6. Orders that OCaml does not fix INSIDE the callees. These are not among the 23
   places, and they were not surveyed completely. Three kinds were seen: (a) an
   application whose two arguments are both calls, for example the unions of two
   free-names calls in middle_end/flambda2/types/grammar/type_grammar.ml:615-629
   and 665-669 and in middle_end/flambda2/term_basics/coercion.ml:21-23; (b) the
   `let ... and ...` in the union of the standard library (stdlib/map.ml:421 and
   427); (c) the record with two calls in N2
   (middle_end/flambda2/nominal/name_occurrences.ml:453-471). In the free-names
   functions the calls involved write nothing but memo cells (each cell gets a
   value that depends on the type alone), so the value returned and the final
   state do not depend on these orders; what they can choose is which of several
   assertion failures is seen. In the path of a waiting renaming (item 3) the
   calls that can add to a table are bound by successive `let`s in every
   function that was read (D3, D4, D7), so their order is fixed by the source.
7. The remark of B9 on how an identifier is chosen in a table that interns (it
   can depend on what the table already holds, when two data have the same hash)
   is true of the code. It does not touch any of the eight places of this part,
   because in none of them can two calls of different fields both add to a
   table. It may matter for other places of the list where two calls can both
   intern.
8. Nothing was assumed from names or types. Where an entry says "LEAF: a field
   projection" or "a constructor application", the body was read. The interface
   files were not checked beyond the ones cited, since an interface cannot
   change a body.
