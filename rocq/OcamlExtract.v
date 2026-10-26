(* Extraction directives mapping the models in this directory onto OCaml's
   own types and functions, for every extraction in the repository to
   [Require]. Nothing here is proved: each line says which OCaml value
   realizes a model definition, and is trusted by inspection.

   - Rocq's primitive [int] (Sint63) is OCaml's [int] and its operations are
     OCaml's. This restates Rocq's own ExtrOCamlInt63 so that the output
     does not depend on Rocq's runtime library.
   - The [Int64] model is OCaml's [Int64]; the axioms in OcamlInt64.v are
     the documented behaviour of each operation named here.
   - The list functions are OCaml's [List] functions; [sort_uniq] is
     [List.sort_uniq Int.compare]. [map_opt] and [filter_map_opt] have no
     OCaml counterpart and are extracted as they are. *)

From Stdlib Require Import Extraction List.
From Stdlib Require Uint63 Sint63.
From OxcamlStdlib Require Import OcamlInt OcamlInt64 OcamlList.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "" ].
Extract Inlined Constant negb => "not".
Extract Inlined Constant andb => "( && )".
Extract Inlined Constant orb => "( || )".

(* OCaml [int]. *)
Extract Constant Uint63.int => "int".
Extraction Inline Uint63.int.
Extract Inlined Constant Uint63.eqb => "Int.equal".
Extract Inlined Constant Sint63.ltb => "( < )".
Extract Inlined Constant Sint63.leb => "( <= )".
Extract Inlined Constant Uint63.add => "( + )".
Extract Inlined Constant Uint63.sub => "( - )".
Extract Inlined Constant Uint63.mul => "( * )".
Extract Inlined Constant Uint63.opp => "Int.neg".
Extract Inlined Constant Uint63.lsl => "( lsl )".
Extract Inlined Constant Sint63.min_int => "Int.min_int".
Extract Inlined Constant Sint63.max_int => "Int.max_int".
Extract Inlined Constant zero => "0".
Extract Inlined Constant one => "1".
Extract Inlined Constant minus_one => "(-1)".
Extract Inlined Constant two => "2".

(* OCaml [Int64]. *)
Extract Constant int64 => "int64".
Extraction Inline int64.
Extract Inlined Constant int64_zero => "0L".
Extract Inlined Constant int64_one => "1L".
Extract Inlined Constant int64_minus_one => "(-1L)".
Extract Inlined Constant int64_min_int => "Int64.min_int".
Extract Inlined Constant int64_max_int => "Int64.max_int".
Extract Inlined Constant int64_of_int => "Int64.of_int".
Extract Inlined Constant int64_to_int => "Int64.to_int".
Extract Inlined Constant int64_add => "Int64.add".
Extract Inlined Constant int64_sub => "Int64.sub".
Extract Inlined Constant int64_mul => "Int64.mul".
Extract Inlined Constant int64_div => "Int64.div".
Extract Inlined Constant int64_rem => "Int64.rem".
Extract Inlined Constant int64_abs => "Int64.abs".
Extract Inlined Constant int64_neg => "Int64.neg".
Extract Inlined Constant int64_shift_right => "Int64.shift_right".
Extract Inlined Constant int64_shift_right_logical =>
  "Int64.shift_right_logical".
Extract Inlined Constant int64_equal => "Int64.equal".
Extract Inlined Constant int64_compare => "Int64.compare".

(* OCaml [List]. *)
Extract Inlined Constant map => "List.map".
Extract Inlined Constant filter => "List.filter".
Extract Inlined Constant filter_map => "List.filter_map".
Extract Inlined Constant concat_map => "List.concat_map".
Extract Inlined Constant rev_append => "List.rev_append".
Extract Inlined Constant forallb => "List.for_all".
Extract Inlined Constant existsb => "List.exists".
Extract Inlined Constant find => "List.find_opt".
Extract Inlined Constant app => "( @ )".
Extract Inlined Constant fst => "fst".
Extract Inlined Constant assoc_opt => "List.assoc_opt".
Extract Inlined Constant compare_length_with => "List.compare_length_with".
Extract Inlined Constant OcamlList.fold_left => "List.fold_left".
Extract Constant sort_uniq => "List.sort_uniq Int.compare".
