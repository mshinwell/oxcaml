open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open List

type known_sets =
  (variable * (function_slot * (function_slot * code_id) list)) list

val forget_set : variable -> known_sets -> known_sets

val forget_sets : variable list -> known_sets -> known_sets

val sets_under_let : known_sets -> variable -> named -> known_sets

val projection_defined : known_sets -> named -> bool

val remove_projections_knowing : known_sets -> expr -> expr

val remove_unused_projections : expr -> expr
