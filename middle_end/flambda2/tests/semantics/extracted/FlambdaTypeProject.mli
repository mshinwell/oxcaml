open BinNums
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open List

val traverse : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option

val project_relation :
  variable list ->
  (variable -> flambda_type option) ->
  variable option ->
  variable option option

val project_inverse_relation :
  variable list ->
  (variable -> flambda_type option) ->
  Relation.t * name ->
  (Relation.t * name) list option

val project_head_of_kind_naked_immediate :
  variable list ->
  (variable -> flambda_type option) ->
  head_of_kind_naked_immediate ->
  head_of_kind_naked_immediate option

val project_descr :
  variable list ->
  (variable -> flambda_type option) ->
  ('a1 -> 'a1 option) ->
  (flambda_type -> 'a1 type_descr option) ->
  'a1 type_descr ->
  'a1 type_descr option

val value_of_expanded : flambda_type -> head_of_kind_value type_descr option

val naked_immediate_of_expanded :
  flambda_type -> head_of_kind_naked_immediate type_descr option

val naked_number_of_expanded :
  naked_number_kind -> flambda_type -> coq_Z list type_descr option

val rec_info_of_expanded : flambda_type -> unit type_descr option

val region_of_expanded : flambda_type -> unit type_descr option

val project_block_case :
  (flambda_type -> flambda_type option) ->
  (env_extension -> env_extension option) ->
  row_like_block_case ->
  row_like_block_case option

val project_variables_out :
  variable list ->
  (variable -> flambda_type option) ->
  flambda_type ->
  flambda_type option
