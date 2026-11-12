open BinNums
open Datatypes
open FlambdaCompareSpec
open FlambdaFreshQuantifierSpec
open FlambdaModel
open FlambdaNominalSpec
open List
open ListDef
open Nat

val variables_in_simple : simple -> variable list

val variables_in_simples : simple list -> variable list

val variables_in_slots : (value_slot * simple) list -> variable list

val variables_in_named : named -> variable list

val variables_in_static_const : static_const -> variable list

val variables_in_apply_cont : apply_cont -> variable list

val variables_in_apply : apply_expr -> variable list

val variables_of : expr -> variable list

val variables_in_handler : continuation_handler -> variable list

val variables_in_binding : static_binding -> variable list

val variables_in_code : code -> variable list

val continuations_in_apply : apply_expr -> continuation list

val continuations_of : expr -> continuation list

val continuations_in_handler : continuation_handler -> continuation list

val continuations_in_binding : static_binding -> continuation list

val continuations_in_code : code -> continuation list

val names_of : expr -> positive list

val binders : expr -> nat

val binders_in_handler : continuation_handler -> nat

val binders_in_binding : static_binding -> nat

val binders_in_code : code -> nat

val bind_variable : renaming -> variable -> variable -> renaming

val bind_continuation : renaming -> continuation -> continuation -> renaming

val new_variable : renaming -> positive list -> variable -> variable

val new_continuation : renaming -> positive list -> continuation -> continuation

val bind_variables :
  renaming ->
  positive list ->
  variable list ->
  (positive list * variable list) * renaming

val bind_continuations :
  renaming ->
  positive list ->
  continuation list ->
  (positive list * continuation list) * renaming

val thread :
  (positive list -> 'a1 -> positive list * 'a2) ->
  positive list ->
  'a1 list ->
  positive list * 'a2 list

val apart : renaming -> positive list -> expr -> positive list * expr

val apart_handler :
  renaming ->
  positive list ->
  continuation_handler ->
  positive list * continuation_handler

val apart_binding :
  renaming -> positive list -> static_binding -> positive list * static_binding

val apart_code : renaming -> positive list -> code -> positive list * code

val renamed_apart : expr -> expr

val rename_apart : expr -> expr
