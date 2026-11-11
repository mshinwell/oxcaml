open BinNums
open BinPos
open Datatypes
open FlambdaModel
open ListDef

type permutation = (positive * positive) list

val swap : positive -> positive -> positive -> positive

val permute : permutation -> positive -> positive

type renaming =
  { variable_permutation : permutation;
    continuation_permutation : permutation
  }

val rename_variable : renaming -> variable -> variable

val rename_continuation : renaming -> continuation -> continuation

val rename_simple : renaming -> simple -> simple

val rename_named : renaming -> named -> named

val rename_apply_cont : renaming -> apply_cont -> apply_cont

val rename_static_const : renaming -> static_const -> static_const

val rename_apply : renaming -> apply_expr -> apply_expr

val rename_expr : renaming -> expr -> expr

val rename_handler : renaming -> continuation_handler -> continuation_handler

val rename_static_binding : renaming -> static_binding -> static_binding

val rename_code : renaming -> code -> code
