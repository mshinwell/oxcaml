open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaValueSpec
open List

type known_closures = (symbol * static_const) list

val static_closure_made : static_binding -> (symbol * static_const) list

val closures_under_statics :
  known_closures -> static_binding list -> known_closures

val forget_slot_var : variable -> known_closures -> known_closures

val forget_slot_vars : variable list -> known_closures -> known_closures

val static_closure_slots :
  static_const -> (function_slot * (value_slot * simple) list) option

val slot_read :
  known_closures ->
  function_slot option ->
  value_slot ->
  simple ->
  simple option

val read_slot_named : known_closures -> named -> named

val static_closure_code : static_const -> code_id option

val callee_code : known_closures -> simple -> code_id option

val call_known_closure : known_closures -> apply_expr -> apply_expr

val use_closures_knowing : known_closures -> expr -> expr

val use_closures_in_handler :
  known_closures -> continuation_handler -> continuation_handler

val use_known_closures : expr -> expr
