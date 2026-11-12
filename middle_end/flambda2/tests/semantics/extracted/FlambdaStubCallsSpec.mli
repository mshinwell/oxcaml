open Datatypes
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

val binding_non_stub_code : static_binding -> code_id list

val non_stub_code : expr -> code_id list

val handler_non_stub_code : continuation_handler -> code_id list

val demote_call : code_id list -> apply_expr -> apply_expr

val demote_calls : code_id list -> expr -> expr

val demote_calls_in_handler :
  code_id list -> continuation_handler -> continuation_handler

val demote_calls_in_code : code_id list -> code -> code

val demote_in_stub_binding : code_id list -> static_binding -> static_binding

val demote_in_stubs : code_id list -> expr -> expr

val demote_in_stubs_of_handler :
  code_id list -> continuation_handler -> continuation_handler

val demote_stub_calls : expr -> expr
