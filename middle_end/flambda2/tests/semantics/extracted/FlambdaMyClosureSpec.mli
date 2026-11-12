open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

val bind_my_closures : (code_id * symbol) list -> expr -> expr

val bind_my_closures_in_handler :
  (code_id * symbol) list -> continuation_handler -> continuation_handler

val bind_my_closures_in_binding :
  (code_id * symbol) list -> static_binding -> static_binding

val bind_my_closure : (code_id * symbol) list -> code_id -> code -> code

val named_makes_no_closure_of : code_id -> named -> bool

val static_closure_of_is : code_id -> symbol -> symbol -> static_const -> bool

val only_closure_of : code_id -> symbol -> expr -> bool

val handler_only_closure_of : code_id -> symbol -> continuation_handler -> bool

val binding_only_closure_of : code_id -> symbol -> static_binding -> bool

val code_only_closure_of : code_id -> symbol -> code -> bool

val only_closures_of : (code_id * symbol) list -> expr -> bool
