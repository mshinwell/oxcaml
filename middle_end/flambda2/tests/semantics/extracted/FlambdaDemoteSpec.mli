open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaWellFormedSpec
open List
open ListDef

val called_with_exn : continuation -> expr -> bool

val handler_called_with_exn : continuation -> continuation_handler -> bool

val binds_continuation : continuation -> expr -> bool

val handler_binds_continuation : continuation -> continuation_handler -> bool

val demotable :
  continuation list -> continuation -> continuation_handler -> expr -> bool

val strip_trap : continuation -> apply_cont -> apply_cont

val strip_traps : continuation -> expr -> expr

val strip_traps_handler :
  continuation -> continuation_handler -> continuation_handler

val clear_exn_handler : continuation_handler -> continuation_handler

val demote_handlers : continuation list -> expr -> expr

val demote_handlers_handler :
  continuation list -> continuation_handler -> continuation_handler

val demote_handlers_binding : static_binding -> static_binding

val demote_handlers_code : code -> code
