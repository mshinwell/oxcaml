open BinPos
open Datatypes
open FlambdaModel
open List

val cont_free_b : continuation -> expr -> bool

val cont_free_in_handler_b : continuation -> continuation_handler -> bool

val remove_unused_conts : expr -> expr

val remove_unused_conts_in_handler :
  continuation_handler -> continuation_handler
