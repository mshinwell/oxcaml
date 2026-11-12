open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedContsSpec
open List

val applied_at_tail : continuation -> continuation_handler -> expr -> bool

val params_not_free : variable list -> continuation_handler -> bool

val sink_into_handler :
  continuation -> continuation_handler -> expr -> expr option

val sink_let_conts : expr -> expr
