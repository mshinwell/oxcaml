open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedContsSpec

val sink_to_use : continuation -> continuation_handler -> expr -> expr option

val sink_conts_to_uses : expr -> expr
