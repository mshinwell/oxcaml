open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open List
open ListDef

val keep : bool list -> 'a1 list -> 'a1 list

val keep_all_or : bool list option -> 'a1 list -> 'a1 list

type masks = (continuation * bool list option) list

val mask_of : masks -> continuation -> bool list option

val drop_args : masks -> apply_cont -> apply_cont

val returned_to : continuation -> expr -> bool

val returned_to_in_handler : continuation -> continuation_handler -> bool

val used_params : bool -> variable list -> expr -> bool list option

val keep_kinds : bool list option -> handler_metadata -> handler_metadata

val drop_params : masks -> expr -> expr

val drop_params_in_handler :
  masks -> continuation_handler -> continuation_handler

val drop_unused_params : expr -> expr
