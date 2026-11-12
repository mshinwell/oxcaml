open Datatypes
open FlambdaForwardSpec
open FlambdaModel
open ListDef

val jump_entry :
  continuation ->
  variable list ->
  handler_metadata ->
  expr ->
  expr ->
  (variable list * apply_cont) option

val forward_jumps_under : forwards -> expr -> expr

val forward_jumps_in_handler :
  forwards -> continuation_handler -> continuation_handler

val forward_jumps : expr -> expr
