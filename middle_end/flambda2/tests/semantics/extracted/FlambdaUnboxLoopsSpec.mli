open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaUnboxParamsSpec
open FlambdaUnboxVariantsSpec
open List
open ListDef

val on_spine : variable -> expr -> bool

val unbox_loop_read :
  facts ->
  continuation ->
  variable list ->
  handler_metadata ->
  expr ->
  expr ->
  read ->
  (((variable list * handler_metadata) * expr) * expr) option

type loop_state = ((variable list * handler_metadata) * expr) * expr

val loop_of : continuation -> loop_state -> expr

val unbox_loop_param :
  nat -> facts -> continuation -> nat -> loop_state -> loop_state

val unbox_loop_params :
  nat -> facts -> continuation -> nat list -> loop_state -> loop_state

val unbox_loop_reads :
  facts ->
  continuation ->
  variable list ->
  handler_metadata ->
  expr ->
  expr ->
  expr

val unbox_loops_knowing : facts -> expr -> expr
