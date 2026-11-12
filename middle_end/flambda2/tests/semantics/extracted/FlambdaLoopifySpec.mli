open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaUnusedContsSpec
open List
open ListDef

val is_self_tail_call :
  variable -> continuation -> continuation -> apply_expr -> bool

val loop_calls :
  variable -> continuation -> continuation -> continuation -> expr -> expr

val loop_calls_in_handler :
  variable ->
  continuation ->
  continuation ->
  continuation ->
  continuation_handler ->
  continuation_handler

val loop_safe :
  variable -> continuation -> continuation -> continuation -> expr -> bool

val loop_safe_handler :
  variable ->
  continuation ->
  continuation ->
  continuation ->
  continuation_handler ->
  bool

val loop_handler : continuation -> code -> continuation_handler

val looped_code : continuation -> code -> code

val loopable : continuation -> code -> bool

val loopify_code : continuation -> code -> code

type loopified = (code_id * continuation) list

val loopify_binding : loopified -> static_binding -> static_binding

val loopify_unit : loopified -> expr -> expr
