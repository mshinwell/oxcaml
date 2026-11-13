open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnaliasParamsSpec
open List
open ListDef
open Nat

val trap_free_of : continuation -> apply_cont -> bool

val only_applied_or_returned_to : continuation -> expr -> bool

val handler_only_applied_or_returned_to :
  continuation -> continuation_handler -> bool

val one_if_same : continuation -> continuation -> nat

val uses_of : continuation -> expr -> nat

val uses_in_handler : continuation -> continuation_handler -> nat

val wrapper :
  continuation ->
  nat ->
  variable list ->
  handler_metadata ->
  continuation_handler

val wrap_uses : continuation -> nat -> continuation_handler -> expr -> expr

val wrap_uses_in_handler :
  continuation ->
  nat ->
  continuation_handler ->
  continuation_handler ->
  continuation_handler

val wrap_return :
  nat ->
  continuation ->
  continuation_handler ->
  expr ->
  (continuation_handler * expr) option

val wrap_from :
  nat ->
  continuation ->
  continuation_handler ->
  expr ->
  continuation_handler * expr

val wrap_returns : expr -> expr
