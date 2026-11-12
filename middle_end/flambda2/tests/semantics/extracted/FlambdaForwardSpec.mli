open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaParamAliasesSpec
open List
open ListDef
open PeanoNat

val binds_cont : continuation -> expr -> bool

val binds_cont_in_handler : continuation -> continuation_handler -> bool

val subst_simple : variable list -> simple list -> simple -> simple

val forwarded : variable list -> simple list -> apply_cont -> apply_cont

type forwards = (continuation * (variable list * apply_cont) option) list

val forward_of : forwards -> continuation -> (variable list * apply_cont) option

val forward_apply_cont : forwards -> apply_cont -> apply_cont

val forward_arm : forwards -> apply_cont -> apply_cont

val passes_on : variable list -> simple list -> bool

val alias_of : forwards -> continuation -> continuation option

val forward_apply : forwards -> apply_expr -> apply_expr

val forwarding :
  continuation ->
  variable list ->
  handler_metadata ->
  expr ->
  expr ->
  (variable list * apply_cont) option

val given_one_inner_variable : continuation -> variable list -> expr -> bool

val forward_entry :
  continuation ->
  variable list ->
  handler_metadata ->
  expr ->
  expr ->
  (variable list * apply_cont) option

val forward_applications_under : forwards -> expr -> expr

val forward_applications_in_handler :
  forwards -> continuation_handler -> continuation_handler

val forward_applications : expr -> expr
