open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaPrimitiveModel
open FlambdaUntagParamsSpec
open List
open ListDef
open Nat

val alias_of : named -> variable option

type twinned = (variable * variable) list

val twin_simple : twinned -> simple -> simple

val twin_args : nat list -> twinned -> simple list -> simple list

val twin_apply_cont : positions -> twinned -> apply_cont -> apply_cont

val twin_named : twinned -> named -> named

val twin_names : variable list -> expr -> variable list

val renamed_from :
  nat list -> nat -> variable list -> variable list -> variable list

val twin_params_list : nat list -> variable list -> expr -> variable list

val twin_metadata : nat list -> handler_metadata -> handler_metadata

val twin_expr :
  positions -> positions -> twinned -> variable list -> expr -> expr

val twin_handler :
  positions ->
  positions ->
  twinned ->
  nat list ->
  continuation_handler ->
  continuation_handler

val head_ok : variable list -> variable list -> expr -> bool

val handler_twins_fit : nat list -> variable list -> expr -> bool

val twin_ok : positions -> positions -> expr -> bool

val twin_handler_ok :
  positions -> positions -> nat list -> continuation_handler -> bool

val twin_sites : positions -> expr -> positions

val handler_twin_sites :
  positions -> continuation -> continuation_handler -> positions

val twin_untag_at : positions -> expr -> expr

val after_alias : variable -> expr -> expr option

val head_positions :
  nat -> variable list -> flambda_kind list -> expr -> nat list

val twin_candidates : expr -> positions

val handler_twin_candidates : continuation -> continuation_handler -> positions

val twin_blame : positions -> positions -> expr -> (continuation * nat) list

val twin_handler_blame :
  positions ->
  positions ->
  continuation ->
  continuation_handler ->
  (continuation * nat) list

val twin_origin :
  positions -> positions -> continuation * nat -> (continuation * nat) list

val twin_settle : nat -> positions -> expr -> positions

val twin_positions : expr -> positions

val twin_params : expr -> expr
