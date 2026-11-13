open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUntagParamsSpec
open List
open ListDef

val shadow_lets :
  nat list -> nat -> variable list -> flambda_kind list -> expr -> expr

val shadow_expr : positions -> expr -> expr

val shadow_handler :
  positions -> nat list -> continuation_handler -> continuation_handler

val handlers_of : expr -> (continuation * continuation_handler) list

val handlers_in_handler :
  continuation_handler -> (continuation * continuation_handler) list

val untagged_in : variable -> expr -> bool

val untagged_in_handler : variable -> continuation_handler -> bool

val gives_needed : positions -> variable -> apply_cont -> bool

val given_needed : positions -> variable -> expr -> bool

val given_needed_in_handler :
  positions -> variable -> continuation_handler -> bool

val needed_from :
  positions -> nat -> variable list -> flambda_kind list -> expr -> nat list

val needed_of : positions -> continuation_handler -> nat list

val needed_round :
  (continuation * continuation_handler) list -> positions -> positions

val needed_positions :
  nat -> (continuation * continuation_handler) list -> positions -> positions

val shadow_positions : expr -> positions

val shadow_params : expr -> expr
