open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedParamsSpec
open List
open ListDef
open PeanoNat

val simple_eqb : simple -> simple -> bool

val binds_var : variable -> expr -> bool

val binds_var_in_handler : variable -> continuation_handler -> bool

val stable : simple -> expr -> bool

val args_if_applies : continuation -> apply_cont -> simple list option

val first_some : 'a1 option -> 'a1 option -> 'a1 option

val some_args : continuation -> expr -> simple list option

val some_args_in_handler :
  continuation -> continuation_handler -> simple list option

val given : continuation -> nat -> (simple -> bool) -> apply_cont -> bool

val always_given : continuation -> nat -> (simple -> bool) -> expr -> bool

val always_given_in_handler :
  continuation -> nat -> (simple -> bool) -> continuation_handler -> bool

val aliases_from :
  nat ->
  variable list ->
  (nat -> variable -> simple option) ->
  simple option list

val aliases_of :
  continuation ->
  variable list ->
  handler_metadata ->
  expr option ->
  expr ->
  expr ->
  simple option list

val bind_aliases :
  variable list -> flambda_kind list -> simple option list -> expr -> expr

val alone : 'a1 list -> bool

val bind_aliased_params : expr -> expr

val bind_aliased_params_in_loop :
  bool ->
  continuation ->
  expr ->
  expr ->
  continuation_handler ->
  continuation_handler
