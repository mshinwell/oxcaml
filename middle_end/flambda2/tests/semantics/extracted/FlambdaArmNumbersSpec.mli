open BinNums
open BinPos
open Datatypes
open FlambdaGiveScrutineeSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaUntagParamsSpec
open List
open ListDef
open OxCamlList

val number_simple : variable -> coq_Z -> simple -> simple

val number_in_apply_cont : variable -> coq_Z option -> apply_cont -> apply_cont

val source_under_let :
  variable -> variable -> named -> variable option -> variable option

val source_under :
  variable -> variable list -> variable option -> variable option

val number_read : variable -> variable option -> coq_Z -> simple -> simple

val number_in_named :
  variable -> variable option -> coq_Z option -> named -> named

val number_in_scrutinee :
  variable -> variable option -> coq_Z option -> simple -> simple

val number_in_region :
  variable -> variable option -> coq_Z option -> expr -> expr

val number_in_handler :
  variable ->
  variable option ->
  coq_Z option ->
  continuation_handler ->
  continuation_handler

val number_in_arms : variable -> coq_Z option -> expr -> expr

val scrutinees : expr -> variable list

val handler_scrutinees : continuation_handler -> variable list

val numbers_in_arms : expr -> expr
