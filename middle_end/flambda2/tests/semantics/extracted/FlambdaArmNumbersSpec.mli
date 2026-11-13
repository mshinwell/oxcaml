open BinNums
open BinPos
open Datatypes
open FlambdaGiveScrutineeSpec
open FlambdaModel
open List
open ListDef
open OxCamlList

val number_simple : variable -> coq_Z -> simple -> simple

val number_in_apply_cont : variable -> coq_Z option -> apply_cont -> apply_cont

val number_in_arms : variable -> coq_Z option -> expr -> expr

val number_in_handler :
  variable -> coq_Z option -> continuation_handler -> continuation_handler

val scrutinees : expr -> variable list

val handler_scrutinees : continuation_handler -> variable list

val numbers_in_arms : expr -> expr
