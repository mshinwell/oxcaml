open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List
open ListDef

type merge_by =
  | By_tagging
  | By_tagging_and_negating

val constant_of_arm : merge_by -> coq_Z -> const option

val merged_arguments : variable -> simple list -> simple list -> simple list

val constant_for : variable -> const -> simple -> simple

val arm_is_merged :
  merge_by -> variable -> apply_cont -> coq_Z * apply_cont -> bool

val bind_tagged : variable -> expr -> expr

val bind_negated : variable -> expr -> expr

val merge_switch : simple -> (coq_Z * apply_cont) list -> expr

val merge_switches : expr -> expr
