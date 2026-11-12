open BinNums
open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open ListDef

val shortcut_arm :
  continuation -> apply_cont -> coq_Z * apply_cont -> coq_Z * apply_cont

val shortcut_switch : continuation -> continuation_handler -> expr -> expr

val shortcut_switches : expr -> expr
