open BinPos
open Datatypes
open FlambdaCompareSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaUnusedContsSpec
open List
open ListDef

val may_be_static : named -> bool

val straight : nat -> expr -> bool

val sharable : continuation_handler -> bool

val handler_params : continuation_handler -> variable list

val same_handler :
  continuation_handler ->
  variable list ->
  continuation list ->
  continuation_handler ->
  bool

val share_with :
  continuation ->
  continuation_handler ->
  variable list ->
  continuation list ->
  expr ->
  expr

val share_handlers : expr -> expr
