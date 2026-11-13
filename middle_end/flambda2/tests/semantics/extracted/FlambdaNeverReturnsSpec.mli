open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedContsSpec
open ListDef
open PeanoNat

val never_returns_b : apply_expr -> code -> bool

val invalid_params : code -> nat -> variable list option

val cut_return : (code_id * code) list -> apply_expr -> expr

val returns_to_invalid : continuation -> continuation_handler -> expr -> bool

val cut_returns : (code_id * code) list -> expr -> expr

val cut_returns_in_handler :
  (code_id * code) list -> continuation_handler -> continuation_handler

val cut_returns_in_binding :
  (code_id * code) list -> static_binding -> static_binding

val cut_returns_in_code : (code_id * code) list -> code -> code
