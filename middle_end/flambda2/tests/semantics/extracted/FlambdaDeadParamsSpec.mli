open BinPos
open Bool
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnusedParamsSpec
open List
open ListDef
open Nat

val bools_eqb : bool list -> bool list -> bool

val mask_eqb : bool list option -> bool list option -> bool

val masks_eqb : masks -> masks -> bool

val settle : nat -> (masks -> masks) -> masks -> masks option

val count_params : (continuation * continuation_handler) list -> nat

val drop_dead : masks -> expr -> expr

val live_params : masks -> bool -> continuation_handler -> bool list option

val drop_dead_in_loop :
  masks -> bool -> continuation_handler -> continuation_handler

val drop_dead_params : expr -> expr
