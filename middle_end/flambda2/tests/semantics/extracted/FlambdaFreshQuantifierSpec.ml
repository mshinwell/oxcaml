open BinNums
open BinPos
open Datatypes
open FlambdaNameAbstractionSpec

(** val names_from : nat -> positive -> positive list **)

let rec names_from count first =
  match count with
  | O -> []
  | S count0 -> first :: names_from count0 (Pos.succ first)

(** val fresh_names : nat -> positive list -> positive list **)

let fresh_names count avoid = names_from count (fresh_name avoid)
