open BinNums
open Datatypes
open FlambdaNameAbstractionSpec

(** val fresh_names : nat -> positive list -> positive list **)

let rec fresh_names count avoid =
  match count with
  | O -> []
  | S count0 ->
    let name = fresh_name avoid in
    name :: fresh_names count0 (name :: avoid)
