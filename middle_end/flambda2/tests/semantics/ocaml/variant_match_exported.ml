(* An exported function that matches on a variant with constant and non-constant
   constructors. *)

type t =
  | A
  | B
  | C of int

let f x = match x with A -> 10 | B -> 20 | C n -> n
