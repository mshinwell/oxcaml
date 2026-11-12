(* A value of a variant type made when the module runs, and an exported function
   that tests it. *)

external opaque : 'a -> 'a = "%opaque"

type t =
  | A
  | B of int

let b = B (opaque 1)

let is_a x = match x with A -> true | B _ -> false

let result = is_a b
