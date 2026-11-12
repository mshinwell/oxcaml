(* A match on a value that is not known, at the top of the unit. As in
   [if_unknown.ml], what stops the validator is a continuation used once, in the
   handler of another. *)

external opaque : 'a -> 'a = "%opaque"

type shape =
  | Point
  | Square of int
  | Rect of int * int

let result =
  match opaque (Square 3) with Point -> 0 | Square n -> n | Rect (w, _) -> w
