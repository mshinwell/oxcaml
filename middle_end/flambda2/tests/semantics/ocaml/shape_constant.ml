(* A variant that one path gives as a constant block, [Box 8], which is a symbol
   of the unit, and the other as a constant constructor, matched after they
   meet, in the unit itself. Simplify gives the continuation where they meet
   whether the value is an immediate and the field: 8 on the path of the symbol
   and [poison] on the other. *)

external opaque : 'a -> 'a = "%opaque"

type shape =
  | Empty
  | Full
  | Box of int

let result =
  let v = if opaque true then Box 8 else Empty in
  match v with Empty -> 1 | Full -> 2 | Box y -> y
