(* The same, where one arm of the match returns an argument of the function. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type shape =
  | Dot
  | Box of int * int

let[@inline never] measure known side =
  let shape = if 0 < side then Box (side, side + 1) else known in
  match shape with Dot -> side | Box (w, h) -> w + h

let result =
  measure (opaque Dot) (opaque 3)
  + measure (opaque (Box (4, 5))) (opaque 0)
  + measure (opaque Dot) (opaque (-2))
