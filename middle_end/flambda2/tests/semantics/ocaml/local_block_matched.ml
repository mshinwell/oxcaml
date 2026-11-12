(* A function that builds a block on one way of a test and matches on what the
   test leaves: the block does not leave the function, which has a region for
   it. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type shape =
  | Dot
  | Box of int * int

let[@inline never] measure known side =
  let shape = if 0 < side then Box (side, side + 1) else known in
  match shape with Dot -> 0 | Box (w, h) -> w + h

let result =
  measure (opaque Dot) (opaque 3)
  + measure (opaque (Box (4, 5))) (opaque 0)
  + measure (opaque Dot) (opaque 0)
