(* A match on an integer with the eight constants from 0 to 7 and a default:
   dense, so the front end can make one Switch after a test of the range. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] weight n =
  match n with
  | 0 -> 5
  | 1 -> 3
  | 2 -> 8
  | 3 -> 1
  | 4 -> 9
  | 5 -> 2
  | 6 -> 7
  | 7 -> 4
  | _ -> 0

let result =
  weight (opaque 2)
  + weight (opaque 6)
  + weight (opaque 7)
  + weight (opaque 9)
  + weight (opaque (-1))
