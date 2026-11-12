(* A match on an integer whose cases are runs of consecutive constants, with
   gaps between the runs and a default. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] band n =
  match n with
  | 0 | 1 | 2 -> 10
  | 3 | 4 | 5 | 6 -> 20
  | 10 | 11 -> 30
  | 20 | 21 | 22 | 23 | 24 -> 40
  | _ -> 0

let result =
  band (opaque 1)
  + band (opaque 6)
  + band (opaque 11)
  + band (opaque 22)
  + band (opaque 8)
  + band (opaque 99)
