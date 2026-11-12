(* A pair of a pair and an integer, taken apart by the pattern of a
   parameter. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] sum ((a, b), c) = a + b + c

let result = sum ((1, opaque 2), 3)
