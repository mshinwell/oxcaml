(* A function that returns a pair, which the caller takes apart at once:
   Simplify inlines it and the pair is not built. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] next_and_double x = x + 1, x * 2

let result =
  let next, double = next_and_double (opaque 3) in
  next + double
