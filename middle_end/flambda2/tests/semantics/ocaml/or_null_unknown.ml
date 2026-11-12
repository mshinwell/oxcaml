(* A match on a value that may be null and that Simplify does not know: the test
   stays. *)

external opaque : int or_null -> int or_null = "%opaque"

let[@inline] or_zero (x : int or_null) = match x with Null -> 0 | This n -> n

let result = or_zero (opaque (This 3))
