(* A match on a value that may be null and is known once the function is
   inlined. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline] or_zero (x : int or_null) = match x with Null -> 0 | This n -> n

let result = or_zero (This 3) + or_zero Null
