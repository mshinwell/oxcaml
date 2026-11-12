(* [compare] at two boxed 64-bit integers, its result tested against zero:
   Simplify makes the test a comparison of the two unboxed numbers. *)

external compare : int64 -> int64 -> int = "%compare"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let result = if compare (opaque 3L) 4L < 0 then 10 else 20
