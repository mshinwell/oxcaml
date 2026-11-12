(* A boxed result that is a constant whatever the number that is not known: the
   product by zero. Simplify gives it the symbol of the literal zero of the
   source, and binds no other. *)

external mul : int64 -> int64 -> int64 = "%int64_mul"

external opaque : 'a -> 'a = "%opaque"

let x_times_zero = mul (opaque 5L) 0L
