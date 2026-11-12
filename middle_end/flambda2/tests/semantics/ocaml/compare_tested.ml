(* The result of [compare] on two integers tested against zero, with [<]:
   Simplify makes the test a comparison of the two integers, and the three-way
   comparison is gone. *)

external compare : int -> int -> int = "%compare"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let result = if compare (opaque 3) 4 < 0 then 10 else 20
