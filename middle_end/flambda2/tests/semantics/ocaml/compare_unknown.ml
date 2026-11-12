(* A comparison of a number that Simplify does not know with a constant: the
   result is the boolean, with no branch. *)

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let result = opaque 3 < 4
