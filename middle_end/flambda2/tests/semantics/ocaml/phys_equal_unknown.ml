(* Physical equality of a number that Simplify does not know with a constant. *)

external ( == ) : 'a -> 'a -> bool = "%eq"

external opaque : 'a -> 'a = "%opaque"

let result = opaque 3 == 3
