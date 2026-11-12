(* The negation of a boolean that Simplify does not know. *)

external not : bool -> bool = "%boolnot"

external opaque : 'a -> 'a = "%opaque"

let result = not (opaque true)
