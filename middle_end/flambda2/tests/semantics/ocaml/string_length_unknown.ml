(* The length of a string that Simplify does not know. *)

external length : string -> int = "%string_length"

external opaque : 'a -> 'a = "%opaque"

let result = length (opaque "hello")
