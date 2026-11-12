(* A character of a string that is a constant of the unit, with no bounds
   check. *)

external unsafe_get : string -> int -> char = "%string_unsafe_get"

let result = unsafe_get "hello" 1
