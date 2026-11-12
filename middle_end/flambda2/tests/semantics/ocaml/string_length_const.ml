(* The length of a string that is a constant of the unit. *)

external length : string -> int = "%string_length"

let result = length "hello"
