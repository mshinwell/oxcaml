(* A character of a constant string, with the bounds check. *)

external get : string -> int -> char = "%string_safe_get"

let result = get "hello" 1
