(* The length of a string that is a constant of the module, read by an exported
   function. *)

external length : string -> int = "%string_length"

let greeting = "hello"

let size () = length greeting
