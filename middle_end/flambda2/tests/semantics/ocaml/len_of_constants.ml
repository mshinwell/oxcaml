(* The lengths of constant strings of 0, 1, 7, 8, 9 and 16 characters, and of
   one with an escape. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

let result =
  length "" + length "a" + length "seven.." + length "eight..."
  + length "nine....." + length "sixteen........." + length "tab\there"
