(* A loop that reads a number from the digits of a string. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external length : string -> int = "%string_length"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

external code : char -> int = "%identity"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

let rec parse s i acc =
  if i < length s
  then parse s (i + 1) ((acc * 10) + (code (unsafe_get s i) - code '0'))
  else acc

let result = parse (opaque "40213") 0 0
