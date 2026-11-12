(* The sum of the bytes of a string, by a loop over its indices. *)

external length : string -> int = "%string_length"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let rec sum s i acc =
  if i < length s then sum s (i + 1) (acc + code (unsafe_get s i)) else acc

let result = sum (opaque "hello") 0 0
