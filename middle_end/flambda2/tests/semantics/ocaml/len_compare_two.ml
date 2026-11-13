(* The lengths of two strings compared. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

let shorter a b = if length a < length b then a else b

let result =
  length (shorter (opaque "abc") "ab") + length (shorter "x" (opaque "yz"))
