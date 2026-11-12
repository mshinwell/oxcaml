(* A character of a string at an index that is not known and out of bounds: the
   bounds check raises, and a handler catches. *)

external get : string -> int -> char = "%string_safe_get"

external code : char -> int = "%identity"

external opaque : 'a -> 'a = "%opaque"

let result = try code (get (opaque "hello") (opaque 7)) with _ -> -1
