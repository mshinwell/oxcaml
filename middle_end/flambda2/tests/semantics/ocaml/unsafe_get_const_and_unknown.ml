(* The read with no check, of a constant string at a constant index, at an index
   that is not known, and of a string that is not known. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

let result =
  code (unsafe_get "hello" 1)
  + code (unsafe_get "hello" (opaque 4))
  + code (unsafe_get (opaque "world") 0)
