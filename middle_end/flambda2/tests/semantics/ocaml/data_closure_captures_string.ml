(* A closure over a string that is not known, and one over a constant string,
   each reading a character of it. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

let reader s = fun i -> code (unsafe_get s i)

let from_constant = reader "hello"

let from_unknown = reader (opaque "world")

let result = from_constant 1 + from_unknown (opaque 0)
