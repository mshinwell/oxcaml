(* The length of a string read in each branch of a test, for the bounds check,
   and again after the two branches meet. *)

external get : string -> int -> char = "%string_safe_get"

external length : string -> int = "%string_length"

external code : char -> int = "%identity"

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let result =
  let s = opaque "hello" in
  let i = opaque 1 in
  let j = opaque 2 in
  let c = if opaque true then get s i else get s j in
  code c + length s
