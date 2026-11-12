(* A character of a string at an unknown index, read in one branch of a test:
   the index is converted for the bounds test and again for the load. *)

external get : string -> int -> char = "%string_safe_get"

external code : char -> int = "%identity"

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let result =
  let s = opaque "hello" in
  let i = opaque 3 in
  if opaque true then code (get s i) + 1 else 0
