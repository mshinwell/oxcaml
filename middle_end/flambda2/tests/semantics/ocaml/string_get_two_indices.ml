(* Two reads of one string at two unknown indices after a test of a third
   value. *)

external get : string -> int -> char = "%string_safe_get"

external code : char -> int = "%identity"

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let result =
  let s = opaque "hello" in
  let i = opaque 1 in
  let j = opaque 2 in
  if opaque false then 0 else code (get s i) + code (get s j)
